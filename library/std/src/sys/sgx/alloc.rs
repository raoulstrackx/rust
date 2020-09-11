use crate::alloc::{GlobalAlloc, Layout, System};
use crate::mem;
use crate::ptr;
use crate::marker::PhantomData;

use super::waitqueue::SpinMutex;

// Using a SpinMutex because we never want to exit the enclave waiting for the
// allocator.
#[cfg_attr(test, linkage = "available_externally")]
#[export_name = "_ZN16__rust_internals3std3sys3sgx5alloc8DLMALLOCE"]
static DLMALLOC: SpinMutex<dlmalloc::Dlmalloc> = SpinMutex::new(dlmalloc::DLMALLOC_INIT);

#[stable(feature = "alloc_system_type", since = "1.28.0")]
unsafe impl GlobalAlloc for System {
    #[inline]
    unsafe fn alloc(&self, layout: Layout) -> *mut u8 {
        DLMALLOC.lock().malloc(layout.size(), layout.align())
    }

    #[inline]
    unsafe fn alloc_zeroed(&self, layout: Layout) -> *mut u8 {
        DLMALLOC.lock().calloc(layout.size(), layout.align())
    }

    #[inline]
    unsafe fn dealloc(&self, ptr: *mut u8, layout: Layout) {
        DLMALLOC.lock().free(ptr, layout.size(), layout.align())
    }

    #[inline]
    unsafe fn realloc(&self, ptr: *mut u8, layout: Layout, new_size: usize) -> *mut u8 {
        DLMALLOC.lock().realloc(ptr, layout.size(), layout.align(), new_size)
    }
}

// The following functions are needed by libunwind. These symbols are named
// in pre-link args for the target specification, so keep that in sync.
#[cfg(not(test))]
#[no_mangle]
pub unsafe extern "C" fn __rust_c_alloc(size: usize, align: usize) -> *mut u8 {
    crate::alloc::alloc(Layout::from_size_align_unchecked(size, align))
}

#[cfg(not(test))]
#[no_mangle]
pub unsafe extern "C" fn __rust_c_dealloc(ptr: *mut u8, size: usize, align: usize) {
    crate::alloc::dealloc(ptr, Layout::from_size_align_unchecked(size, align))
}

#[derive(Debug, PartialEq, Eq)]
pub enum Error {
    AlignmentError,
    DoubleFree,
    MemoryNotManagedByAllocator,
    MemorySizeNotPowerOfTwo,
    MinBlockSizeLargerThanMemory,
    MinBlockSizeTooSmall,
}

pub trait MemoryMapper {
    fn map_region(base: *const u8, size: usize);

    fn unmap_region(base: *const u8, size: usize);

    fn min_map_size() -> usize {
        0x1000
    }
}

struct SGXv2;

impl MemoryMapper for SGXv2 {
    fn map_region(base: *const u8, size: usize) {
        assert_eq!(size % Self::min_map_size(), 0);
        println!("map region: {:?} - {}", base, size);
    }

    fn unmap_region(base: *const u8, size: usize) {
        assert_eq!(size % Self::min_map_size(), 0);
        println!("unmap region: {:?} - {}", base, size);
    }
}

/// A small, simple allocator that can only allocate blocks of a pre-determined, specific size.
#[derive(Debug, PartialEq, Eq)]
pub struct SimpleAllocator<T, M : MemoryMapper> {
    memory_base: *mut u8,
    memory_size: usize,
    free_blocks: *mut u8,
    next_uninit_block: *mut u8,
    phantom: PhantomData<(T, M)>,
}

impl<T, M : MemoryMapper> SimpleAllocator<T, M> {
    pub fn block_size() -> usize {
        mem::size_of::<T>()
            .max(mem::size_of::<*mut u8>())
            .next_power_of_two()
    }

    fn memory_end(&self) -> *const u8 {
        (self.memory_base as usize + self.memory_size) as _
    }

    pub fn new(memory_base: *mut u8, memory_size: usize) -> Result<SimpleAllocator<T, M>, Error> {
        if (memory_base as usize) % M::min_map_size() != 0 ||
           (memory_base as usize) % Self::block_size() != 0 ||
           M::min_map_size() % Self::block_size() != 0 {
            return Err(Error::AlignmentError);
        }
        Ok(SimpleAllocator {
            memory_base,
            memory_size,
            next_uninit_block: memory_base,
            free_blocks: ptr::null_mut(),
            phantom: PhantomData,
        })
    }

    pub fn alloc(&mut self) -> Option<*mut T> {
        unsafe {
            if self.free_blocks.is_null() {
                let ptr = self.next_uninit_block as *mut T;
                if (ptr as *const u8) < self.memory_end() {
                    // There are no free memory blocks, but part of the memory region is still
                    // uninitialized; use a new uninitialized block
                    if (ptr as usize) % M::min_map_size() == 0 {
                        // Request that a new page is mapped in memory
                        M::map_region(ptr as _, M::min_map_size());
                    }
                    self.next_uninit_block = (self.next_uninit_block as usize + Self::block_size()) as *mut u8;
                    assert_eq!((ptr as usize) % Self::block_size(), 0);
                    Some(ptr)
                } else {
                    None
                }
            } else if self.next_uninit_block < (self.memory_base as usize + self.memory_size) as _ {
                // There are free memory blocks available, recycle one
                let new_head: *mut u8 = ptr::read(self.free_blocks as _);
                let ptr = self.free_blocks;
                self.free_blocks = new_head;
                assert_eq!((ptr as usize) % Self::block_size(), 0);
                Some(ptr as _)
            } else {
                // We're out of memory
                None
            }
        }
    }

    pub fn free(&mut self, ptr: *mut T) {
        unsafe {
            ptr::write(ptr as _, self.free_blocks);
            self.free_blocks = ptr as _;
        }
    }
}

#[derive(Debug, PartialEq, Eq)]
pub enum Block {
    Free,
    Allocated,
    Partitioned(*mut Block, *mut Block),
}

#[derive(Debug, PartialEq, Eq)]
pub struct BuddyAllocator<M : MemoryMapper>{
    block: *mut Block,
    min_block_size: usize,
    memory_base: *mut u8,
    memory_size: usize,
    allocator: SimpleAllocator<Block, M>,
}

impl<M : MemoryMapper> BuddyAllocator<M> {
    fn tree_depth(memory_size: usize, min_block_size: usize) -> u32 {
        let max_depth = memory_size.next_power_of_two().trailing_zeros();
        let block_depth = min_block_size.next_power_of_two().trailing_zeros();

        assert!(min_block_size <= memory_size);
        max_depth - block_depth
    }

    fn max_metadata_entries(memory_size: usize, min_block_size: usize) -> u32 {
        let depth = Self::tree_depth(memory_size, min_block_size);
        2u32.pow(depth + 1) - 1
    }

    fn max_metadata_size(memory_size: usize, min_block_size: usize) -> usize {
        (Self::max_metadata_entries(memory_size, min_block_size) as usize) * SimpleAllocator::<Block, M>::block_size()
    }

    pub fn new(memory_base: *mut u8, memory_size: usize, min_block_size: usize) -> Result<BuddyAllocator<M>, Error> {
        if !memory_size.is_power_of_two() {
            return Err(Error::MemorySizeNotPowerOfTwo);
        }
        if !min_block_size.is_power_of_two() {
            return Err(Error::MemorySizeNotPowerOfTwo);
        }
        if min_block_size < M::min_map_size() {
            return Err(Error::MinBlockSizeTooSmall);
        }
        if memory_size < min_block_size {
            return Err(Error::MinBlockSizeLargerThanMemory);
        }
        if memory_size < Self::max_metadata_size(memory_size, min_block_size) {
            return Err(Error::MinBlockSizeTooSmall);
        }
        let allocator = SimpleAllocator::new(memory_base, Self::max_metadata_size(memory_size, min_block_size).next_power_of_two()).expect("compile time checks");
        let buddy = BuddyAllocator::<M> {
            block: ptr::null_mut(),
            min_block_size,
            memory_base,
            memory_size,
            allocator,
        };
        Ok(buddy)
    }

    pub unsafe fn alloc(&mut self, size: usize) -> Option<*mut u8> {
        unsafe fn alloc_helper<M : MemoryMapper>(allocator: &mut SimpleAllocator<Block, M>, block_base: *mut u8, block_size: usize, block: *mut Block, alloc_size: usize, map_memory: bool) -> Option<*mut u8> {
            unsafe fn new_block<M : MemoryMapper>(allocator: &mut SimpleAllocator<Block, M>) -> Option<*mut Block> {
                let b: *mut Block = allocator.alloc()?;
                ptr::write(b, Block::Free);
                Some(b)
            }
            if block_size < alloc_size {
                return None
            }

            match ptr::read(block) {
                Block::Free => {
                    if 2 * alloc_size <= block_size {
                        // Split region
                        let left = new_block(allocator)?;
                        let right = new_block(allocator)?;
                        assert_eq!(ptr::read(left), Block::Free);
                        assert_eq!(ptr::read(right), Block::Free);
                        if let Some(alloc_addr) = alloc_helper(allocator, block_base, block_size / 2, left, alloc_size, map_memory) {
                            *block = Block::Partitioned(left, right);
                            Some(alloc_addr)
                        } else {
                            panic!("Should have allocated memory");
                        }
                    } else {
                        // Use entire region
                        ptr::write(block, Block::Allocated);
                        if map_memory {
                            // Don't map metadata in memory. The SimpleAllocator will take care of
                            // that
                            M::map_region(block_base, block_size);
                        }
                        Some(block_base)
                    }
                },
                Block::Partitioned(left, right) => {
                    if let Some(addr) = alloc_helper(allocator, block_base, block_size / 2, left, alloc_size, map_memory) {
                        // Left partition had space
                        Some(addr)
                    } else if let Some(addr) = alloc_helper(allocator, ((block_base as usize) + block_size / 2) as _, block_size / 2, right, alloc_size, map_memory) {
                        // Right partition had space
                        Some(addr)
                    } else {
                        // No partition had space
                        None
                    }
                },
                Block::Allocated => None,
            }
        }

        if self.block.is_null() {
            // Reserve space for book keeping
            self.block = self.allocator.alloc()?;
            ptr::write(self.block, Block::Free);
            let metadata = alloc_helper(&mut self.allocator,
                                        self.memory_base,
                                        self.memory_size,
                                        self.block,
                                        Self::max_metadata_size(self. memory_size, self.min_block_size),
                                        false);
            assert!(metadata.is_some());
        }
        let size = if size < self.min_block_size { self.min_block_size } else { size };
        let size = size.next_power_of_two();
        alloc_helper(&mut self.allocator, self.memory_base, self.memory_size, self.block, size, true)
    }

    pub unsafe fn free(&mut self, ptr: *mut u8, _size: usize) -> Result<(), Error> {
        unsafe fn free_helper<M : MemoryMapper>(allocator: &mut SimpleAllocator<Block, M>, block_size: usize, block: *mut Block, base: *mut u8, ptr: *mut u8) -> Result<(), Error> {
            match ptr::read(block) {
                Block::Allocated => {
                    ptr::write(block, Block::Free);
                    if M::min_map_size() < block_size {
                        M::unmap_region(base, block_size);
                    }
                    Ok(())
                },
                Block::Partitioned(left, right) => {
                    if ptr as usize - (base as usize) < block_size / 2 {
                        free_helper(allocator, block_size / 2, left, base, ptr)?;
                    } else {
                        free_helper(allocator, block_size / 2, right, (base as usize + block_size / 2) as _, ptr)?;
                    }
                    if ptr::read(left) == Block::Free && 
                        ptr::read(right) == Block::Free {
                        allocator.free(left);
                        allocator.free(right);
                        ptr::write(block, Block::Free);
                        if M::min_map_size() == block_size {
                            // The left and right parts combined are exactly one page. At a lower
                            // level, it couldn't be unmapped as there still may be data on that
                            // page. Now the entire page is free, unmap it. It also isn't possible
                            // that the block size is larger than a page as the buddy allocator
                            // always halfs the available memory. If the block now spans two pages,
                            // it would already have been unmapped on a lower level
                            M::unmap_region(base, block_size);
                        }
                    }
                    Ok(())
                }
                Block::Free => Err(Error::DoubleFree),
            }
        }
        if ptr < self.memory_base || (self.memory_base as usize + self.memory_size) as *mut u8 <= ptr {
            return Err(Error::MemoryNotManagedByAllocator);
        }
        free_helper(&mut self.allocator, self.memory_size, self.block, self.memory_base, ptr)?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::SGXv2;
    use crate::BuddyAllocator;
    use crate::MemoryMapper;
    use crate::SimpleAllocator;
    use std::alloc::GlobalAlloc;
    use std::ptr;

    #[test]
    fn tree_depth() {
        assert_eq!(BuddyAllocator::<SGXv2>::tree_depth(1, 1), 0);
        assert_eq!(BuddyAllocator::<SGXv2>::tree_depth(8, 1), 3);
        assert_eq!(BuddyAllocator::<SGXv2>::tree_depth(16, 1), 4);
        assert_eq!(BuddyAllocator::<SGXv2>::tree_depth(16, 2), 3);
        assert_eq!(BuddyAllocator::<SGXv2>::tree_depth(16, 4), 2);
    }

    #[test]
    fn buddy_alloc2() {
        unsafe {
            let memory_size = 0x10000;
            let memory_base = std::alloc::System.alloc(std::alloc::Layout::from_size_align(memory_size, memory_size).unwrap());
            SGXv2::unmap_region(memory_base, memory_size);
            let mut space = BuddyAllocator::<SGXv2>::new(memory_base, memory_size, 0x1000).unwrap();
            let alloc0 = space.alloc(0x511);
            let alloc1 = space.alloc(0x511);
            assert_eq!(Some((memory_base as usize + 0x1000) as _), alloc0);
            assert_eq!(Some((memory_base as usize + 0x2000) as _), alloc1);
            assert_eq!(Ok(()), space.free(alloc1.unwrap(), 0x511));
            assert_eq!(Ok(()), space.free(alloc0.unwrap(), 0x511));
        }
    }

    #[test]
    pub fn buddy_alloc_bruteforce() {
        fn mark_allocated(base: *mut u8, size: usize) {
            for index in 0..size {
                let ptr = (base as usize + index) as *mut u8;
                unsafe {
                    assert_eq!(*ptr, 0);
                    *ptr = 1;
                }
            }
        }

        fn mark_free(base: *mut u8, size: usize) {
            for index in 0..size {
                let ptr = (base as usize + index) as *mut u8;
                unsafe {
                    assert_eq!(*ptr, 1);
                    *ptr = 0;
                }
            }
        }

        use rand::Rng;

        let memory_size = 0x100000;
        let memory_base = unsafe { std::alloc::System.alloc_zeroed(std::alloc::Layout::from_size_align(memory_size, memory_size).unwrap()) };
        SGXv2::unmap_region(memory_base, memory_size);
        let mut space = BuddyAllocator::<SGXv2>::new(memory_base, memory_size, 0x1000).unwrap();
        let mut rnd = rand::thread_rng();
        let mut pointers: Vec<(*mut u8, usize)> = Vec::new();
    
        for _i in 0..1000 {
            if rnd.gen() {
                // Allocate
                let size = rnd.gen::<usize>() % (memory_size / 10);
                unsafe {
                    if let Some(ptr) = space.alloc(size) {
                        mark_allocated(ptr, size);
                        pointers.push((ptr, size));
                    }
                }
            } else {
                // Free
                if 0 < pointers.len() {
                    let idx = rnd.gen::<usize>() % pointers.len();
                    let (ptr, size) = pointers.remove(idx);
                    mark_free(ptr, size);
                    unsafe { assert_eq!(Ok(()), space.free(ptr, size)) };
                }
            }
        }

        while let Some((ptr, size)) = pointers.pop() {
            mark_free(ptr, size);
            unsafe { assert_eq!(Ok(()), space.free(ptr, size)) };
        }
    }

    #[test]
    fn simple_alloc() {
        unsafe {
            let region = std::alloc::System.alloc(std::alloc::Layout::from_size_align(0x1000, 0x1000).unwrap());
            SGXv2::unmap_region(region, 0x1000);
            let mut allocator = SimpleAllocator::<u32, SGXv2>::new(region, 0x1000).unwrap();
            let mut ptrs = Vec::new();
            for i in 0..100 {
                match allocator.alloc() {
                    Some(ptr) => {
                        assert!((region as *mut u32) <= ptr && ptr < (region as usize + 0x1000) as *mut u32 );
                        ptr::write(ptr, i);
                        ptrs.push(ptr);
                    },
                    None      => panic!("Not enough memory"),
                }
            }
            for ptr in ptrs.iter() {
                allocator.free(*ptr);
            }
        }
    }

    #[test]
    fn bruteforce_simple_alloc() {
        fn mark_allocated(base: *mut u8, size: usize) {
            for index in 0..size {
                let ptr = (base as usize + index) as *mut u8;
                unsafe {
                    *ptr = 1;
                }
            }
        }

        fn mark_free(base: *mut u8, size: usize) {
            for index in 0..size {
                let ptr = (base as usize + index) as *mut u8;
                unsafe {
                    assert_eq!(*ptr, 1);
                    *ptr = 0;
                }
            }
        }

        use std::alloc::GlobalAlloc;
        use rand::Rng;

        let memory_size = 0x1000;
        let region = unsafe { std::alloc::System.alloc_zeroed(std::alloc::Layout::from_size_align(memory_size, memory_size.next_power_of_two()).unwrap()) };

        SGXv2::unmap_region(region, memory_size);
        let mut space = SimpleAllocator::<u32, SGXv2>::new(region, memory_size).unwrap();
        let mut rnd = rand::thread_rng();
        let mut ptrs = Vec::new();
        let num_runs = 10000;
        for i in 0..num_runs {
            let force_free = (9 * num_runs) / 10 < i;
            if rnd.gen::<usize>() % 100 < 70 && !force_free {
                // alloc
                match space.alloc() {
                    Some(ptr) => {
                        ptrs.push(ptr);
                        assert!(ptr < (region as usize + memory_size) as _);
                        assert!(region <= ptr as _);
                        mark_allocated(ptr as _, SimpleAllocator::<u32, SGXv2>::block_size());
                    }
                    None      => (),
                }
            } else {
                // free
                if 0 < ptrs.len() {
                    let idx = rnd.gen::<usize>() % ptrs.len();
                    let ptr = ptrs.remove(idx);
                    mark_free(ptr as _, SimpleAllocator::<u32, SGXv2>::block_size());
                    space.free(ptr);
                }
            }
        }
    }
}
