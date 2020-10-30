#![cfg_attr(test, allow(dead_code))] // why is this necessary?
use fortanix_sgx_abi::tls::{Tls, TlsFlags};
use super::ext::arch;
use crate::ffi::CStr;
use crate::io;
use crate::os::fortanix_sgx::mem::enclave_entry;
use crate::sys::alloc::{self, Sgx};
use crate::sys::sgx::abi::{self, SgxVersion};
use crate::sys::sgx::abi::mem as sgx_mem;
use crate::time::Duration;
use core::alloc::Layout;
use core::convert::TryInto;
use core::mem;
use sgx_isa::{PageType, Secinfo, SecinfoFlags, Tcs};

use super::abi::thread;
use super::abi::usercalls;

pub struct Thread {
    handle: task_queue::JoinHandle,
}

pub const DEFAULT_MIN_STACK_SIZE: usize = 2 * 1024 * 1024;
const DEFAULT_STACK_GUARD_SIZE: isize = 0x10000;

mod tcs_queue {
    use super::super::abi::mem as sgx_mem;
    use super::super::abi::thread;
    use crate::ptr::NonNull;
    use crate::sync::{Mutex, MutexGuard, Once};

    #[derive(Clone, PartialEq, Eq, Debug)]
    pub(super) struct Tcs {
        address: NonNull<u8>,
    }

    impl Tcs {
        fn new(address: NonNull<u8>) -> Tcs {
            Tcs { address }
        }

        pub(super) fn address(&self) -> &NonNull<u8> {
            &self.address
        }
    }

    /// A queue of not running TCS structs
    static mut TCS_QUEUE: Option<Mutex<Vec<Tcs>>> = None;
    static TCS_QUEUE_INIT: Once = Once::new();

    fn init_tcs_queue() -> Vec<Tcs> {
        let mut tcs_queue = Vec::new();

        unsafe {
            for offset in 0.. {
                let tcs_ptr = sgx_mem::tcs_ptr_array().offset(offset);
                if *tcs_ptr == 0 {
                    break;
                } else {
                    let address = *tcs_ptr + sgx_mem::image_base();
                    let address = NonNull::new(address as _).unwrap();

                    if address != thread::current() {
                        tcs_queue.push(Tcs::new(address));
                    }
                }
            }
        }
        tcs_queue
    }

    fn lock() -> MutexGuard<'static, Vec<Tcs>> {
        unsafe {
            TCS_QUEUE_INIT.call_once(|| TCS_QUEUE = Some(Mutex::new(init_tcs_queue())));
            TCS_QUEUE.as_ref().unwrap().lock().unwrap()
        }
    }

    pub(super) fn take_tcs(stack: usize) -> Option<Tcs> {
        let mut tcs_queue = lock();
        if let Some(tcs) = tcs_queue.pop() {
            Some(tcs)
        } else {
            match abi::sgx_version() {
                SgxVersion::SGXv1 => {
                    None
                },
                SgxVersion::SGXv2 => {
                    Some(Thread::create_dynamic_thread(stack));
                }
            }
        }
    }

    pub(super) fn add_tcs(tcs: Tcs) {
        let mut tcs_queue = lock();
        tcs_queue.insert(0, tcs);
    }
}

mod task_queue {
    use super::tcs_queue::{self, Tcs};
    use crate::ptr::NonNull;
    use crate::sync::mpsc;
    use crate::sync::{Mutex, MutexGuard, Once};

    pub type JoinHandle = mpsc::Receiver<()>;

    pub(super) struct Task {
        p: Box<dyn FnOnce()>,
        done: mpsc::Sender<()>,
        tcs: Tcs,
    }

    impl Task {
        pub(super) fn new(tcs: Tcs, p: Box<dyn FnOnce()>) -> (Task, JoinHandle) {
            let (done, recv) = mpsc::channel();
            let task = Task { p, done, tcs };
            (task, recv)
        }

        pub(super) fn run(self) {
            let Task { tcs, p, done } = self;

            p();

            let _ = done.send(());
            // The TCS may be scheduled before it actually finished execution. This is
            // mitigated by the enclave runner by blocking until the TCS actually finished
            tcs_queue::add_tcs(tcs);
        }
    }

    #[cfg_attr(test, linkage = "available_externally")]
    #[export_name = "_ZN16__rust_internals3std3sys3sgx6thread15TASK_QUEUE_INITE"]
    static TASK_QUEUE_INIT: Once = Once::new();
    #[cfg_attr(test, linkage = "available_externally")]
    #[export_name = "_ZN16__rust_internals3std3sys3sgx6thread10TASK_QUEUEE"]
    static mut TASK_QUEUE: Option<Mutex<Vec<Task>>> = None;

    pub(super) fn lock() -> MutexGuard<'static, Vec<Task>> {
        unsafe {
            TASK_QUEUE_INIT.call_once(|| TASK_QUEUE = Some(Default::default()));
            TASK_QUEUE.as_ref().unwrap().lock().unwrap()
        }
    }

    pub(super) fn take_task(tcs: NonNull<u8>) -> Option<Task> {
        let mut tasks = lock();
        let (i, _) = tasks.iter().enumerate().find(|(_i, task)| *task.tcs.address() == tcs)?;
        let task = tasks.remove(i);
        Some(task)
    }
}

impl Thread {
    fn create_dynamic_thread(stack_size: usize) -> io::Result<*mut u8> {
        fn alloc_area(size: usize, alignment: usize) -> io::Result<*mut u8> {
            let page =
                unsafe { crate::alloc::alloc(Layout::from_size_align_unchecked(size, alignment)) };
            if !page.is_null() { Ok(page) } else { Err(io::ErrorKind::UnexpectedEof.into()) }
        }

        /// Allocates a new stack guarded with guard pages
        /// Returns a pointer to the top of the stack
        fn alloc_stack(stack_size: usize) -> io::Result<(*mut u8, *mut u8)> {
            let stack = alloc::alloc_guarded_area(stack_size, DEFAULT_STACK_GUARD_SIZE)
                .ok_or(io::ErrorKind::UnexpectedEof)?;
            let tos =
                unsafe { stack.offset(DEFAULT_STACK_GUARD_SIZE as isize + stack_size as isize) };
            Ok((stack, tos))
        }

        /// Allocates a new SSA stack
        fn alloc_ssa_stack(nssa: usize) -> io::Result<*mut u8> {
            alloc_area(nssa * Sgx::PAGE_SIZE, Sgx::PAGE_SIZE)
        }

        /// Creates a new TLS area
        fn alloc_tls(stack_tos: *mut u8) -> io::Result<*mut u8> {
            let tls_area = alloc_area(mem::size_of::<Tls>(), alloc::Sgx::PAGE_SIZE)?;
            unsafe {
                let tos_offset = stack_tos.offset_from(sgx_mem::image_base() as _).try_into().unwrap();
                let tls_area = mem::transmute::<_, *mut Tls>(tls_area);
                *tls_area = Tls::new(tos_offset, TlsFlags::SECONDARY_TCS);
            }
            Ok(tls_area as _)
        }

        fn new_tcs(stack_size: usize) -> io::Result<*mut u8> {
            let (_stack, stack_tos) = alloc_stack(stack_size)?;
            let ssa = alloc_ssa_stack(abi::nssa() as _)?;
            let tls = alloc_tls(stack_tos)?;
            let entry = unsafe { mem::transmute::<_, *const u8>(enclave_entry()) };

            unsafe {
                let tcs: *mut Tcs = alloc_area(Sgx::PAGE_SIZE, Sgx::PAGE_SIZE)? as _;
                *tcs = Tcs {
                    ossa: ssa.offset_from(sgx_mem::image_base() as _) as _,
                    nssa: abi::nssa() as _,
                    oentry: entry.offset_from(sgx_mem::image_base() as _) as _,
                    ofsbasgx: tls.offset_from(sgx_mem::image_base() as _) as _,
                    ogsbasgx: tls.offset_from(sgx_mem::image_base() as _) as _,
                    fslimit: (mem::size_of::<Tls>() - 1) as _,
                    gslimit: (mem::size_of::<Tls>() - 1) as _,
                    ..Tcs::default()
                };
                Ok(tcs as _)
            }
        }

        let tcs = new_tcs(stack_size)?;

        // Ask SGX driver to change page type
        usercalls::change_memory_type(tcs, Sgx::PAGE_SIZE, PageType::Tcs)?;

        // Accept page type changes
        let flags = SecinfoFlags::from(PageType::Tcs) | SecinfoFlags::MODIFIED;
        let secinfo = Secinfo::from(flags).into();
        arch::eaccept(tcs as _, &secinfo).map_err(|_e| {
            io::Error::new(io::ErrorKind::InvalidData, "OS prevented creation of TCS struct")
        })?;

        Ok(tcs)
    }

    // unsafe: see thread::Builder::spawn_unchecked for safety requirements
    pub unsafe fn new(stack: usize, p: Box<dyn FnOnce()>) -> io::Result<Thread> {
        let tcs = tcs_queue::take_tcs(stack).ok_or(io::Error::from(io::ErrorKind::WouldBlock))?;
        let mut tasks = task_queue::lock();
        unsafe { usercalls::launch_thread(tcs.address().as_ptr() as _)? };
        let (task, handle) = task_queue::Task::new(tcs, p);
        tasks.push(task);
        Ok(Thread(handle))
    }

    pub(super) fn entry() {
        let task = task_queue::take_task(thread::current())
            .expect("enclave entered through TCS unexpectedly");
        task.run()
    }

    pub fn yield_now() {
        let wait_error = rtunwrap!(Err, usercalls::wait(0, usercalls::raw::WAIT_NO));
        rtassert!(wait_error.kind() == io::ErrorKind::WouldBlock);
    }

    pub fn set_name(_name: &CStr) {
        // FIXME: could store this pointer in TLS somewhere
    }

    pub fn sleep(dur: Duration) {
        usercalls::wait_timeout(0, dur, || true);
    }

    pub fn join(self) {
        let _ = self.handle.recv();
    }
}

pub mod guard {
    pub type Guard = !;
    pub unsafe fn current() -> Option<Guard> {
        None
    }
    pub unsafe fn init() -> Option<Guard> {
        None
    }
}
