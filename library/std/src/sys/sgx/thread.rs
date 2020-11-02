#![cfg_attr(test, allow(dead_code))] // why is this necessary?
use fortanix_sgx_abi::tcsls::{Tcsls, TcslsFlags};
use super::ext::arch;
use crate::ffi::CStr;
use crate::io;
use crate::os::fortanix_sgx::mem::enclave_entry;
use crate::sys::alloc::{self, Sgx, MemoryArea};
use crate::sys::sgx::abi;
use crate::sys::sgx::abi::mem as sgx_mem;
use crate::time::Duration;
use core::convert::TryInto;
use core::mem;
use sgx_isa::{PageType, Secinfo, SecinfoFlags, Tcs};

use super::abi::thread;
use super::abi::usercalls;

pub struct Thread {
    handle: task_queue::JoinHandle,
}

#[derive(Debug)]
pub struct ThreadResources {
    stack: MemoryArea,
    ssa: MemoryArea,
    tcsls: MemoryArea,
    tcs: MemoryArea,
}

mod thread_destructor {
    use super::ThreadResources;
    use crate::sync::{Mutex, Once};

    static mut STOPPED_THREAD_INIT: Once = Once::new();
    static mut STOPPED_THREAD: Option<Mutex<Option<ThreadResources>>> = None;

    pub fn destruct_thread_resources(resources: ThreadResources) {
        unsafe {
            STOPPED_THREAD_INIT.call_once(|| STOPPED_THREAD = Some(Mutex::new(None)));
            let mut last_resources = STOPPED_THREAD.as_ref().unwrap().lock().unwrap();
            *last_resources = Some(resources)
        }
    }
}

pub const DEFAULT_MIN_STACK_SIZE: usize = 2 * 1024 * 1024;
const DEFAULT_STACK_GUARD_SIZE: usize = 0x10000;

mod tcs_queue {
    use super::thread_destructor;
    use super::super::abi::{self, SgxVersion};
    use super::super::abi::mem as sgx_mem;
    use super::super::abi::thread;
    use crate::sys::thread::Thread;
    use crate::ptr::NonNull;
    use crate::sync::{Mutex, MutexGuard, Once};
    use crate::sys::thread::ThreadResources;

    pub(super) enum Tcs {
        Static(NonNull<u8>),
        Dynamic(ThreadResources),
    }

    impl Tcs {
        fn new_static(address: NonNull<u8>) -> Tcs {
            Tcs::Static(address)
        }

        fn new_dynamic(resources: ThreadResources) -> Tcs {
            Tcs::Dynamic(resources)
        }

        pub(super) fn address(&self) -> NonNull<u8> {
            match self {
                Tcs::Static(ptr) => ptr.to_owned(),
                Tcs::Dynamic(resources) => NonNull::new(resources.tcs.start()).unwrap(),
            }
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
                        tcs_queue.push(Tcs::new_static(address));
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

    pub(super) fn select_tcs(stack: usize) -> Option<Tcs> {
        match abi::sgx_version() {
            SgxVersion::SGXv1 => {
                let mut tcs_queue = lock();
                tcs_queue.pop()
            },
            SgxVersion::SGXv2 => {
                Some(Tcs::new_dynamic(Thread::create_dynamic_thread(stack).ok()?))
            }
        }
    }

    pub(super) fn release_tcs(tcs: Tcs) {
        match tcs {
            Tcs::Static(tcs) => {
                let mut tcs_queue = lock();
                // The TCS may be scheduled before it actually finished execution. This is
                // mitigated by the enclave runner by blocking until the TCS actually finished
                tcs_queue.insert(0, Tcs::Static(tcs));
            },
            Tcs::Dynamic(resources) => {
                thread_destructor::destruct_thread_resources(resources)
            }
        }
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
            tcs_queue::release_tcs(tcs);
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
        let (i, _) = tasks.iter().enumerate().find(|(_i, task)| task.tcs.address() == tcs)?;
        let task = tasks.remove(i);
        Some(task)
    }
}

impl Thread {
    fn create_dynamic_thread(stack_size: usize) -> io::Result<ThreadResources> {
        /// Creates a new TCS local storage area
        fn alloc_tcsls(stack_tos: *mut u8) -> io::Result<MemoryArea> {
            let tcsls_area = Sgx::alloc_guarded_area(alloc::Sgx::PAGE_SIZE, alloc::Sgx::PAGE_SIZE).ok_or(io::ErrorKind::UnexpectedEof)?;
            unsafe {
                let tos_offset = stack_tos.offset_from(sgx_mem::image_base() as _).try_into().unwrap();
                let tcsls_area = mem::transmute::<_, *mut Tcsls>(tcsls_area.start());
                *tcsls_area = Tcsls::new(tos_offset, TcslsFlags::SECONDARY_TCS);
            }
            Ok(tcsls_area)
        }

        fn new_tcs(stack_size: usize) -> io::Result<ThreadResources> {
            let stack = Sgx::alloc_guarded_area(stack_size, DEFAULT_STACK_GUARD_SIZE).ok_or(io::ErrorKind::UnexpectedEof)?;
            let ssa = Sgx::alloc_guarded_area(abi::nssa() as usize * Sgx::PAGE_SIZE, Sgx::PAGE_SIZE).ok_or(io::ErrorKind::UnexpectedEof)?;
            let tcsls = alloc_tcsls(stack.end())?;
            let entry = unsafe { mem::transmute::<_, *const u8>(enclave_entry()) };

            unsafe {
                let tcs_page = Sgx::alloc_guarded_area(Sgx::PAGE_SIZE, Sgx::PAGE_SIZE).ok_or(io::ErrorKind::UnexpectedEof)?;
                let tcs: *mut Tcs = tcs_page.start() as _;
                *tcs = Tcs {
                    ossa: ssa.start().offset_from(sgx_mem::image_base() as _) as _,
                    nssa: abi::nssa() as _,
                    oentry: entry.offset_from(sgx_mem::image_base() as _) as _,
                    ofsbasgx: tcsls.start().offset_from(sgx_mem::image_base() as _) as _,
                    ogsbasgx: tcsls.start().offset_from(sgx_mem::image_base() as _) as _,
                    fslimit: (mem::size_of::<Tcsls>() - 1) as _,
                    gslimit: (mem::size_of::<Tcsls>() - 1) as _,
                    ..Tcs::default()
                };

                Ok(ThreadResources {
                    stack,
                    ssa,
                    tcsls,
                    tcs: tcs_page,
                })
            }
        }

        let resources = new_tcs(stack_size)?;

        // Ask SGX driver to change page type
        usercalls::change_memory_type(resources.tcs.start(), Sgx::PAGE_SIZE, PageType::Tcs)?;

        // Accept page type changes
        let flags = SecinfoFlags::from(PageType::Tcs) | SecinfoFlags::MODIFIED;
        let secinfo = Secinfo::from(flags).into();
        arch::eaccept(resources.tcs.start() as _, &secinfo).map_err(|_e| {
            io::Error::new(io::ErrorKind::InvalidData, "OS prevented creation of TCS struct")
        })?;

        Ok(resources)
    }

    // unsafe: see thread::Builder::spawn_unchecked for safety requirements
    pub unsafe fn new(stack: usize, p: Box<dyn FnOnce()>) -> io::Result<Thread> {
        let tcs = tcs_queue::select_tcs(stack).ok_or(io::Error::from(io::ErrorKind::WouldBlock))?;
        let mut tasks = task_queue::lock();
        unsafe { usercalls::launch_thread(tcs.address().as_ptr() as _)? };
        let (task, handle) = task_queue::Task::new(tcs, p);
        tasks.push(task);
        Ok(Thread { handle })
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
