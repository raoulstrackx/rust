// Do not remove inline: will result in relocation failure
#[inline(always)]
pub(crate) unsafe fn rel_ptr<T>(offset: u64) -> *const T {
    (image_base() + offset) as *const T
}

// Do not remove inline: will result in relocation failure
#[inline(always)]
pub(crate) unsafe fn rel_ptr_mut<T>(offset: u64) -> *mut T {
    (image_base() + offset) as *mut T
}

extern "C" {
    static ENCLAVE_SIZE: usize;
    static HEAP_BASE: u64;
    static HEAP_SIZE: usize;
    static UNMAPPED_SIZE: u64;
    static UNMAPPED_BASE: u64;
    static TCS_LIST: u64;
}

/// Returns the base memory address of the heap
pub(crate) fn heap_base() -> *const u8 {
    unsafe { rel_ptr_mut(HEAP_BASE) }
}

/// Returns the size of the heap
pub(crate) fn heap_size() -> usize {
    unsafe { HEAP_SIZE }
}

// Do not remove inline: will result in relocation failure
// For the same reason we use inline ASM here instead of an extern static to
// locate the base
/// Returns address at which current enclave is loaded.
#[inline(always)]
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn image_base() -> u64 {
    let base: u64;
    unsafe {
        asm!(
            "lea IMAGE_BASE(%rip), {}",
            lateout(reg) base,
            // NOTE(#76738): ATT syntax is used to support LLVM 8 and 9.
            options(att_syntax, nostack, preserves_flags, nomem, pure),
        )
    };
    base
}

/// Returns `true` if the specified memory range is in the enclave.
///
/// `p + len` must not overflow.
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn is_enclave_range(p: *const u8, len: usize) -> bool {
    let start = p as u64;
    let end = start + (len as u64);
    start >= image_base() && end <= image_base() + (unsafe { ENCLAVE_SIZE } as u64) // unsafe ok: link-time constant
}

/// Returns `true` if the specified memory range is in userspace.
///
/// `p + len` must not overflow.
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn is_user_range(p: *const u8, len: usize) -> bool {
    let start = p as u64;
    let end = start + (len as u64);
    end <= image_base() || start >= image_base() + (unsafe { ENCLAVE_SIZE } as u64) // unsafe ok: link-time constant
}

/// Returns the base memory address of the unmapped memory area. On platforms with SGXv2 features,
/// this region can be used to dynamically add enclave pages
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn unmapped_base() -> u64 {
    unsafe { image_base() + UNMAPPED_BASE }
}

/// Returns the size of the unmapped memory area
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn unmapped_size() -> u64 {
    unsafe { UNMAPPED_SIZE }
}

/// Returns the base memory address of the entry code
#[unstable(feature = "sgx_platform", issue = "56975")]
#[inline(always)]
pub fn enclave_entry() -> u64 {
    let base: u64;
    unsafe {
        asm!(
            "lea sgx_entry(%rip), {}",
            lateout(reg) base,
            // NOTE(#76738): ATT syntax is used to support LLVM 8 and 9.
            options(att_syntax, nostack, preserves_flags, nomem, pure),
        )
    };
    base
}

/// Returns whether the pointer is part of the unmapped memory range
/// `p + len` must not overflow
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn is_unmapped_range(p: *const u8, len: usize) -> bool {
    let start = p as u64;
    let end = start + (len as u64);
    start >= unmapped_base() && end <= unmapped_base() + unmapped_size() // unsafe ok: link-time constant
}

/// Returns the location of the TCS array. Each item in the array is a pointer (relative from
/// enclave base) to a TCS created at enclave build time.
#[unstable(feature = "sgx_platform", issue = "56975")]
pub fn tcs_ptr_array() -> *const u64 {
    unsafe { rel_ptr_mut(TCS_LIST) }
}
