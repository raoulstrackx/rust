// Test LVI load hardening on SGX inline assembly code

// assembly-output: emit-asm
// compile-flags: --crate-type staticlib
// only-x86_64-fortanix-unknown-sgx

#![feature(asm)]

#[no_mangle]
pub extern fn get(ptr: &u64) -> u64 {
    let value : u64;
    unsafe {
        asm!(".start_inline_asm:
            movq ($1), $0
            .end_inline_asm:"
            : "=r"(value)
            : "r"(ptr) );
    }
    value
}

// CHECK: get
// CHECK: .start_inline_asm
// CHECK-NEXT: movq
// CHECK-NEXT: lfence
// CHECK-NEXT: .end_inline_asm

#[no_mangle]
pub extern fn myret() {
    unsafe {
        asm!(".start_myret_inline_asm:
            retq
            .end_myret_inline_asm:");
    }
}

// CHECK: myret
// CHECK: .start_myret_inline_asm
// CHECK-NEXT: notq (%rsp)
// CHECK-NEXT: notq (%rsp)
// CHECK-NEXT: lfence
// CHECK-NEXT: retq
