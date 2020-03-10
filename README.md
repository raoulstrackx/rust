# rustc Compiler

When the LVI vulnerability was/will be made public, the mitigations will not be merged upstream in rustc/llvm:

  - The LVI passes may not be available
  - The passes will definitively not include hardening of (function-level) inline assembly
  - We had to write our own module-level inline assembly pass. 

This repository contains all those patches to be used within Fortanix.

