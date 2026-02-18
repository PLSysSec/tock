# TickTock

This repository contains TickTock-a fork of the Tock OS that verifies memory isolation for user space processes. [Flux](https://github.com/flux-rs/flux) is used for the verification.

You can find the paper [here](https://dl.acm.org/doi/epdf/10.1145/3731569.3764856).

The main verification bits can be found under the `kernel` directory, along with the arch directory. Specifically, `allocator.rs` contains the memory allocator referenced in the paper. `arch/cortex-m/src/mpu.rs` contains the MPU implementation for ARMv6m and ARMv7m devices. `arch/rv32i/src/pmp.rs` contains the MPU implementation for RISC devices.

You can find Lean proofs for SMT solver issues in this [repo](https://github.com/PLSysSec/vtock-lean). Verification of the ARM interrupt handlers and context switching code can be found in this [repo](https://github.com/PLSysSec/tock-veri-asm).

The original Tock repo can be found [here](https://github.com/tock/tock).