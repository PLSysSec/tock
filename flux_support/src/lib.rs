#![no_std]

mod extern_specs;
mod flux_arr;
mod flux_pair;
mod flux_ptr;
mod flux_range;
mod flux_register_interface;
mod math;
use core::panic;
pub use flux_arr::*;
pub use flux_pair::*;
pub use flux_ptr::*;
pub use flux_range::*;
pub use flux_register_interface::*;
pub use math::*;

#[macro_export]
macro_rules! const_assume {
    ($cond:expr) => {
        const { assert!($cond) };
        $crate::assume($cond);
    }
}

#[allow(dead_code)]
#[flux_rs::sig(fn(x: bool[true]))]
pub const fn assert(_x: bool) {}

#[flux_rs::sig(fn(b:bool) ensures b)]
pub const fn assume(b: bool) {
    if !b {
        panic!("assume fails")
    }
}

#[flux_rs::trusted]
#[flux_rs::sig(fn(a: usize, b: usize) -> usize[a + b])]
pub fn flux_trusted_add(a: usize, b: usize) -> usize {
    a + b
}


pub mod capability {
    use super::FluxPtrU8;

    flux_rs::defs! {
        fn mpu_configured_for(start: int, brk: int) -> bool;
    }

    #[flux_rs::refined_by(start: int, brk: int)]
    #[flux_rs::invariant(mpu_configured_for(start, brk))]
    pub struct MpuConfiguredCapability {
        #[field(FluxPtrU8[start])]
        pub start: FluxPtrU8,
        #[field(FluxPtrU8[brk])]
        pub brk: FluxPtrU8,
    }

    impl MpuConfiguredCapability {
        #[flux_rs::trusted(
            reason = "Trusted initializer for capability establishing the MPU is configured for this apps start and brk"
        )]
        #[flux_rs::sig(fn (start: FluxPtrU8, brk: FluxPtrU8) -> Self)]
        pub fn new(start: FluxPtrU8, brk: FluxPtrU8) -> Self {
            Self { start, brk }
        }
    }

    pub struct MpuEnabledCapability {}

    impl MpuEnabledCapability {
        pub fn new() -> Self {
            Self {}
        }
    }
}
