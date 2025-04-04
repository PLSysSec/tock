#![no_std]
use core::ops::{Deref, DerefMut};
use core::ptr::{null, null_mut, NonNull};

#[allow(dead_code)]
#[flux_rs::sig(fn(x: bool[true]))]
pub fn assert(_x: bool) {}

#[flux_rs::sig(fn(b:bool) ensures b)]
pub fn assume(b: bool) {}

// #[flux_rs::opaque]
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct FluxPtr {
    inner: *mut u8,
}

// VTOCK-TODO: fill in these functions with obvious implementations
impl FluxPtr {
    pub const fn wrapping_add(self, count: usize) -> FluxPtr {
        Self {
            inner: self.inner.wrapping_add(count),
        }
    }

    pub const fn wrapping_sub(self, count: usize) -> FluxPtr {
        Self {
            inner: self.inner.wrapping_sub(count),
        }
    }

    pub fn is_null(self) -> bool {
        self.inner.is_null()
    }

    pub fn as_usize(self) -> usize {
        self.inner as usize
    }

    pub fn as_u32(self) -> u32 {
        self.inner as u32
    }

    pub const unsafe fn offset(self, count: isize) -> Self {
        Self {
            inner: self.inner.offset(count),
        }
    }

    pub const unsafe fn add(self, count: usize) -> Self {
        Self {
            inner: self.inner.add(count),
        }
    }

    pub fn unsafe_as_ptr(self) -> *mut u8 {
        self.inner
    }

    pub const fn null() -> Self {
        Self {
            inner: null::<u8>() as *mut u8,
        }
    }

    pub const fn null_mut() -> Self {
        Self {
            inner: null_mut::<u8>() as *mut u8,
        }
    }
}

// impl From<usize> for FluxPtr {
//     fn from(_item: usize) -> Self {
//         unimplemented!()
//         // Number { value: item }
//     }
// }

// impl Into<usize> for FluxPtr {
//     fn into(self) -> usize {
//         unimplemented!()
//         // Number { value: self }
//     }
// }

pub type FluxPtrU8 = FluxPtr;
pub type FluxPtrU8Mut = FluxPtr;

pub trait FluxPtrExt {
    fn as_fluxptr(&self) -> FluxPtr;
}

impl FluxPtrExt for *mut u8 {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr { inner: *self }
    }
}

impl FluxPtrExt for *const u8 {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr {
            inner: *self as *mut u8,
        }
    }
}

impl<T> FluxPtrExt for &[T] {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr {
            inner: self.as_ptr() as *mut u8,
        }
    }
}

impl<T> FluxPtrExt for &mut [T] {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr {
            inner: self.as_ptr() as *mut u8,
        }
    }
}

impl<T> FluxPtrExt for NonNull<T> {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr {
            inner: self.as_ptr() as *mut u8,
        }
    }
}

impl FluxPtrExt for usize {
    fn as_fluxptr(&self) -> FluxPtr {
        FluxPtr {
            inner: *self as *mut u8,
        }
    }
}

impl Deref for FluxPtr {
    type Target = u8;

    fn deref(&self) -> &Self::Target {
        unsafe { &*self.inner }
    }
}

impl DerefMut for FluxPtr {
    fn deref_mut(&mut self) -> &mut Self::Target {
        unsafe { &mut *self.inner }
    }
}
