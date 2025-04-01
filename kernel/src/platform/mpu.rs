// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Interface for configuring the Memory Protection Unit.

use core::fmt::{self, Display};
#[allow(clippy::wildcard_imports)]
use flux_support::*;

#[derive(Copy, Clone, Debug)]
#[flux_rs::refined_by(r: bool, w: bool, x: bool)]
pub enum Permissions {
    #[flux::variant(Permissions[true, true, true])]
    ReadWriteExecute,
    #[flux::variant(Permissions[true, true, false])]
    ReadWriteOnly,
    #[flux::variant(Permissions[true, false, true])]
    ReadExecuteOnly,
    #[flux::variant(Permissions[true, false, false])]
    ReadOnly,
    #[flux::variant(Permissions[false, false, true])]
    ExecuteOnly,
}

#[derive(Copy, Clone, PartialEq, Eq)]
#[flux_rs::refined_by(ptr: int, sz: int)]
pub struct Region {
    /// The memory address where the region starts.
    ///
    /// For maximum compatibility, we use a u8 pointer, however, note that many
    /// memory protection units have very strict alignment requirements for the
    /// memory regions protected by the MPU.
    #[flux_rs::field(FluxPtrU8Mut[ptr])]
    start_address: FluxPtrU8Mut,

    /// The number of bytes of memory in the MPU region.
    #[flux_rs::field(usize[sz])]
    size: usize,
}

impl Region {
    /// Create a new MPU region with a given starting point and length in bytes.
    #[flux_rs::sig(fn (FluxPtrU8Mut[@start], usize[@size]) -> Region[start, size])]
    pub fn new(start_address: FluxPtrU8Mut, size: usize) -> Region {
        Region {
            start_address,
            size,
        }
    }

    /// Getter: retrieve the address of the start of the MPU region.
    pub fn start_address(&self) -> FluxPtrU8Mut {
        self.start_address
    }

    /// Getter: retrieve the length of the region in bytes.
    pub fn size(&self) -> usize {
        self.size
    }
}

#[derive(Clone, Copy)]
#[flux_rs::opaque]
#[flux_rs::refined_by(start: int, size: int)]
struct RegionDefaultGhost {}

impl RegionDefaultGhost {
    #[flux_rs::trusted]
    #[flux_rs::sig(fn () -> Self)]
    fn unset() -> Self {
        Self {}
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn (start: FluxPtrU8, size: usize) -> Self[start, size])]
    fn set(_start: FluxPtrU8, _size: usize) -> Self {
        Self {}
    }
}

/// Null type for the default type of the `MpuConfig` type in an implementation
/// of the `MPU` trait. This custom type allows us to implement `Display` with
/// an empty implementation to meet the constraint on `type MpuConfig`.
#[derive(Clone, Copy)]
#[flux_rs::refined_by(set: bool, rnum: int, start: int, size: int)]
pub struct MpuRegionDefault {
    #[field(Option<{p. FluxPtrU8[p] | p == start}>[set])]
    start: Option<FluxPtrU8>,

    #[field(Option<{sz. usize[sz] | sz == size}>[set])]
    size: Option<usize>,

    #[field(usize[rnum])]
    region_number: usize,

    #[field(RegionDefaultGhost[start, size])]
    _ghost: RegionDefaultGhost
}

impl Display for MpuRegionDefault {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[flux_rs::assoc(fn astart(self: Self) -> int)]
#[flux_rs::assoc(fn asize(self: Self) -> int)]
#[flux_rs::assoc(fn rstart(self: Self) -> int)]
#[flux_rs::assoc(fn rsize(self: Self) -> int)]
#[flux_rs::assoc(fn rnum(self: Self) -> int)]
#[flux_rs::assoc(fn is_set(self: Self) -> bool)]
pub trait RegionDescriptor {
    #[flux_rs::sig(fn (region_num: usize) -> Self {s: !<Self as RegionDescriptor>::is_set(s) })]
    fn default(region_num: usize) -> Self;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{p. FluxPtrU8[p] | p == <Self as RegionDescriptor>::astart(r)}>)]
    fn accessible_start(&self) -> Option<FluxPtrU8>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{p. FluxPtrU8[p] | p == <Self as RegionDescriptor>::rstart(r)}>)]
    fn region_start(&self) -> Option<FluxPtrU8>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{sz. usize[sz] | sz == <Self as RegionDescriptor>::asize(r)}>)]
    fn accessible_size(&self) -> Option<usize>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{sz. usize[sz] | sz == <Self as RegionDescriptor>::rsize(r)}>)]
    fn region_size(&self) -> Option<usize>;

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool;

    #[flux_rs::sig(fn (&Self[@r]) -> usize[<Self as RegionDescriptor>::rnum(r)])]
    fn region_num(&self) -> usize;

    fn overlaps(&self, other: &Self) -> bool;
}

#[flux_rs::assoc(fn astart(self: Self) -> int { self.start })]
#[flux_rs::assoc(fn asize(self: Self) -> int { self.size })]
#[flux_rs::assoc(fn rstart(self: Self) -> int { self.start })]
#[flux_rs::assoc(fn rsize(self: Self) -> int { self.size })]
#[flux_rs::assoc(fn rnum(self: Self) -> int { self.rnum })]
#[flux_rs::assoc(fn is_set(self: Self) -> bool { self.set })]
impl RegionDescriptor for MpuRegionDefault {
    #[flux_rs::sig(fn (region_num: usize) -> Self {s: !s.set})]
    fn default(num: usize) -> Self {
        Self {
            start: None,
            size: None,
            _ghost: RegionDefaultGhost::unset(),
            region_number: num,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{p. FluxPtrU8[p] | p == r.start }>)]
    fn accessible_start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{p. FluxPtrU8[p] | p == r.start }>)]
    fn region_start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{sz. usize[sz] | sz == r.size }>)]
    fn accessible_size(&self) -> Option<usize> {
        self.size
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<{sz. usize[sz] | sz == r.size }>)]
    fn region_size(&self) -> Option<usize> {
        self.size
    }

    #[flux_rs::sig(fn (&Self[@r]) -> usize[r.rnum])]
    fn region_num(&self) -> usize {
        self.region_number 
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[r.set])]
    fn is_set(&self) -> bool {
        self.start.is_some()
    }

    fn overlaps(&self, _other: &Self) -> bool {
        false
    }
}

/// The generic trait that particular memory protection unit implementations
/// need to implement.
///
/// This trait is implements generic MPU functionality that is common across different
/// MPU implementations.
#[flux_rs::assoc(fn enabled(self: Self) -> bool)]
#[flux_rs::assoc(fn disabled(self: Self) -> bool)]
pub trait MPU {
    /// MPU-specific state that defines a region for the MPU.
    /// That is, this should contain all of the required state such that the
    /// implementation can be passed an array of of this type and it should be
    /// able to correctly and entirely configure the MPU.
    ///
    /// This state will be held on a per-process basis as a way to cache all of
    /// the process settings. When the kernel switches to a new process it will
    /// use the `MpuConfig` for that process to quickly configure the MPU.
    ///
    /// It is `Default` so we can create empty state when the process is
    /// created, and `Display` so that the `panic!()` output can display the
    /// current state to help with debugging.
    type Region: RegionDescriptor + Display + Copy;

    /// Enables the MPU for userspace apps.
    ///
    /// This function must enable the permission restrictions on the various
    /// regions protected by the MPU.
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{r: <Self as MPU>::enabled(r)})]
    fn enable_app_mpu(&mut self);

    /// Disables the MPU for userspace apps.
    ///
    /// This function must disable any access control that was previously setup
    /// for an app if it will interfere with the kernel.
    /// This will be called before the kernel starts to execute as on some
    /// platforms the MPU rules apply to privileged code as well, and therefore
    /// some of the MPU configuration must be disabled for the kernel to effectively
    /// manage processes.
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{r: <Self as MPU>::disabled(r)})]
    fn disable_app_mpu(&mut self);

    /// Returns the maximum number of regions supported by the MPU.
    fn number_total_regions(&self) -> usize;

    ///
    /// Deals with the alignment, size, and other constraints of the specific
    /// MPU to create a new region.
    ///
    /// Returns None if the MPU cannot allocate a region with the passed
    /// constraints
    #[flux_rs::sig(
        fn (
            self: &Self,
            region_number: usize, 
            available_start: FluxPtrU8, 
            available_size: usize, 
            region_size: usize, 
            permissions: Permissions,
        ) -> Option<{r. Self::Region[r] | 
            // region is set
            <Self::Region as RegionDescriptor>::is_set(r) &&
            // region is within available start generally
            <Self::Region as RegionDescriptor>::astart(r) >= available_start &&
            // if the region size is the same as the available size then the start is exact
            (available_size == region_size =>  <Self::Region as RegionDescriptor>::astart(r) == available_start) &&
            // region accessible size is equal to the size asked for
            <Self::Region as RegionDescriptor>::asize(r) == region_size &&
            // region fits into space 
            <Self::Region as RegionDescriptor>::astart(r) + <Self::Region as RegionDescriptor>::asize(r) <= available_start + available_size &&
            // accessible start is ok
            <Self::Region as RegionDescriptor>::astart(r) >= <Self::Region as RegionDescriptor>::rstart(r) &&
            // accessible region is within bounds
            <Self::Region as RegionDescriptor>::astart(r) + <Self::Region as RegionDescriptor>::asize(r) <= <Self::Region as RegionDescriptor>::rstart(r) + <Self::Region as RegionDescriptor>::rsize(r)
        }>
    )]
    fn new_region(
        &self,
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Self::Region>;

    /// Configures the MPU with the provided region configuration.
    ///
    /// An implementation must ensure that all memory locations not covered by
    /// an allocated region are inaccessible in user mode and accessible in
    /// supervisor mode.
    ///
    /// # Arguments
    ///
    /// - `region`: MPU region to be configured
    fn configure_mpu(&mut self, regions: &[Self::Region]);
}

// /// Implement default MPU trait for unit.
#[flux_rs::assoc(fn enabled(self: Self) -> bool { true })]
#[flux_rs::assoc(fn disabled(self: Self) -> bool { true })]
impl MPU for () {
    type Region = MpuRegionDefault;

    #[flux_rs::sig(fn (self: &strg Self) ensures self: Self)]
    fn enable_app_mpu(&mut self) {}

    #[flux_rs::sig(fn (self: &strg Self) ensures self: Self)]
    fn disable_app_mpu(&mut self) {}

    fn number_total_regions(&self) -> usize {
        0
    }

    fn configure_mpu(&mut self, _config: &[Self::Region]) {}

    #[flux_rs::sig(
        fn (
            self: &Self,
            region_number: usize, 
            available_start: FluxPtrU8, 
            available_size: usize, 
            region_size: usize, 
            permissions: Permissions,
        ) -> Option<{r. Self::Region[r] | 
            // region is set
            <<Self as MPU>::Region as RegionDescriptor>::is_set(r) &&
            // region number is set
            <<Self as MPU>::Region as RegionDescriptor>::rnum(r) == region_number &&
            // region is within available start
            <<Self as MPU>::Region as RegionDescriptor>::astart(r) >= available_start &&
            // region accessible size is equal to the size asked for
            <<Self as MPU>::Region as RegionDescriptor>::asize(r) == region_size &&
            // region fits into space 
            <<Self as MPU>::Region as RegionDescriptor>::astart(r) + <<Self as MPU>::Region as RegionDescriptor>::asize(r) <= available_start + available_size &&
            // accessible start is ok
            <<Self as MPU>::Region as RegionDescriptor>::astart(r) >= <<Self as MPU>::Region as RegionDescriptor>::rstart(r) &&
            // accessible region is within bounds
            <<Self as MPU>::Region as RegionDescriptor>::astart(r) + <<Self as MPU>::Region as RegionDescriptor>::asize(r) <= <Self::Region as RegionDescriptor>::rstart(r) + <Self::Region as RegionDescriptor>::rsize(r)
        }>
    )]
    fn new_region(
        &self,
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        _permissions: Permissions,
    ) -> Option<Self::Region> {
        if region_size <= available_size {
            Some(MpuRegionDefault {
                start: Some(available_start),
                size: Some(region_size),
                region_number,
                _ghost: RegionDefaultGhost::set(available_start, region_size)
            })
        } else {
            None
        }
    }
}
