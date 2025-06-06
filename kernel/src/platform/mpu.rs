// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Interface for configuring the Memory Protection Unit.

use core::fmt::{self, Display};
use flux_support::capability::*;
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
pub struct Region {
    /// The memory address where the region starts.
    ///
    /// For maximum compatibility, we use a u8 pointer, however, note that many
    /// memory protection units have very strict alignment requirements for the
    /// memory regions protected by the MPU.
    start_address: FluxPtrU8Mut,

    /// The number of bytes of memory in the MPU region.
    size: usize,
}

impl Region {
    /// Create a new MPU region with a given starting point and length in bytes.
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

#[flux_rs::opaque]
#[flux_rs::refined_by(start: int, size: int, permissions: Permissions)]
#[derive(Clone, Copy)]
struct DefaultGhost {}

#[flux_rs::trusted(reason = "opaque wrapper")]
impl DefaultGhost {
    #[flux_rs::sig(fn (start: FluxPtrU8, size: usize, perms: Permissions) -> Self[start, size, perms])]
    pub fn new(start: FluxPtrU8, size: usize, perms: Permissions) -> Self {
        Self {}
    }

    pub fn empty() -> Self {
        Self {}
    }
}

/// Null type for the default type of the `MpuConfig` type in an implementation
/// of the `MPU` trait. This custom type allows us to implement `Display` with
/// an empty implementation to meet the constraint on `type MpuConfig`.
#[derive(Clone, Copy)]
#[flux_rs::refined_by(start: int, size: int, perms: Permissions, is_set: bool, rnum: int)]
pub struct MpuRegionDefault {
    #[field(Option<FluxPtrU8[start]>[is_set])]
    start: Option<FluxPtrU8>,
    #[field(Option<usize[size]>[is_set])]
    size: Option<usize>,
    #[field(Option<Permissions[perms]>[is_set])]
    perms: Option<Permissions>,
    #[field(usize[rnum])]
    region_number: usize,
    #[field(DefaultGhost[start, size, perms])]
    _ghost: DefaultGhost,
}

impl Display for MpuRegionDefault {
    fn fmt(&self, _f: &mut fmt::Formatter<'_>) -> fmt::Result {
        Ok(())
    }
}

#[flux_rs::assoc(fn astart(r: Self) -> int)]
#[flux_rs::assoc(fn rstart(r: Self) -> int)]
#[flux_rs::assoc(fn asize(r: Self) -> int)]
#[flux_rs::assoc(fn rsize(r: Self) -> int)]
#[flux_rs::assoc(fn is_set(r: Self) -> bool)]
#[flux_rs::assoc(fn rnum(r: Self) -> int)]
#[flux_rs::assoc(fn perms(r: Self) -> Permissions)]
// #[flux_rs::assoc(fn region_can_access(r: Self, start: int, end: int, perms: Permissions) -> bool)]
// #[flux_rs::assoc(fn region_cant_access_at_all(r: Self, start: int, end: int) -> bool)]
#[flux_rs::assoc(fn overlaps(r1: Self, r2: Self) -> bool)]
pub trait RegionDescriptor: core::marker::Sized {
    #[flux_rs::sig(fn (rnum: usize) -> Self {r: !<Self as RegionDescriptor>::is_set(r) && <Self as RegionDescriptor>::rnum(r) == rnum})]
    fn default(region_num: usize) -> Self;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::astart(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn accessible_start(&self) -> Option<FluxPtrU8>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::rstart(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn region_start(&self) -> Option<FluxPtrU8>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{ptr: <Self as RegionDescriptor>::asize(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn accessible_size(&self) -> Option<usize>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{ptr: <Self as RegionDescriptor>::rsize(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn region_size(&self) -> Option<usize>;

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool;

    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2]) -> bool[<Self as RegionDescriptor>::overlaps(r1, r2)])]
    fn overlaps(&self, other: &Self) -> bool;

    /// Deals with the alignment, size, and other constraints of the specific
    /// MPU to create a new region.
    ///
    /// Returns None if the MPU cannot allocate a region with the passed
    /// constraints
    #[flux_rs::sig(fn (
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<{r. Self[r] | 
        <Self as RegionDescriptor>::is_set(r) &&
        <Self as RegionDescriptor>::perms(r) == permissions &&
        <Self as RegionDescriptor>::rnum(r) == region_number &&
        <Self as RegionDescriptor>::astart(r) >= available_start &&
        <Self as RegionDescriptor>::astart(r) == <Self as RegionDescriptor>::rstart(r) &&
        <Self as RegionDescriptor>::astart(r) + <Self as RegionDescriptor>::asize(r) <= available_start + available_size &&
        <Self as RegionDescriptor>::asize(r) >= region_size
    }> requires region_number < 8)]
    fn create_bounded_region(
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Self>;

    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        region_number: usize,
        permissions: Permissions,
    ) -> Option<{r. Self[r] | 
        <Self as RegionDescriptor>::is_set(r) &&
        <Self as RegionDescriptor>::rnum(r) == region_number &&
        <Self as RegionDescriptor>::perms(r) == permissions &&
        <Self as RegionDescriptor>::astart(r) == region_start &&
        <Self as RegionDescriptor>::rstart(r) == region_start &&
        <Self as RegionDescriptor>::astart(r) + <Self as RegionDescriptor>::asize(r) <= region_start + available_size &&
        <Self as RegionDescriptor>::asize(r)  >= region_size
    }> requires region_number < 8)]
    fn update_region(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        region_number: usize,
        permissions: Permissions,
    ) -> Option<Self>;

    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize,
            permissions: Permissions,
        ) -> Option<{r. Self[r] | 
                <Self as RegionDescriptor>::is_set(r) &&
                <Self as RegionDescriptor>::rnum(r) == region_number &&
                <Self as RegionDescriptor>::perms(r) == permissions &&
                <Self as RegionDescriptor>::astart(r) == start &&
                <Self as RegionDescriptor>::astart(r) + <Self as RegionDescriptor>::asize(r) == start + size
            }>
        requires region_number < 8
    )]
    fn create_exact_region(
        region_number: usize,
        start: FluxPtrU8,
        size: usize,
        permissions: Permissions,
    ) -> Option<Self>;

}

#[flux_rs::assoc(fn astart(r: Self) -> int { r.start })]
#[flux_rs::assoc(fn rstart(r: Self) -> int { r.start })]
#[flux_rs::assoc(fn asize(r: Self) -> int { r.size })]
#[flux_rs::assoc(fn rsize(r: Self) -> int { r.size })]
#[flux_rs::assoc(fn is_set(r: Self) -> bool { r.is_set })]
#[flux_rs::assoc(fn rnum(r: Self) -> int { r.rnum })]
#[flux_rs::assoc(fn perms(r: Self) -> Permissions { r.perms })]
// #[flux_rs::assoc(fn region_can_access(r: Self, start: int, end: int, perms: Permissions) -> bool {
//     r.is_set && 
//     start >= r.start &&
//     end <= r.start + r.size && 
//     r.perms == perms
// })]
// #[flux_rs::assoc(fn region_cant_access_at_all(r: Self, start: int, end: int) -> bool {
//     !r.is_set || 
//     !(r.start < start && start < r.start + r.size)
// })]
#[flux_rs::assoc(fn overlaps(region1: Self, region2: Self) -> bool {
    false
})]
impl RegionDescriptor for MpuRegionDefault {
    #[flux_rs::sig(fn (rnum: usize) -> Self {r: !<Self as RegionDescriptor>::is_set(r) && <Self as RegionDescriptor>::rnum(r) == rnum})]
    fn default(num: usize) -> Self {
        Self {
            start: None,
            size: None,
            region_number: num,
            perms: None,
            _ghost: DefaultGhost::empty(),
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::astart(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn accessible_start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::rstart(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn region_start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{ptr: <Self as RegionDescriptor>::asize(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn accessible_size(&self) -> Option<usize> {
        self.size
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{ptr: <Self as RegionDescriptor>::rsize(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn region_size(&self) -> Option<usize> {
        self.size
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool {
        self.start.is_some()
    }
    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2]) -> bool[<Self as RegionDescriptor>::overlaps(r1, r2)])]
    fn overlaps(&self, _other: &Self) -> bool {
        false
    }

    #[flux_rs::sig(fn (
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<{r. Self[r] | 
        <MpuRegionDefault as RegionDescriptor>::is_set(r) &&
        <MpuRegionDefault as RegionDescriptor>::rnum(r) == region_number &&
        <MpuRegionDefault as RegionDescriptor>::perms(r) == permissions && 
        <MpuRegionDefault as RegionDescriptor>::astart(r) >= available_start &&
        <MpuRegionDefault as RegionDescriptor>::astart(r) == <MpuRegionDefault as RegionDescriptor>::rstart(r) &&
        <MpuRegionDefault as RegionDescriptor>::astart(r) + <MpuRegionDefault as RegionDescriptor>::asize(r) <= available_start + available_size &&
        <MpuRegionDefault as RegionDescriptor>::asize(r) >= region_size
    }>)]
    fn create_bounded_region(
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Self> {
        if region_size > available_size {
            None
        } else {
            Some(MpuRegionDefault {
                start: Some(available_start),
                size: Some(region_size),
                perms: Some(permissions),
                region_number,
                _ghost: DefaultGhost::new(available_start, region_size, permissions),
            })
        }
    }

    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        region_number: usize,
        permissions: Permissions,
    ) -> Option<{r. Self[r] | 
        <MpuRegionDefault as RegionDescriptor>::is_set(r) &&
        <MpuRegionDefault as RegionDescriptor>::rnum(r) == region_number &&
        <MpuRegionDefault as RegionDescriptor>::perms(r) == permissions && 
        <MpuRegionDefault as RegionDescriptor>::perms(r) == permissions &&
        <MpuRegionDefault as RegionDescriptor>::astart(r) == region_start &&
        <MpuRegionDefault as RegionDescriptor>::rstart(r) == region_start &&
        <MpuRegionDefault as RegionDescriptor>::astart(r) + <MpuRegionDefault as RegionDescriptor>::asize(r) <= region_start + available_size &&
        <MpuRegionDefault as RegionDescriptor>::asize(r)  >= region_size
    }>)]
    fn update_region(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        region_number: usize,
        permissions: Permissions,
    ) -> Option<Self> {
        if region_size > available_size {
            None
        } else {
            Some(MpuRegionDefault {
                start: Some(region_start),
                size: Some(region_size),
                perms: Some(permissions),
                region_number,
                _ghost: DefaultGhost::new(region_start, region_size, permissions),
            })
        }
    }

    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize,
            permissions: Permissions,
        ) -> Option<{r. Self[r] | 
                <MpuRegionDefault as RegionDescriptor>::is_set(r) &&
                <MpuRegionDefault as RegionDescriptor>::rnum(r) == region_number &&
                <MpuRegionDefault as RegionDescriptor>::perms(r) == permissions &&
                <MpuRegionDefault as RegionDescriptor>::astart(r) == start &&
                <MpuRegionDefault as RegionDescriptor>::astart(r) + <MpuRegionDefault as RegionDescriptor>::asize(r) == start + size
            }>
    )]
    fn create_exact_region(
        region_number: usize,
        start: FluxPtrU8,
        size: usize,
        permissions: Permissions,
    ) -> Option<Self> {
        Some(MpuRegionDefault {
            start: Some(start),
            size: Some(size),
            perms: Some(permissions),
            region_number,
            _ghost: DefaultGhost::new(start, size, permissions),
        })
    }
}

/// The generic trait that particular memory protection unit implementations
/// need to implement.
///
/// This trait is implements generic MPU functionality that is common across different
/// MPU implementations.
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
    fn enable_app_mpu(&self) -> MpuEnabledCapability;

    /// Disables the MPU for userspace apps.  ///
    /// This function must disable any access control that was previously setup
    /// for an app if it will interfere with the kernel.
    /// This will be called before the kernel starts to execute as on some
    /// platforms the MPU rules apply to privileged code as well, and therefore
    /// some of the MPU configuration must be disabled for the kernel to effectively
    /// manage processes.
    fn disable_app_mpu(&self);

    /// Returns the maximum number of regions supported by the MPU.
    fn number_total_regions(&self) -> usize;

    /// Configures the MPU with the provided region configuration.
    ///
    /// An implementation must ensure that all memory locations not covered by
    /// an allocated region are inaccessible in user mode and accessible in
    /// supervisor mode.
    ///
    /// # Arguments
    ///
    /// - `region`: MPU region to be configured
    fn configure_mpu(&self, regions: &RArray<Self::Region>);

}

// /// Implement default MPU trait for unit.
impl MPU for () {
    type Region = MpuRegionDefault;

    #[flux_rs::sig(fn (self: &Self) -> MpuEnabledCapability)]
    fn enable_app_mpu(&self) -> MpuEnabledCapability {
        MpuEnabledCapability {}
    }

    #[flux_rs::sig(fn (self: &Self))]
    fn disable_app_mpu(&self) {}

    fn number_total_regions(&self) -> usize {
        0
    }

    fn configure_mpu(&self, _config: &RArray<Self::Region>) {}
}
