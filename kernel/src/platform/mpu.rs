// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Interface for configuring the Memory Protection Unit.

use core::fmt::{self, Display};
use flux_support::capability::*;
#[allow(clippy::wildcard_imports)]
use flux_support::*;

flux_rs::defs! {
    fn valid_size(x: int) -> bool {
        0 <= x && x <= u32::MAX
    }
}

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
    pub(crate) fn new(_start: FluxPtrU8, _size: usize, _perms: Permissions) -> Self {
        Self {}
    }

    pub(crate) fn empty() -> Self {
        Self {}
    }
}

/// Null type for the default type of the `MpuConfig` type in an implementation
/// of the `MPU` trait. This custom type allows us to implement `Display` with
/// an empty implementation to meet the constraint on `type MpuConfig`.
#[derive(Clone, Copy)]
#[flux_rs::refined_by(start: int, size: int, perms: Permissions, is_set: bool, rnum: int)]
#[flux_rs::invariant(is_set => (valid_size(size) && valid_size(start + size)))]
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

#[flux_rs::assoc(fn start(r: Self) -> int)]
#[flux_rs::assoc(fn size(r: Self) -> int)]
#[flux_rs::assoc(fn is_set(r: Self) -> bool)]
#[flux_rs::assoc(fn rnum(r: Self) -> int)]
#[flux_rs::assoc(fn perms(r: Self) -> Permissions)]
#[flux_rs::assoc(fn overlaps(r1: Self, start: int, end: int) -> bool)]
#[flux_rs::assoc(final fn region_can_access_exactly(r: Self, start: int, end: int, perms: Permissions) -> bool {
    <Self as RegionDescriptor>::is_set(r) &&
    start == <Self as RegionDescriptor>::start(r) &&
    end == <Self as RegionDescriptor>::start(r) + <Self as RegionDescriptor>::size(r) &&
    perms == <Self as RegionDescriptor>::perms(r)
})]
#[flux_rs::assoc(final fn regions_can_access_exactly(r1: Self, r2: Self, start: int, end: int, perms: Permissions) -> bool {
    <Self as RegionDescriptor>::is_set(r1) &&
    <Self as RegionDescriptor>::perms(r1) == perms &&
    start == <Self as RegionDescriptor>::start(r1) &&
    <Self as RegionDescriptor>::size(r1) > 0 &&
    ((!<Self as RegionDescriptor>::is_set(r2)) => (
        end == <Self as RegionDescriptor>::start(r1) + <Self as RegionDescriptor>::size(r1)
    )) &&
    (<Self as RegionDescriptor>::is_set(r2) => (
        <Self as RegionDescriptor>::size(r2) > 0 &&
        <Self as RegionDescriptor>::start(r1) + <Self as RegionDescriptor>::size(r1) == <Self as RegionDescriptor>::start(r2) &&
        end == <Self as RegionDescriptor>::start(r1) + <Self as RegionDescriptor>::size(r1) + <Self as RegionDescriptor>::size(r2) &&
        <Self as RegionDescriptor>::perms(r2) == perms
    ))
})]
#[flux_rs::assoc(final fn no_region_overlaps_app_block(regions: Map<int, Self>, mem_start: int, mem_end: int) -> bool {
    forall i: int in 2..8 {
        let region = map_select(regions, i);
        !<Self as RegionDescriptor>::overlaps(region, mem_start, mem_end)
    }
})]
pub trait RegionDescriptor: core::marker::Sized {
    #[flux_rs::sig(fn (rnum: usize) -> Self {r: !<Self as RegionDescriptor>::is_set(r) && <Self as RegionDescriptor>::rnum(r) == rnum})]
    fn default(region_num: usize) -> Self;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::start(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn start(&self) -> Option<FluxPtrU8>;

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{sz: <Self as RegionDescriptor>::size(r) == sz && valid_size(sz) && valid_size(<Self as RegionDescriptor>::start(r) + sz)}>[<Self as RegionDescriptor>::is_set(r)])]
    fn size(&self) -> Option<usize>;

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool;

    #[flux_rs::sig(fn (&Self[@r], start: usize, end: usize) -> bool[<Self as RegionDescriptor>::overlaps(r, start, end)])]
    fn overlaps(&self, start: usize, end: usize) -> bool;

    /// Deals with the alignment, size, and other constraints of the specific
    /// MPU to create a new region.
    ///
    /// Returns None if the MPU cannot allocate a region with the passed
    /// constraints
    #[flux_rs::sig(fn (
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>{p:
            <Self as RegionDescriptor>::start(p.fst) >= available_start &&
            ((!<Self as RegionDescriptor>::is_set(p.snd)) =>
                <Self as RegionDescriptor>::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    <Self as RegionDescriptor>::start(p.fst),
                    <Self as RegionDescriptor>::start(p.fst) + <Self as RegionDescriptor>::size(p.fst),
                    permissions
                )
            ) &&
            (<Self as RegionDescriptor>::is_set(p.snd) =>
                <Self as RegionDescriptor>::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    <Self as RegionDescriptor>::start(p.fst),
                    <Self as RegionDescriptor>::start(p.fst) + <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd),
                    permissions
                )
            )
        }> requires valid_size(available_start + available_size) && max_region_number > 0 && max_region_number < 8
    )]
    fn allocate_regions(
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>>;

    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>{p:
        ((!<Self as RegionDescriptor>::is_set(p.snd)) =>
            <Self as RegionDescriptor>::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + <Self as RegionDescriptor>::size(p.fst),
                permissions
            ) &&
            <Self as RegionDescriptor>::size(p.fst) >= region_size
        ) &&
        (<Self as RegionDescriptor>::is_set(p.snd) =>
            <Self as RegionDescriptor>::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd),
                permissions
            ) &&
            <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd) >= region_size
        )
    }> requires valid_size(region_start + available_size) && max_region_number > 0 && max_region_number < 8)]
    fn update_regions(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>>;

    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize,
            permissions: Permissions,
        ) -> Option<Self{r: <Self as RegionDescriptor>::region_can_access_exactly(r, start, start + size, permissions)}>
        requires valid_size(start + size) && region_number < 8
    )]
    fn create_exact_region(
        region_number: usize,
        start: FluxPtrU8,
        size: usize,
        permissions: Permissions,
    ) -> Option<Self>;

    // a lemma to help with safety critical invariants
    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8, perms: Permissions)
        requires <Self as RegionDescriptor>::region_can_access_exactly(r, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r, end, u32::MAX)
    )]
    fn lemma_region_can_access_exactly_implies_no_overlap(
        &self,
        _start: FluxPtrU8,
        _end: FluxPtrU8,
        _perms: Permissions,
    );

    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2], start: FluxPtrU8, end: FluxPtrU8, perms: Permissions)
        requires
            <Self as RegionDescriptor>::regions_can_access_exactly(r1, r2, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r1, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r1, end, u32::MAX) &&
            !<Self as RegionDescriptor>::overlaps(r2, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r2, end, u32::MAX)
    )]
    fn lemma_regions_can_access_exactly_implies_no_overlap(
        _r1: &Self,
        _r2: &Self,
        start: FluxPtrU8,
        end: FluxPtrU8,
        _perms: Permissions,
    );

    #[flux_rs::sig(fn (&Self[@r], access_end: FluxPtrU8, desired_end: FluxPtrU8)
        requires
            !<Self as RegionDescriptor>::overlaps(r, access_end, u32::MAX) &&
            access_end <= desired_end
        ensures !<Self as RegionDescriptor>::overlaps(r, desired_end, u32::MAX)
    )]
    fn lemma_no_overlap_le_addr_implies_no_overlap_addr(
        &self,
        _access_end: FluxPtrU8,
        _desired_end: FluxPtrU8,
    );

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8)
        requires !<Self as RegionDescriptor>::is_set(r)
        ensures !<Self as RegionDescriptor>::overlaps(r, start, end)
    )]
    fn lemma_region_not_set_implies_no_overlap(&self, start: FluxPtrU8, end: FluxPtrU8);

    #[flux_rs::sig(fn (&Self[@r],
            flash_start: FluxPtrU8,
            flash_end: FluxPtrU8,
            mem_start: FluxPtrU8,
            mem_end: FluxPtrU8
        )
        requires
            <Self as RegionDescriptor>::region_can_access_exactly(r, flash_start, flash_end, Permissions { r: true, x: true, w: false })
            &&
            flash_end <= mem_start
        ensures
            !<Self as RegionDescriptor>::overlaps(r, mem_start, mem_end)

    )]
    fn lemma_region_can_access_flash_implies_no_app_block_overlaps(
        &self,
        flash_start: FluxPtrU8,
        flash_end: FluxPtrU8,
        mem_start: FluxPtrU8,
        mem_end: FluxPtrU8,
    );
}

#[flux_rs::assoc(fn start(r: Self) -> int { r.start })]
#[flux_rs::assoc(fn size(r: Self) -> int { r.size })]
#[flux_rs::assoc(fn is_set(r: Self) -> bool { r.is_set })]
#[flux_rs::assoc(fn rnum(r: Self) -> int { r.rnum })]
#[flux_rs::assoc(fn perms(r: Self) -> Permissions { r.perms })]
#[flux_rs::assoc(fn overlaps(region1: Self, start: int, end: int) -> bool {
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

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::start(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{ptr: <Self as RegionDescriptor>::size(r) == ptr && valid_size(ptr) && valid_size(<Self as RegionDescriptor>::start(r) + ptr) }>[<Self as RegionDescriptor>::is_set(r)])]
    fn size(&self) -> Option<usize> {
        // TODO:RJ:YUCK
        match self.size {
            None => None,
            Some(sz) => Some(sz),
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool {
        self.start.is_some()
    }
    #[flux_rs::sig(fn (&Self[@r1], start: usize, end: usize) -> bool[<Self as RegionDescriptor>::overlaps(r1, start, end)])]
    fn overlaps(&self, _start: usize, _end: usize) -> bool {
        false
    }

    #[flux_rs::sig(fn (
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize{valid_size(available_start + available_size)},
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>{p:
            <Self as RegionDescriptor>::start(p.fst) >= available_start &&
            valid_size(<MpuRegionDefault as RegionDescriptor>::start(p.fst) + <MpuRegionDefault as RegionDescriptor>::size(p.fst)) &&
            ((!<Self as RegionDescriptor>::is_set(p.snd)) =>
                <Self as RegionDescriptor>::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    <Self as RegionDescriptor>::start(p.fst),
                    <Self as RegionDescriptor>::start(p.fst) + <Self as RegionDescriptor>::size(p.fst),
                    permissions
                )
            ) &&
            (<Self as RegionDescriptor>::is_set(p.snd) =>
                <Self as RegionDescriptor>::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    <Self as RegionDescriptor>::start(p.fst),
                    <Self as RegionDescriptor>::start(p.fst) + <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd),
                    permissions
                )
            )
        }> requires max_region_number > 0 && max_region_number < 8)]
    fn allocate_regions(
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>> {
        if region_size > available_size || region_size == 0 {
            None
        } else {
            Some(Pair {
                fst: MpuRegionDefault {
                    start: Some(available_start),
                    size: Some(region_size),
                    perms: Some(permissions),
                    region_number: max_region_number - 1,
                    _ghost: DefaultGhost::new(available_start, region_size, permissions),
                },
                snd: RegionDescriptor::default(max_region_number),
            })
        }
    }

    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize{valid_size(region_start + available_size)},
        region_size: usize,
        max_region_number: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>{p:
        valid_size(<MpuRegionDefault as RegionDescriptor>::start(p.fst) + <MpuRegionDefault as RegionDescriptor>::size(p.fst)) &&
        ((!<Self as RegionDescriptor>::is_set(p.snd)) =>
            <Self as RegionDescriptor>::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + <Self as RegionDescriptor>::size(p.fst),
                permissions
            ) &&
            <Self as RegionDescriptor>::size(p.fst) >= region_size
        ) &&
        (<Self as RegionDescriptor>::is_set(p.snd) =>
            <Self as RegionDescriptor>::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd),
                permissions
            ) &&
            <Self as RegionDescriptor>::size(p.fst) + <Self as RegionDescriptor>::size(p.snd) >= region_size
        )
    }> requires max_region_number > 0 && max_region_number < 8)]
    fn update_regions(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: Permissions,
    ) -> Option<Pair<Self, Self>> {
        if region_size > available_size || region_size == 0 {
            None
        } else {
            Some(Pair {
                fst: MpuRegionDefault {
                    start: Some(region_start),
                    size: Some(region_size),
                    perms: Some(permissions),
                    region_number: max_region_number - 1,
                    _ghost: DefaultGhost::new(region_start, region_size, permissions),
                },
                snd: RegionDescriptor::default(max_region_number),
            })
        }
    }

    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize{valid_size(start + size)},
            permissions: Permissions,
        ) -> Option<Self{r: <Self as RegionDescriptor>::region_can_access_exactly(r, start, start + size, permissions)}>
        requires region_number < 8
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

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8, perms: Permissions)
        requires <Self as RegionDescriptor>::region_can_access_exactly(r, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r, end, u32::MAX)
    )]
    fn lemma_region_can_access_exactly_implies_no_overlap(
        &self,
        _start: FluxPtrU8,
        _end: FluxPtrU8,
        _perms: Permissions,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2], start: FluxPtrU8, end: FluxPtrU8, perms: Permissions)
        requires <Self as RegionDescriptor>::regions_can_access_exactly(r1, r2, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r1, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r1, end, u32::MAX) &&
            !<Self as RegionDescriptor>::overlaps(r2, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r2, end, u32::MAX)
    )]
    fn lemma_regions_can_access_exactly_implies_no_overlap(
        _r1: &Self,
        _r2: &Self,
        _start: FluxPtrU8,
        _end: FluxPtrU8,
        _perms: Permissions,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r], access_end: FluxPtrU8, desired_end: FluxPtrU8)
        requires
            !<Self as RegionDescriptor>::overlaps(r, access_end, u32::MAX) &&
            access_end <= desired_end
        ensures !<Self as RegionDescriptor>::overlaps(r, desired_end, u32::MAX)
    )]
    fn lemma_no_overlap_le_addr_implies_no_overlap_addr(
        &self,
        _access_end: FluxPtrU8,
        _desired_end: FluxPtrU8,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8)
        requires !<Self as RegionDescriptor>::is_set(r)
        ensures !<Self as RegionDescriptor>::overlaps(r, start, end)
    )]
    fn lemma_region_not_set_implies_no_overlap(&self, _start: FluxPtrU8, _end: FluxPtrU8) {}

    #[flux_rs::sig(fn (&Self[@r],
            flash_start: FluxPtrU8,
            flash_end: FluxPtrU8,
            mem_start: FluxPtrU8,
            mem_end: FluxPtrU8
        )
        requires
            <Self as RegionDescriptor>::region_can_access_exactly(r, flash_start, flash_end, Permissions { r: true, x: true, w: false })
            &&
            flash_end <= mem_start
        ensures
            !<Self as RegionDescriptor>::overlaps(r, mem_start, mem_end)

    )]
    fn lemma_region_can_access_flash_implies_no_app_block_overlaps(
        &self,
        _flash_start: FluxPtrU8,
        _flash_end: FluxPtrU8,
        _mem_start: FluxPtrU8,
        _mem_end: FluxPtrU8,
    ) {
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
    fn configure_mpu(&self, regions: &RArray<Self::Region>, id: usize);
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

    fn configure_mpu(&self, _config: &RArray<Self::Region>, id: usize) {}
}
