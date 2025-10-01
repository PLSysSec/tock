#![allow(unused)]
// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

//! Implementation of the memory protection unit for the Cortex-M0+, Cortex-M3,
//! Cortex-M4, and Cortex-M7
use core::cell::Cell;
use core::cmp;
use core::fmt;
use core::num::NonZeroUsize;
use flux_support::capability::MpuEnabledCapability;
use kernel::utilities::StaticRef;

use crate::tcb::math::*;
use crate::tcb::theorems::*;
use flux_support::register_bitfields_u32;
use flux_support::*;
use kernel::platform::mpu::{self, RegionDescriptor};
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::math;
use kernel::utilities::registers::interfaces::{Readable, Writeable};
use kernel::utilities::registers::{FieldValue, ReadOnly, ReadWrite};

extern crate flux_core;
/// MPU Registers for the Cortex-M3, Cortex-M4 and Cortex-M7 families
/// Described in section 4.5 of
/// <http://infocenter.arm.com/help/topic/com.arm.doc.dui0553a/DUI0553A_cortex_m4_dgug.pdf>
#[repr(C)]
struct MpuRegisters {
    /// Indicates whether the MPU is present and, if so, how many regions it
    /// supports.
    pub mpu_type: ReadOnly<u32, Type::Register>,

    /// The control register:
    ///   * Enables the MPU (bit 0).
    ///   * Enables MPU in hard-fault, non-maskable interrupt (NMI).
    ///   * Enables the default memory map background region in privileged mode.
    pub ctrl: ReadWrite<u32, Control::Register>,

    /// Selects the region number (zero-indexed) referenced by the region base
    /// address and region attribute and size registers.
    pub rnr: ReadWrite<u32, RegionNumber::Register>,

    /// Defines the base address of the currently selected MPU region.
    pub rbar: ReadWrite<u32, RegionBaseAddress::Register>,

    /// Defines the region size and memory attributes of the selected MPU
    /// region. The bits are defined as in 4.5.5 of the Cortex-M4 user guide.
    pub rasr: ReadWrite<u32, RegionAttributes::Register>,
}

register_bitfields_u32![u32,
    Type [
        /// The number of MPU instructions regions supported. Always reads 0.
        IREGION OFFSET(16) NUMBITS(8) [],
        /// The number of data regions supported. If this field reads-as-zero the
        /// processor does not implement an MPU
        DREGION OFFSET(8) NUMBITS(8) [],
        /// Indicates whether the processor support unified (0) or separate
        /// (1) instruction and data regions. Always reads 0 on the
        /// Cortex-M4.
        SEPARATE OFFSET(0) NUMBITS(1) []
    ],

    Control [
        /// Enables privileged software access to the default
        /// memory map
        PRIVDEFENA OFFSET(2) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],
        /// Enables the operation of MPU during hard fault, NMI,
        /// and FAULTMASK handlers
        HFNMIENA OFFSET(1) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],
        /// Enables the MPU
        ENABLE OFFSET(0) NUMBITS(1) [
            Disable = 0,
            Enable = 1
        ]
    ],

    RegionNumber [
        /// Region indicating the MPU region referenced by the MPU_RBAR and
        /// MPU_RASR registers. Range 0-7 corresponding to the MPU regions.FieldValue<
        REGION OFFSET(0) NUMBITS(8) []
    ],

    RegionBaseAddress [
        /// Base address of the currently selected MPU region.
        ADDR OFFSET(5) NUMBITS(27) [],
        /// MPU Region Number valid bit.
        VALID OFFSET(4) NUMBITS(1) [
            /// Use the base address specified in Region Number Register (RNR)
            UseRNR = 0,
            /// Use the value of the REGION field in this register (RBAR)
            UseRBAR = 1
        ],
        /// Specifies which MPU region to set if VALID is set to 1.
        REGION OFFSET(0) NUMBITS(4) []
    ],

    pub RegionAttributes [
        /// Enables instruction fetches/execute permission
        XN OFFSET(28) NUMBITS(1) [
            Enable = 0,
            Disable = 1
        ],
        /// Defines access permissions
        AP OFFSET(24) NUMBITS(3) [
            //                                 Privileged  Unprivileged
            //                                 Access      Access
            NoAccess = 0b000,               // --          --
            PrivilegedOnly = 0b001,         // RW          --
            UnprivilegedReadOnly = 0b010,   // RW          R-
            ReadWrite = 0b011,              // RW          RW
            Reserved = 0b100,               // undef       undef
            PrivilegedOnlyReadOnly = 0b101, // R-          --
            ReadOnly = 0b110,               // R-          R-
            ReadOnlyAlias = 0b111           // R-          R-
        ],
        /// Subregion disable bits
        SRD OFFSET(8) NUMBITS(8) [],
        /// Specifies the region size, being 2^(SIZE+1) (minimum 3)
        SIZE OFFSET(1) NUMBITS(5) [],
        /// Enables the region
        ENABLE OFFSET(0) NUMBITS(1) []
    ]
];

const MPU_BASE_ADDRESS: StaticRef<MpuRegisters> =
    unsafe { StaticRef::new(0xE000ED90 as *const MpuRegisters) };

/// State related to the real physical MPU.
///
/// There should only be one instantiation of this object as it represents
/// real hardware.
///
#[flux_rs::invariant(NUM_REGIONS == 8 || NUM_REGIONS == 16)]
pub struct MPU<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> {
    /// MMIO reference to MPU registers.
    registers: StaticRef<MpuRegisters>,
    /// Optimization logic. This is used to indicate which application the MPU
    /// is currently configured for so that the MPU can skip updating when the
    /// kernel returns to the same app.
    hardware_is_configured_for: OptionalCell<usize>,
}

impl<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> MPU<NUM_REGIONS, MIN_REGION_SIZE> {
    pub const unsafe fn new() -> Self {
        flux_support::const_assume!(NUM_REGIONS == 8 || NUM_REGIONS == 16);
        Self {
            registers: MPU_BASE_ADDRESS,
            hardware_is_configured_for: OptionalCell::empty(),
        }
    }

    // Function useful for boards where the bootloader sets up some
    // MPU configuration that conflicts with Tock's configuration:
    pub unsafe fn clear_mpu(&self) {
        self.registers
            .ctrl
            .write(Control::ENABLE::CLEAR().into_inner());
    }

    fn is_configured_for(&self, id: usize) -> bool {
        if let Some(last_id) = self.hardware_is_configured_for.get() {
            last_id == id
        } else {
            false
        }
    }
}

/// Per-process struct storing MPU configuration for cortex-m MPUs.
///
/// The cortex-m MPU has eight regions, all of which must be configured (though
/// unused regions may be configured as disabled). This struct caches the result
/// of region configuration calculation.

/// Records the index of the last region used for application RAM and flash memory.
/// Regions 0-APP_MEMORY_REGION_MAX_NUM are used for application RAM and flash. Regions
/// with indices above APP_MEMORY_REGION_MAX_NUM can be used for other MPU
/// needs.
///
/// Note the process heap will be region 0 and possibly region 1. Process flash will be region 2
const APP_MEMORY_REGION_MAX_NUM: usize = 2;
const HEAP_REGION1: usize = 0;
const HEAP_REGION2: usize = 1;
const FLASH_REGION: usize = 2;

impl fmt::Display for CortexMRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\r\n Cortex-M Region")?;
        if let Some(location) = self.location() {
            let access_bits = self.attributes().read(RegionAttributes::AP());
            let start = location.region_start.as_usize();
            write!(
                f,
                "\
                    \r\n  Region: [{:#010X}:{:#010X}], length: {} bytes; ({:#x})",
                start,
                start + location.region_size,
                location.region_size,
                // access_str,
                access_bits,
            )?;
            let subregion_bits = self.attributes().read(RegionAttributes::SRD());
            let subregion_size = location.region_size / 8; // VTock BUG : This is wrong - cannot use logical size to compute the subregion size
            for j in 0..8 {
                write!(
                    f,
                    "\
                        \r\n    Sub-region {}: [{:#010X}:{:#010X}], {}",
                    j,
                    start + j * subregion_size,
                    start + (j + 1) * subregion_size,
                    if (subregion_bits >> j) & 1 == 0 {
                        "Enabled"
                    } else {
                        "Disabled"
                    },
                )?;
            }
        } else {
            write!(f, "\r\n  Region: Unused")?;
        }
        write!(f, "\r\n")
    }
}

#[derive(Copy, Clone)]
#[flux_rs::refined_by(astart: int, asize: int, rstart: int, rsize: int)]
struct CortexMLocation {
    #[field(FluxPtrU8[astart])]
    pub accessible_start: FluxPtrU8,
    #[field({usize[asize] | valid_size(astart + asize) })]
    pub accessible_size: usize,
    #[field(FluxPtrU8[rstart])]
    pub region_start: FluxPtrU8,
    #[field(usize[rsize])]
    pub region_size: usize,
}

// flux tracking the actual region size rather than
// the "logical region"
#[derive(Copy, Clone)]
#[flux_rs::opaque]
#[flux_rs::refined_by(region_no: int, astart: int, asize: int, rstart: int, rsize: int, perms: mpu::Permissions)]
struct GhostRegionState {}

impl GhostRegionState {
    // trusted intializer for ghost state stuff
    #[flux_rs::trusted(reason = "ghost state")]
    #[flux_rs::sig(fn (
        FluxPtrU8[@astart],
        usize[@asize],
        FluxPtrU8[@rstart],
        usize[@rsize],
        usize[@region_num],
        mpu::Permissions[@perms]
    ) -> GhostRegionState[region_num, astart, asize, rstart, rsize, perms]
    )]
    fn set(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        permissions: mpu::Permissions,
    ) -> Self {
        Self {}
    }

    #[flux_rs::trusted(reason = "ghost state")]
    #[flux_rs::sig(fn (
        usize[@region_num]
    ) -> GhostRegionState { r: r.region_no == region_num }
    )]
    fn unset(region_num: usize) -> Self {
        Self {}
    }
}

/// Struct storing configuration for a Cortex-M MPU region.
// if the region is set, the rbar bits encode the accessible start & region_num properly and the rasr bits encode the size and permissions properly
#[derive(Copy, Clone)]
#[flux_rs::refined_by(
    rbar: FieldValueU32,
    rasr: FieldValueU32,
    region_no: int,
    set: bool,
    astart: int,
    asize: int,
    rstart: int,
    rsize: int,
    perms: mpu::Permissions
)]
pub struct CortexMRegion {
    #[field(Option<{l. CortexMLocation[l] | l.astart == astart && l.asize == asize && l.rstart == rstart && l.rsize == rsize }>[set])]
    location: Option<CortexMLocation>,
    #[field({FieldValueU32<RegionBaseAddress::Register>[rbar] |
        rbar_region_number(rbar.value) == bv32(region_no) &&
        rbar_valid_bit_set(rbar.value)
    })]
    base_address: FieldValueU32<RegionBaseAddress::Register>,
    #[field({FieldValueU32<RegionAttributes::Register>[rasr] |
        let first = first_subregion_from_logical(rstart, rsize, astart, asize);
        let last  = last_subregion_from_logical(rstart, rsize, astart, asize);
        let bv_first = bv32(first);
        let bv_last  = bv32(last);
        (set =>
            (
                rbar_region_start(rbar.value) == bv32(rstart) &&
                rasr_region_size(rasr.value) == bv32(rsize) &&
                subregions_enabled_bit_set(rasr.value, bv_first, bv_last) &&
                subregions_disabled_bit_set(rasr.value, bv_first, bv_last) &&
                perms_match_exactly(rasr.value, perms)
            )
        ) &&
        (!set =>
            !rasr_global_region_enabled(rasr.value) &&
            subregions_enabled_exactly(rasr.value, 0, 7)
        )}
    )]
    attributes: FieldValueU32<RegionAttributes::Register>,
    #[field(GhostRegionState[region_no, astart, asize, rstart, rsize, perms])]
    ghost_region_state: GhostRegionState,
}

impl PartialEq<mpu::Region> for CortexMRegion {
    fn eq(&self, other: &mpu::Region) -> bool {
        self.location().map_or(
            false,
            |CortexMLocation {
                 accessible_start: addr,
                 accessible_size: size,
                 ..
             }| { addr == other.start_address() && size == other.size() },
        )
    }
}

#[flux_rs::trusted(reason = "bitwise arith")]
#[flux_rs::sig(fn(num: u32) -> u32{r: (r < 32) && (num > 1 => r > 0) && (pow2(num) => (bv32(num) == exp2(bv32(r))))})]
fn log_base_two(num: u32) -> u32 {
    if num == 0 {
        0
    } else {
        31 - num.leading_zeros()
    }
}

#[flux_rs::trusted(reason = "math support (bitwise arithmetic fact)")]
// VTOCK Note: Realized this only works when enabled_mask is not 0 because
// 0xff ^ 0 == 1 but anything & 0 = 0.
#[flux_rs::sig(fn ({usize[@fsr] | fsr <= lsr}, {usize[@lsr] | lsr < 8}) -> u8{r:
    let mask = enabled_srd_mask(bv32(fsr), bv32(lsr));
    if mask == 0 {
        bv32(r) == mask
    } else {
        bv32(r) == bv_xor(0xff, mask)
    }
})]
fn subregion_mask(min_subregion: usize, max_subregion: usize) -> u8 {
    let enabled_mask = ((1 << (max_subregion - min_subregion + 1)) - 1) << min_subregion;
    if enabled_mask == 0 {
        enabled_mask
    } else {
        u8::MAX ^ enabled_mask
    }
}

#[flux_rs::sig(
    fn (po2_aligned_start: usize{valid_size(po2_aligned_start)}, min_size: usize) -> Option<usize{size:
        size >= min_size && pow2(size) && aligned(po2_aligned_start, size) && octet(size) && half_max(size)
    }>
    requires
        half_max(min_size) &&
        min_size >= 256
)]
// Should only be called with a start that aligns to a po2
fn next_aligned_power_of_two(po2_aligned_start: usize, min_size: usize) -> Option<usize> {
    // if start is 0 everything aligns
    if po2_aligned_start == 0 {
        let size = min_size.next_power_of_two();
        theorem_aligned0(po2_aligned_start, size);
        theorem_pow2_octet(size);
        return Some(size);
    }

    if !is_aligned(po2_aligned_start, 2) {
        return None;
    }

    // Find the largest power of 2 that divides start
    // VTOCK TODO: Should just be usize stuff
    let mut trailing_zeros = po2_aligned_start.trailing_zeros() as usize;
    let largest_pow2_divisor = power_of_two(usize_to_u32(trailing_zeros));
    theorem_to_pow2_is_pow2(trailing_zeros);
    theorem_to_pow2_gt1(trailing_zeros);

    // all powers of two less than largest_pow2_divisors will align the start
    let min_power = min_size.next_power_of_two();
    if min_power <= largest_pow2_divisor && min_power >= 8 {
        theorem_pow2_octet(min_power);
        theorem_pow2_le_aligned(po2_aligned_start, largest_pow2_divisor, min_power);
        Some(min_power)
    } else {
        // in this case such a value doesn't exist
        None
    }
}

#[flux_rs::assoc(fn start(r: Self) -> int { r.astart })]
#[flux_rs::assoc(fn size(r: Self) -> int { r.asize })]
#[flux_rs::assoc(fn is_set(r: Self) -> bool { r.set })]
#[flux_rs::assoc(fn rnum(r: Self) -> int { r.region_no })]
#[flux_rs::assoc(fn perms(r: Self) -> mpu::Permissions { r.perms })]
#[flux_rs::assoc(fn overlaps(region1: Self, start: int, end: int) -> bool { region_overlaps(region1, start, end)})]
impl mpu::RegionDescriptor for CortexMRegion {
    #[flux_rs::sig(fn (rnum: usize) -> Self {r: !Self::is_set(r) && Self::rnum(r) == rnum})]
    fn default(region_num: usize) -> Self {
        // TODO: Do better with precondition
        if region_num < 8 {
            Self::empty(region_num)
        } else {
            panic!()
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: Self::start(r) == ptr}>[Self::is_set(r)])]
    fn start(&self) -> Option<FluxPtrU8> {
        match self.location {
            Some(loc) => Some(loc.accessible_start),
            None => None,
        }
    }

    #[flux_rs::reveal(valid_size)]
    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{sz: Self::size(r) == sz && valid_size(sz) && valid_size(Self::start(r) + sz)}>[Self::is_set(r)])]
    fn size(&self) -> Option<usize> {
        match self.location {
            Some(loc) => Some(loc.accessible_size),
            None => None,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[Self::is_set(r)])]
    fn is_set(&self) -> bool {
        self.location.is_some()
    }

    #[flux_rs::sig(fn (&Self[@r], start: usize, end: usize) -> bool[Self::overlaps(r, start, end)])]
    fn overlaps(&self, start: usize, end: usize) -> bool {
        self.region_overlaps(start, end)
    }

    #[flux_rs::reveal(first_subregion_from_logical, last_subregion_from_logical)]
    #[flux_rs::sig(fn (
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<Self, Self>{p:
            Self::start(p.fst) >= available_start &&
            ((!Self::is_set(p.snd)) =>
                Self::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    Self::start(p.fst),
                    Self::start(p.fst) + Self::size(p.fst),
                    permissions
                )
            ) &&
            (Self::is_set(p.snd) =>
                Self::regions_can_access_exactly(
                    p.fst,
                    p.snd,
                    Self::start(p.fst),
                    Self::start(p.fst) + Self::size(p.fst) + Self::size(p.snd),
                    permissions
                )
            )
        }> requires max_region_number > 0 && max_region_number < 8
    )]
    fn allocate_regions(
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        total_size: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<CortexMRegion, CortexMRegion>> {
        // creates 2 regions with region_start and region_end = region_start + region_size within available start + available size

        let mut start = available_start.as_usize();
        let mut size = total_size;

        let overflow_bound = (u32::MAX / 2 + 1) as usize;
        if size == 0 || size > overflow_bound || start > overflow_bound {
            // cannot create such a region
            return None;
        }

        // size must be >= 256 and a power of two for subregions
        size = flux_support::max_usize(size, 512);

        size = size.next_power_of_two();

        theorem_pow2_div2_pow2(size);
        theorem_div2_pow2(size);
        let region_size = size / 2;
        flux_rs::assert(region_size * 2 == size);

        // region size must be aligned to start
        start = align(start, region_size);

        theorem_pow2_octet(region_size);
        theorem_div_octet(region_size);

        // calculate subregions
        let subregion_size = region_size / 8;

        let num_subregions_enabled = total_size.div_ceil(subregion_size);
        let subregions_enabled_end = start + num_subregions_enabled * subregion_size;

        // make sure this fits within our available size
        if subregions_enabled_end > available_start.as_usize() + available_size {
            return None;
        }

        let num_subregions0 = min_usize(num_subregions_enabled, 8);
        let num_subregions1 = num_subregions_enabled.saturating_sub(8);

        let snd_region = if num_subregions1 == 0 {
            mpu::RegionDescriptor::default(max_region_number)
        } else {
            theorem_aligned_plus_aligned_to_is_aligned(start, region_size);
            CortexMRegion::new_with_srd(
                FluxPtr::from(start + region_size),
                num_subregions1 * subregion_size,
                FluxPtr::from(start + region_size),
                region_size,
                max_region_number,
                0,
                num_subregions1 - 1,
                permissions,
            )?
        };

        Some(Pair {
            fst: CortexMRegion::new_with_srd(
                FluxPtr::from(start),
                num_subregions0 * subregion_size,
                FluxPtr::from(start),
                region_size,
                max_region_number - 1,
                0,
                num_subregions0 - 1,
                permissions,
            )?,
            snd: snd_region,
        })
    }

    #[flux_rs::reveal(first_subregion_from_logical, last_subregion_from_logical)]
    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<Self, Self>{p:
        ((!Self::is_set(p.snd)) =>
            Self::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + Self::size(p.fst),
                permissions
            ) &&
            Self::size(p.fst) >= region_size
        ) &&
        (Self::is_set(p.snd) =>
            Self::regions_can_access_exactly(
                p.fst,
                p.snd,
                region_start,
                region_start + Self::size(p.fst) + Self::size(p.snd),
                permissions
            ) &&
            Self::size(p.fst) + Self::size(p.snd) >= region_size
        )
    }> requires max_region_number > 0 && max_region_number < 8)]
    fn update_regions(
        region_start: FluxPtrU8,
        available_size: usize,
        total_size: usize,
        max_region_number: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<CortexMRegion, CortexMRegion>> {
        let overflow_bound = (u32::MAX / 2 + 1) as usize;
        if total_size == 0
            || total_size > overflow_bound
            || region_start.as_usize() > overflow_bound
        {
            // cannot create such a region
            return None;
        }

        // get the smallest size >= region size / 2 which is a power of two and aligned to the start
        let mut min_total_size = flux_support::max_usize(512, total_size);

        if min_total_size % 2 != 0 {
            min_total_size += 1;
        }

        let mut underlying_region_size =
            next_aligned_power_of_two(region_start.as_usize(), min_total_size / 2)?;

        theorem_pow2_octet(underlying_region_size);
        theorem_div_octet(underlying_region_size);

        // calculate subregions
        let subregion_size = underlying_region_size / 8;

        let num_enabled_subregions = total_size.div_ceil(subregion_size);

        let subregions_enabled_end =
            region_start.as_usize() + num_enabled_subregions * subregion_size;

        if subregions_enabled_end > region_start.as_usize() + available_size
            || underlying_region_size > (u32::MAX / 2 + 1) as usize
        {
            return None;
        }

        let num_subregions0 = min_usize(num_enabled_subregions, 8);
        let num_subregions1 = num_enabled_subregions.saturating_sub(8);

        let snd_region = if num_subregions1 == 0 {
            mpu::RegionDescriptor::default(max_region_number)
        } else {
            theorem_aligned_plus_aligned_to_is_aligned(
                region_start.as_usize(),
                underlying_region_size,
            );
            CortexMRegion::new_with_srd(
                FluxPtr::from(region_start.as_usize() + underlying_region_size),
                num_subregions1 * subregion_size,
                FluxPtr::from(region_start.as_usize() + underlying_region_size),
                underlying_region_size,
                max_region_number,
                0,
                num_subregions1 - 1,
                permissions,
            )?
        };

        Some(Pair {
            fst: CortexMRegion::new_with_srd(
                region_start,
                num_subregions0 * subregion_size,
                region_start,
                underlying_region_size,
                max_region_number - 1,
                0,
                num_subregions0 - 1,
                permissions,
            )?,
            snd: snd_region,
        })
    }

    #[flux_rs::reveal(first_subregion_from_logical, last_subregion_from_logical)]
    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize,
            permissions: mpu::Permissions,
        ) -> Option<Self{r: Self::region_can_access_exactly(r, start, start + size, permissions)}>
        requires region_number < 8
    )]
    fn create_exact_region(
        region_number: usize,
        start: FluxPtrU8,
        size: usize,
        permissions: mpu::Permissions,
    ) -> Option<CortexMRegion> {
        // We can't allocate a size that isn't a power of 2 or a size that is < 32 since that will not fit the requirements for a subregion
        if size > (u32::MAX / 2 + 1) as usize || !size.is_power_of_two() || size < 32 {
            return None;
        }

        if is_aligned(start.as_usize(), size) {
            // we can just create a region
            Some(CortexMRegion::new_no_srd(
                start,
                size,
                start,
                size,
                region_number,
                permissions,
            )?)
        } else {
            let min_size = flux_support::max_usize(size, 256);
            let underlying_region_start = start.as_usize();
            // VTOCK: If the start passed is not even, we fail.
            // This is generally a sane thing to do because a start being odd means that
            let underlying_region_size = next_aligned_power_of_two(start.as_usize(), min_size)?;

            // check overflows
            if underlying_region_size > (u32::MAX / 2 + 1) as usize {
                return None;
            }

            theorem_div_octet(underlying_region_size);

            // calculate subreigons
            let subregion_size = underlying_region_size / 8;

            // if the size isn't aligned to the subregion size we have a problem
            // since that means we cannot divide the requested size into an appropriate
            // number of subregions
            if !is_aligned(size, subregion_size) {
                return None;
            }
            theorem_aligned_ge(size, subregion_size);

            let num_subregions_enabled = size / subregion_size;

            if (start.as_usize() > u32::MAX as usize - size) {
                return None;
            }

            Some(CortexMRegion::new_with_srd(
                start,
                size,
                FluxPtr::from(underlying_region_start),
                underlying_region_size,
                region_number,
                0,
                num_subregions_enabled - 1,
                permissions,
            )?)
        }
    }

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8, perms: mpu::Permissions)
        requires
            Self::region_can_access_exactly(r, start, end, perms)
        ensures
            !Self::overlaps(r, 0, start) &&
            !Self::overlaps(r, end, u32::MAX)
    )]
    fn lemma_region_can_access_exactly_implies_no_overlap(
        &self,
        _start: FluxPtrU8,
        _end: FluxPtrU8,
        _perms: mpu::Permissions,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2], start: FluxPtrU8, end: FluxPtrU8, perms: mpu::Permissions)
        requires Self::regions_can_access_exactly(r1, r2, start, end, perms)
        ensures
            !Self::overlaps(r1, 0, start) &&
            !Self::overlaps(r1, end, u32::MAX) &&
            !Self::overlaps(r2, 0, start) &&
            !Self::overlaps(r2, end, u32::MAX)
    )]
    #[flux_rs::trusted_impl]
    fn lemma_regions_can_access_exactly_implies_no_overlap(
        _r1: &Self,
        r2: &Self,
        start: FluxPtrU8,
        end: FluxPtrU8,
        _perms: mpu::Permissions,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r], access_end: FluxPtrU8, desired_end: FluxPtrU8)
        requires
            !Self::overlaps(r, access_end, u32::MAX) &&
            access_end <= desired_end
        ensures !Self::overlaps(r, desired_end, u32::MAX)
    )]
    fn lemma_no_overlap_le_addr_implies_no_overlap_addr(
        &self,
        _access_end: FluxPtrU8,
        _desired_end: FluxPtrU8,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8)
        requires !Self::is_set(r)
        ensures !Self::overlaps(r, start, end)
    )]
    fn lemma_region_not_set_implies_no_overlap(&self, _start: FluxPtrU8, _end: FluxPtrU8) {}

    #[flux_rs::sig(fn (&Self[@r],
            flash_start: FluxPtrU8,
            flash_end: FluxPtrU8,
            mem_start: FluxPtrU8,
            mem_end: FluxPtrU8
        )
        requires
            Self::region_can_access_exactly(r, flash_start, flash_end, mpu::Permissions { r: true, x: true, w: false })
            &&
            flash_end <= mem_start
        ensures
            !Self::overlaps(r, mem_start, mem_end)

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

impl CortexMRegion {
    #[flux_rs::reveal(
        rbar_region_number,
        rbar_region_start,
        rbar_valid_bit_set,
        least_five_bits
    )]
    #[flux_rs::sig(fn (region_start: FluxPtrU8, region_num: usize, region_size: usize) -> FieldValueU32<RegionBaseAddress::Register>{rbar:
        rbar_region_number(rbar.value) == bv32(region_num) &&
        rbar_region_start(rbar.value) == bv32(region_start) &&
        rbar_valid_bit_set(rbar.value)
    }
    requires
        region_num < 8 &&
        region_size >= 32 && pow2(region_size) && aligned(region_start, region_size)
    )]
    fn base_address_register(
        region_start: FluxPtrU8,
        region_num: usize,
        region_size: usize,
    ) -> FieldValueU32<RegionBaseAddress::Register> {
        theorem_aligned_value_ge32_lowest_five_bits0(region_start.as_usize(), region_size);
        let shifted_val = region_start_rs32(region_start);
        RegionBaseAddress::ADDR().val(shifted_val)
            + RegionBaseAddress::VALID::UseRBAR()
            + RegionBaseAddress::REGION().val(usize_to_u32(region_num))
    }

    #[flux_rs::reveal(
        subregions_enabled_bit_set,
        subregions_disabled_bit_set,
        octet,
        first_subregion_from_logical,
        last_subregion_from_logical
    )]
    #[flux_rs::sig(
        fn (region_size: usize, permissions: mpu::Permissions) -> FieldValueU32<RegionAttributes::Register>{rasr:
            rasr_global_region_enabled(rasr.value) &&
            rasr_region_size(rasr.value) == bv32(region_size) &&
            perms_match_exactly(rasr.value, permissions) &&
            subregions_enabled_exactly(rasr.value, 0, 7)
        }
        requires pow2(region_size) && octet(region_size) && 32 <= region_size && half_max(region_size)
    )]
    fn attributes_register_no_srd(
        region_size: usize,
        permissions: mpu::Permissions,
    ) -> FieldValueU32<RegionAttributes::Register> {
        // Determine access and execute permissions
        let (access, execute) = match permissions {
            mpu::Permissions::ReadWriteExecute => (
                RegionAttributes::AP::ReadWrite(),
                RegionAttributes::XN::Enable(),
            ),
            mpu::Permissions::ReadWriteOnly => (
                RegionAttributes::AP::ReadWrite(),
                RegionAttributes::XN::Disable(),
            ),
            mpu::Permissions::ReadExecuteOnly => (
                RegionAttributes::AP::UnprivilegedReadOnly(),
                RegionAttributes::XN::Enable(),
            ),
            mpu::Permissions::ReadOnly => (
                RegionAttributes::AP::UnprivilegedReadOnly(),
                RegionAttributes::XN::Disable(),
            ),
            mpu::Permissions::ExecuteOnly => (
                RegionAttributes::AP::PrivilegedOnly(),
                RegionAttributes::XN::Enable(),
            ),
        };

        let region_size_u32 = usize_to_u32(region_size);
        let size_value = log_base_two(region_size_u32) - 1;
        // Attributes register
        RegionAttributes::ENABLE::SET()
            + RegionAttributes::SIZE().val(size_value)
            + access
            + execute
    }

    #[flux_rs::reveal(
        first_subregion_from_logical,
        last_subregion_from_logical,
        subregions_enabled_bit_set,
        subregions_disabled_bit_set
    )]
    #[flux_rs::sig(
        fn (
            FluxPtrU8[@astart],
            usize[@asize],
            FluxPtrU8[@rstart],
            usize[@rsize],
            usize[@rnum],
            usize[@fsr],
            usize[@lsr],
            mpu::Permissions[@perms]
        ) -> Option<CortexMRegion {r:
                r.astart == astart &&
                r.asize == asize &&
                r.rstart == rstart &&
                r.rsize == rsize &&
                r.region_no == rnum &&
                r.perms == perms &&
                r.set
            }>
        requires
            rnum < 8 &&
            rsize >= 32 &&
            rsize >= 256 &&
            pow2(rsize) &&
            aligned(rstart, rsize) &&
            fsr <= lsr &&
            lsr < 8 &&
            first_subregion_from_logical(rstart, rsize, astart, asize) == fsr &&
            last_subregion_from_logical(rstart, rsize, astart, asize) == lsr &&
            rsize <= u32::MAX / 2 + 1
    )]
    fn new_with_srd(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        fsr: usize,
        lsr: usize,
        permissions: mpu::Permissions,
    ) -> Option<CortexMRegion> {
        if !check_valid_size(logical_start.as_usize(), logical_size) {
            return None;
        }

        theorem_pow2_octet(region_size);
        // Base address register
        let base_address = Self::base_address_register(region_start, region_num, region_size);
        // Attributes register
        let mut attributes = Self::attributes_register_no_srd(region_size, permissions);

        let location = CortexMLocation {
            accessible_start: logical_start,
            accessible_size: logical_size,
            region_start,
            region_size,
        };

        let ghost_region_state = GhostRegionState::set(
            logical_start,
            logical_size,
            region_start,
            region_size,
            region_num,
            permissions,
        );

        // If using subregions, add a subregion mask. The mask is a 8-bit
        // bitfield where `0` indicates that the corresponding subregion is enabled.
        // To compute the mask, we start with all subregions disabled and enable
        // the ones in the inclusive range [min_subregion, max_subregion].
        let mask = subregion_mask(fsr, lsr);
        attributes += RegionAttributes::SRD().val(mask as u32);
        Some(Self {
            location: Some(location),
            base_address,
            attributes,
            ghost_region_state,
        })
    }

    #[flux_rs::sig(
        fn (
            FluxPtrU8[@astart],
            usize[@asize],
            FluxPtrU8[@rstart],
            usize[@rsize],
            usize[@no],
            mpu::Permissions[@perms]
        ) -> Option<CortexMRegion {r:
                r.astart == astart &&
                r.asize == asize &&
                r.rstart == rstart &&
                r.rsize == rsize &&
                r.region_no == no &&
                r.perms == perms &&
                r.set
            }>
        requires
            no < 8 &&
            rsize == asize &&
            rstart == astart &&
            rsize >= 32 &&
            pow2(rsize) &&
            aligned(rstart, rsize) &&
            rsize <= u32::MAX / 2 + 1
    )]
    fn new_no_srd(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        permissions: mpu::Permissions,
    ) -> Option<CortexMRegion> {
        if !check_valid_size(logical_start.as_usize(), logical_size) {
            return None;
        }
        theorem_pow2_octet(region_size);
        // Base address register
        let base_address = Self::base_address_register(region_start, region_num, region_size);
        // Attributes register
        let attributes = Self::attributes_register_no_srd(region_size, permissions);

        theorem_first_subregion_0(region_start, region_size, logical_start, logical_size);
        theorem_last_subregion_7(region_start, region_size, logical_start, logical_size);
        theorem_subregions_disabled_bit_set_0_7(&attributes);

        let location = CortexMLocation {
            accessible_start: logical_start,
            accessible_size: logical_size,
            region_start,
            region_size,
        };

        let ghost_region_state = GhostRegionState::set(
            logical_start,
            logical_size,
            region_start,
            region_size,
            region_num,
            permissions,
        );

        Some(Self {
            location: Some(location),
            base_address,
            attributes,
            ghost_region_state,
        })
    }

    #[flux_rs::reveal(subregions_enabled_bit_set, subregions_disabled_bit_set)]
    #[flux_rs::sig(fn ({usize[@region_no] | region_no < 16}) -> Self {r: r.region_no == region_no && !r.set})]
    pub(crate) fn empty(region_num: usize) -> CortexMRegion {
        let clear = RegionAttributes::ENABLE::CLEAR();
        CortexMRegion {
            location: None,
            base_address: RegionBaseAddress::VALID::UseRBAR()
                + RegionBaseAddress::REGION().val(usize_to_u32(region_num)),
            attributes: RegionAttributes::ENABLE::CLEAR(),
            ghost_region_state: GhostRegionState::unset(region_num),
        }
    }

    #[flux_rs::sig(fn (&CortexMRegion[@r]) -> Option<{l. CortexMLocation[l] | l.astart == r.astart && l.asize == r.asize && l.rstart == r.rstart && l.rsize == r.rsize}>[r.set])]
    fn location(&self) -> Option<CortexMLocation> {
        self.location
    }

    #[flux_rs::sig(fn(&CortexMRegion[@region]) -> FieldValueU32<RegionBaseAddress::Register>[region.rbar])]
    fn base_address(&self) -> FieldValueU32<RegionBaseAddress::Register> {
        self.base_address
    }

    #[flux_rs::sig(fn(&CortexMRegion[@region]) -> FieldValueU32<RegionAttributes::Register>[region.rasr])]
    fn attributes(&self) -> FieldValueU32<RegionAttributes::Register> {
        self.attributes
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    pub(crate) fn is_set(&self) -> bool {
        self.location.is_some()
    }

    #[flux_rs::sig(fn (&Self[@region], start: usize, end: usize) -> bool[region_overlaps(region, start, end)])]
    pub(crate) fn region_overlaps(&self, start: usize, end: usize) -> bool {
        match self.location() {
            Some(region_loc) => {
                let region_start = region_loc.accessible_start.as_usize();
                let region_end = region_start + region_loc.accessible_size;

                region_start < end && start < region_end
            }
            None => false,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtr[r.astart]>[r.set])]
    pub(crate) fn accessible_start(&self) -> Option<FluxPtr> {
        match self.location() {
            Some(l) => Some(l.accessible_start),
            None => None,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize[r.asize]>[r.set])]
    pub(crate) fn accessible_size(&self) -> Option<usize> {
        match self.location() {
            Some(l) => Some(l.accessible_size),
            None => None,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize[r.rsize]>[r.set])]
    pub(crate) fn region_size(&self) -> Option<usize> {
        match self.location() {
            Some(l) => Some(l.region_size),
            None => None,
        }
    }
}

impl<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> mpu::MPU
    for MPU<NUM_REGIONS, MIN_REGION_SIZE>
{
    type Region = CortexMRegion;

    fn enable_app_mpu(&self) -> MpuEnabledCapability {
        self.registers.ctrl.write(
            (Control::ENABLE::SET() + Control::HFNMIENA::CLEAR() + Control::PRIVDEFENA::SET())
                .into_inner(),
        );
        MpuEnabledCapability {}
    }

    fn disable_app_mpu(&self) {
        self.registers
            .ctrl
            .write(Control::ENABLE::CLEAR().into_inner());
    }

    fn number_total_regions(&self) -> usize {
        self.registers.mpu_type.read(Type::DREGION().into_inner()) as usize
    }

    fn configure_mpu(&self, config: &RArray<CortexMRegion>, id: usize, is_dirty: bool) {
        if self.is_configured_for(id) && !is_dirty {
            return; // fastpath - we are already using this config
        }
        for i in 0..NUM_REGIONS {
            if i < 8 {
                let region = config.get(i);
                self.registers
                    .rbar
                    .write(region.base_address().into_inner());
                self.registers.rasr.write(region.attributes().into_inner());
            } else {
                let region = CortexMRegion::empty(i);
                self.registers
                    .rbar
                    .write(region.base_address().into_inner());
                self.registers.rasr.write(region.attributes().into_inner());
            }
        }
        self.hardware_is_configured_for.set(id);
    }
}
