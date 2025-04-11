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
use kernel::utilities::StaticRef;

use flux_support::register_bitfields;
use flux_support::*;
use kernel::platform::mpu;
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::math;
use kernel::utilities::registers::interfaces::{Readable, Writeable};
use kernel::utilities::registers::{FieldValue, ReadOnly, ReadWrite};

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

register_bitfields![u32,
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

    RegionAttributes [
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
pub struct MPU<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> {
    /// MMIO reference to MPU registers.
    registers: StaticRef<MpuRegisters>,
    /// Monotonically increasing counter for allocated regions, used
    /// to assign unique IDs to `CortexMConfig` instances.
    config_count: Cell<NonZeroUsize>,
    /// Optimization logic. This is used to indicate which application the MPU
    /// is currently configured for so that the MPU can skip updating when the
    /// kernel returns to the same app.
    hardware_is_configured_for: OptionalCell<NonZeroUsize>,
}

impl<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> MPU<NUM_REGIONS, MIN_REGION_SIZE> {
    pub const unsafe fn new() -> Self {
        Self {
            registers: MPU_BASE_ADDRESS,
            config_count: Cell::new(NonZeroUsize::MIN),
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
            let start = location.accessible_start.as_usize();
            write!(
                f,
                "\
                    \r\n  Region: [{:#010X}:{:#010X}], length: {} bytes; ({:#x})",
                start,
                start + location.accessible_size,
                location.accessible_size,
                // access_str,
                access_bits,
            )?;
            let subregion_bits = self.attributes().read(RegionAttributes::SRD());
            let subregion_size = location.accessible_size / 8; // VTock BUG : This is wrong - cannot use logical size to compute the subregion size
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
    #[field(usize[asize])]
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
#[flux_rs::refined_by(astart: int, asize: int, rstart: int, rsize: int, perms: mpu::Permissions)]
struct GhostRegionState {}

impl GhostRegionState {
    // trusted intializer for ghost state stuff
    #[flux_rs::trusted]
    #[flux_rs::sig(fn (
        FluxPtrU8[@astart],
        usize[@asize],
        FluxPtrU8[@rstart],
        usize[@rsize],
        mpu::Permissions[@perms]
    ) -> GhostRegionState[astart, asize, rstart, rsize, perms]
    )]
    fn set(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        permissions: mpu::Permissions,
    ) -> Self {
        Self {}
    }

    #[flux_rs::trusted]
    #[flux_rs::sig(fn () -> GhostRegionState)]
    fn unset() -> Self {
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
    astart: int, // accessible start
    asize: int, // accessible size
    rstart: int,
    rsize: int,
    perms: mpu::Permissions
)]
pub struct CortexMRegion {
    #[field(Option<{l. CortexMLocation[l] | l.astart == astart && l.asize == asize && l.rstart == rstart && l.rsize == rsize }>[set])]
    location: Option<CortexMLocation>, // actually accessible start and size
    #[field(usize[region_no])]
    region_number: usize,
    #[field({FieldValueU32<RegionBaseAddress::Register>[rbar] | set => region(value(rbar)) == bv32(region_no)})]
    base_address: FieldValueU32<RegionBaseAddress::Register>,
    #[field({FieldValueU32<RegionAttributes::Register>[rasr] | (set => can_access_exactly(rasr, rbar, astart, asize, perms)) && (!set => !region_enable(value(rasr)))})]
    attributes: FieldValueU32<RegionAttributes::Register>,
    #[field(GhostRegionState[astart, asize, rstart, rsize, perms])]
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

impl mpu::RegionDescriptor for CortexMRegion {
    fn default(region_num: usize) -> Self {
        // TODO: Do better with precondition
        if region_num < 8 {
            Self::empty(region_num)
        } else {
            panic!()
        }
    }

    fn accessible_start(&self) -> Option<FluxPtrU8> {
        Some(self.location?.accessible_start)
    }

    fn region_start(&self) -> Option<FluxPtrU8> {
        Some(self.location?.region_start)
    }

    fn accessible_size(&self) -> Option<usize> {
        Some(self.location?.accessible_size)
    }

    fn region_size(&self) -> Option<usize> {
        Some(self.location?.region_size)
    }

    fn region_num(&self) -> usize {
        self.region_number
    }

    fn is_set(&self) -> bool {
        self.location.is_some()
    }

    fn overlaps(&self, other: &CortexMRegion) -> bool {
        self.region_overlaps(other)
    }
}

impl CortexMRegion {
    fn new(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        subregions: Option<(usize, usize)>,
        permissions: mpu::Permissions,
    ) -> CortexMRegion {
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

        // Base address register
        let base_address = RegionBaseAddress::ADDR().val((region_start.as_u32()) >> 5)
            + RegionBaseAddress::VALID::UseRBAR()
            + RegionBaseAddress::REGION().val(region_num as u32);

        let size_value = math::log_base_two_u32_usize(region_size) - 1;

        // Attributes register
        let mut attributes = RegionAttributes::ENABLE::SET()
            + RegionAttributes::SIZE().val(size_value)
            + access
            + execute;

        // If using subregions, add a subregion mask. The mask is a 8-bit
        // bitfield where `0` indicates that the corresponding subregion is enabled.
        // To compute the mask, we start with all subregions disabled and enable
        // the ones in the inclusive range [min_subregion, max_subregion].
        if let Some((min_subregion, max_subregion)) = subregions {
            let mask = (min_subregion..=max_subregion).fold(u8::MAX, |res, i| {
                // Enable subregions bit by bit (1 ^ 1 == 0)
                res ^ (1 << i)
            });
            attributes += RegionAttributes::SRD().val(mask as u32);
        }

        Self {
            location: Some(CortexMLocation {
                accessible_start: logical_start,
                accessible_size: logical_size,
                region_start,
                region_size,
            }),
            region_number: region_num,
            base_address,
            attributes,
            ghost_region_state: GhostRegionState::set(
                logical_start,
                logical_size,
                region_start,
                region_size,
                permissions,
            ),
        }
    }

    fn empty(region_num: usize) -> CortexMRegion {
        CortexMRegion {
            location: None,
            region_number: region_num,
            base_address: RegionBaseAddress::VALID::UseRBAR()
                + RegionBaseAddress::REGION().val(region_num as u32),
            attributes: RegionAttributes::ENABLE::CLEAR(),
            ghost_region_state: GhostRegionState::unset(),
        }
    }

    fn location(&self) -> Option<CortexMLocation> {
        self.location
    }

    fn base_address(&self) -> FieldValueU32<RegionBaseAddress::Register> {
        self.base_address
    }

    fn attributes(&self) -> FieldValueU32<RegionAttributes::Register> {
        self.attributes
    }

    fn region_overlaps(&self, other: &CortexMRegion) -> bool {
        if self.location.is_some() && other.location.is_some() {
            let fst_region_loc = self.location.unwrap();
            let snd_region_loc = other.location.unwrap();

            let fst_region_start = fst_region_loc.accessible_start;
            let fst_region_end = fst_region_start.wrapping_add(fst_region_loc.accessible_size);

            let snd_region_start = snd_region_loc.accessible_start;
            let snd_region_end = snd_region_start.wrapping_add(snd_region_loc.accessible_size);

            fst_region_start < snd_region_end && snd_region_start < fst_region_end
        } else {
            false
        }
    }
}

fn next_aligned_power_of_two(po2_aligned_start: usize, min_size: usize) -> Option<usize> {
    // if start is 0 everything aligns
    if po2_aligned_start == 0 {
        let size = min_size.next_power_of_two();
        return Some(size);
    }

    if po2_aligned_start % 2 != 0 {
        return None;
    }

    // Find the largest power of 2 that divides start
    // VTOCK TODO: Should just be usize stuff
    let mut trailing_zeros = po2_aligned_start.trailing_zeros() as usize;
    let largest_pow2_divisor = 1 << trailing_zeros;

    // all powers of two less than largest_pow2_divisors will align the start
    let min_power = min_size.next_power_of_two();
    if min_power <= largest_pow2_divisor && min_power >= 8 {
        Some(min_power)
    } else {
        // in this case such a value doesn't exist
        None
    }
}

impl<const NUM_REGIONS: usize, const MIN_REGION_SIZE: usize> mpu::MPU
    for MPU<NUM_REGIONS, MIN_REGION_SIZE>
{
    type Region = CortexMRegion;

    fn enable_app_mpu(&self) {
        self.registers.ctrl.write(
            (Control::ENABLE::SET() + Control::HFNMIENA::CLEAR() + Control::PRIVDEFENA::SET())
                .into_inner(),
        );
    }

    fn disable_app_mpu(&self) {
        self.registers
            .ctrl
            .write(Control::ENABLE::CLEAR().into_inner());
    }

    fn number_total_regions(&self) -> usize {
        self.registers.mpu_type.read(Type::DREGION().into_inner()) as usize
    }

    fn create_bounded_region(
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: mpu::Permissions,
    ) -> Option<CortexMRegion> {
        // creates a region with region_start and region_end = region_start + region_size within available start + available size
        let mut start = available_start.as_usize();
        let mut size = region_size;

        let overflow_bound = (u32::MAX / 2 + 1) as usize;
        if size == 0 || size > overflow_bound || start > overflow_bound {
            // cannot create such a region
            return None;
        }

        // size must be >= 256 and a power of two for subregions
        size = cmp::max(size, 256);
        size = size.next_power_of_two();

        // region size must be aligned to start
        start += size - (start % size);

        // calculate subregions
        let subregion_size = size / 8;
        let num_subregions_enabled = region_size.div_ceil(subregion_size);

        let subregions_enabled_end = start + num_subregions_enabled * subregion_size;

        // make sure this fits within our available size
        if subregions_enabled_end > available_start.as_usize() + available_size {
            return None;
        }

        // create the region
        Some(CortexMRegion::new(
            FluxPtr::from(start),
            num_subregions_enabled * subregion_size,
            FluxPtr::from(start),
            size,
            region_number,
            Some((0, num_subregions_enabled - 1)),
            permissions,
        ))
    }

    fn update_region(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        region_number: usize,
        permissions: mpu::Permissions,
    ) -> Option<CortexMRegion> {
        let overflow_bound = (u32::MAX / 2 + 1) as usize;
        if region_size == 0
            || region_size > overflow_bound
            || region_start.as_usize() > overflow_bound
        {
            // cannot create such a region
            return None;
        }

        // get the smallest size >= region size which is a power of two and aligned to the start
        let min_region_size = flux_support::max_usize(256, region_size);
        let mut underlying_region_size =
            next_aligned_power_of_two(region_start.as_usize(), min_region_size)?;

        if underlying_region_size > available_size
            || underlying_region_size > (u32::MAX / 2 + 1) as usize
        {
            return None;
        }

        // calculate subreigons
        let subregion_size = underlying_region_size / 8;

        let num_subregions_enabled = region_size.div_ceil(subregion_size);

        let subregions_enabled_end =
            region_start.as_usize() + num_subregions_enabled * subregion_size;

        // create the region
        Some(CortexMRegion::new(
            region_start,
            num_subregions_enabled * subregion_size,
            region_start,
            underlying_region_size,
            region_number,
            Some((0, num_subregions_enabled - 1)),
            permissions,
        ))
    }

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

        if start.as_usize() % size == 0 {
            // we can just create a region
            Some(CortexMRegion::new(
                start,
                size,
                start,
                size,
                region_number,
                None,
                permissions,
            ))
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

            // calculate subreigons
            let subregion_size = underlying_region_size / 8;

            // if the size isn't aligned to the subregion size we have a problem
            // since that means we cannot divide the requested size into an appropriate
            // number of subregions
            if size % subregion_size == 0 {
                return None;
            }

            let num_subregions_enabled = size / subregion_size;

            Some(CortexMRegion::new(
                start,
                size,
                FluxPtr::from(underlying_region_start),
                underlying_region_size,
                region_number,
                Some((0, num_subregions_enabled - 1)),
                permissions,
            ))
        }
    }

    fn configure_mpu(&self, config: &[CortexMRegion; 8]) {
        for region in config.iter() {
            self.registers
                .rbar
                .write(region.base_address().into_inner());
            self.registers.rasr.write(region.attributes().into_inner());
        }
        // cannot have unused regions
        if NUM_REGIONS > 8 {
            for i in 8..NUM_REGIONS {
                let region = CortexMRegion::empty(i);
                self.registers
                    .rbar
                    .write(region.base_address().into_inner());
                self.registers.rasr.write(region.attributes().into_inner());
            }
        }
    }
}
