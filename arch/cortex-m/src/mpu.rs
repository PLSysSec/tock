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

use flux_support::register_bitfields;
use flux_support::*;
use kernel::platform::mpu;
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::math;

// VTOCK-TODO: NUM_REGIONS currently fixed to 8. Need to also handle 16
flux_rs::defs! {
    fn bv32(x:int) -> bitvec<32> { bv_int_to_bv32(x) }
    fn bit(reg: bitvec<32>, power_of_two: bitvec<32>) -> bool { reg & power_of_two != 0}
    fn extract(reg: bitvec<32>, mask:int, offset: int) -> bitvec<32> { reg & (bv32(mask) << bv32(offset)) }

    // TODO: auto-generate field definitions somehow
    // TODO: make more type safe with aliases
    // TODO: well-formedness predicates
    // CTRL
    fn enable(reg:bitvec<32>) -> bool { bit(reg, 0x00000001)}
    fn hfnmiena(reg:bitvec<32>) -> bool { bit(reg, 0x00000002)}
    fn privdefena(reg:bitvec<32>) -> bool { bit(reg, 0x00000004)}
    // RNR
    fn num(reg:bitvec<32>) -> bitvec<32> { extract(reg, 0x000000ff, 0) }
    // Rbar
    fn valid(reg:bitvec<32>) -> bool { bit(reg, 0x00000010)}
    fn region(reg:bitvec<32>) -> bitvec<32> { extract(reg, 0x0000000f, 0)}
    fn addr(reg:bitvec<32>) -> bitvec<32> {  extract(reg, 0xffffffe0, 5)}
    // Rasr
    fn xn(reg:bitvec<32>) -> bool { bit(reg, 0x08000000)}
    fn region_enable(reg:bitvec<32>) -> bool { bit(reg, 0x00000001)}
    fn ap(reg:bitvec<32>) -> bitvec<32> { extract(reg, 0x07000000, 24) }
    fn srd(reg:bitvec<32>) -> bitvec<32> { extract(reg, 0x0000ff00, 8) }
    fn size(reg:bitvec<32>) -> bitvec<32> { extract(reg, 0x0000003e, 1) }

    fn value(fv: FieldValueU32) -> bitvec<32> { fv.value}
    fn rbar(region: CortexMRegion) -> bitvec<32> { value(region.rbar) }
    fn rasr(region: CortexMRegion) -> bitvec<32> { value(region.rasr) }


    fn map_set<T>(m: Map<int, T>, k: int, v: T) -> Map<int, T> { map_store(m, k, v) }
    fn map_get<T>(m: Map<int, T>, k:int) -> T { map_select(m, k) }
    fn map_def(v: bitvec<32>) -> Map<int, bitvec<32>> { map_default(v) }


    // fn enabled(mpu: MPU) -> bool { enable(mpu.ctrl)}
    // VTOCK_TODO: simplify
    fn mpu_configured_for(mpu: MPU, config: CortexMConfig) -> bool {
        map_get(mpu.regions, 0) == rbar(map_get(config.regions, 0)) &&
        map_get(mpu.attrs, 0) == rasr(map_get(config.regions, 0)) &&
        map_get(mpu.regions, 1) == rbar(map_get(config.regions, 1)) &&
        map_get(mpu.attrs, 1) == rasr(map_get(config.regions, 1)) &&
        map_get(mpu.regions, 2) == rbar(map_get(config.regions, 2)) &&
        map_get(mpu.attrs, 2) == rasr(map_get(config.regions, 2)) &&
        map_get(mpu.regions, 3) == rbar(map_get(config.regions, 3)) &&
        map_get(mpu.attrs, 3) == rasr(map_get(config.regions, 3)) &&
        map_get(mpu.regions, 4) == rbar(map_get(config.regions, 4)) &&
        map_get(mpu.attrs, 4) == rasr(map_get(config.regions, 4)) &&
        map_get(mpu.regions, 5) == rbar(map_get(config.regions, 5)) &&
        map_get(mpu.attrs, 5) == rasr(map_get(config.regions, 5)) &&
        map_get(mpu.regions, 6) == rbar(map_get(config.regions, 6)) &&
        map_get(mpu.attrs, 6) == rasr(map_get(config.regions, 6)) &&
        map_get(mpu.regions, 7) == rbar(map_get(config.regions, 7)) &&
        map_get(mpu.attrs, 7) == rasr(map_get(config.regions, 7))
    }

    fn contains(rbar: bitvec<32>, rasr: bitvec<32>, ptr: int, sz: int) -> bool {
        (bv32(ptr) >= addr(rbar)) && (bv32(ptr + sz) < addr(rbar) + size(rasr))
    }

    fn subregion_enabled(rasr: bitvec<32>, rbar: bitvec<32>, ptr: int, sz: int) -> bool {
        size(rasr) >= 8 && // must be at least 256 bits
        // {
            // let subregion_size = size(rasr) - 3;
            // let offset = ptr % size(rasr);
            // let subregion_id = (addr(rbar) & size(rasr)) / (size(rasr) - 3);
            bit(srd(rasr), bv_urem(bv32(ptr), size(rasr)) / (size(rasr) - 3))
        // }
    }

    fn can_service(rbar: bitvec<32>, rasr: bitvec<32>, ptr: int, sz: int) -> bool {
        region_enable(rasr) &&
        contains(rbar, rasr, ptr, sz) &&
        subregion_enabled(rasr, rbar, ptr, sz)
    }

    // https://developer.arm.com/documentation/dui0552/a/cortex-m3-peripherals/optional-memory-protection-unit/mpu-access-permission-attributes?lang=en
    fn user_can_read(rasr: bitvec<32>) -> bool {
        ap(rasr) == 2 ||
        ap(rasr) == 3 ||
        ap(rasr) == 6 ||
        ap(rasr) == 7
    }

    // https://developer.arm.com/documentation/dui0552/a/cortex-m3-peripherals/optional-memory-protection-unit/mpu-access-permission-attributes?lang=en
    fn user_can_write(rasr: bitvec<32>) -> bool {
        ap(rasr) == 3
    }

    fn user_access_succeeds(rbar: bitvec<32>, rasr: bitvec<32>, perms: mpu::Permissions) -> bool {
        xn(rasr) => !perms.x &&
        user_can_read(rasr) => perms.r &&
        user_can_write(rasr) => perms.w
    }

    /*

    // Need to verify non-overlapping? or implement last?
    // desugar into 28 line predicate?
    // TODO: verify whole thing, not little toy one
    // Idea: safely overapproximate -- every region that can service an address must satisfy the rules
    // -- is this actually sound?

    forall region in self.regions. last(|r|
        r.can_service(addr, size))) ==>
        user_access_succeeds(region.rbar, region.rasr, perms) // Done
        addr.aligned_to(arch.alignment) &&
        addr.aligned_to(size))
    */

    fn region_can_access(mpu: MPU, addr: int, sz: int, perms: mpu::Permissions, idx: int) -> bool {
        can_service(map_get(mpu.regions, idx), map_get(mpu.attrs, idx), addr, sz) =>
        user_access_succeeds(map_get(mpu.regions, idx), map_get(mpu.attrs, idx), perms)
    }

    fn config_region_can_access(config: CortexMConfig, addr: int, sz: int, perms: mpu::Permissions, idx: int) -> bool {
        can_service(rbar(map_get(config.regions, idx)), rasr(map_get(config.regions, idx)), addr, sz) =>
        user_access_succeeds(rbar(map_get(config.regions, idx)), rasr(map_get(config.regions, idx)), perms)
    }

    fn can_access(mpu: MPU, addr: int, sz: int, perms: mpu::Permissions) -> bool {
        region_can_access(mpu, addr, sz, perms, 0) &&
        region_can_access(mpu, addr, sz, perms, 1) &&
        region_can_access(mpu, addr, sz, perms, 2) &&
        region_can_access(mpu, addr, sz, perms, 3) &&
        region_can_access(mpu, addr, sz, perms, 4) &&
        region_can_access(mpu, addr, sz, perms, 5) &&
        region_can_access(mpu, addr, sz, perms, 6) &&
        region_can_access(mpu, addr, sz, perms, 7)


        // can_service(map_get(mpu.regions, 0), map_get(mpu.attrs, 0), addr, sz) => user_access_succeeds(map_get(mpu.regions, 0), map_get(mpu.attrs, 0), perms)
        // true
    }

    fn config_can_access(config: CortexMConfig, addr: int, sz: int, perms: mpu::Permissions) -> bool {
        config_region_can_access(config, addr, sz, perms, 0) &&
        config_region_can_access(config, addr, sz, perms, 1) &&
        config_region_can_access(config, addr, sz, perms, 2) &&
        config_region_can_access(config, addr, sz, perms, 3) &&
        config_region_can_access(config, addr, sz, perms, 4) &&
        config_region_can_access(config, addr, sz, perms, 5) &&
        config_region_can_access(config, addr, sz, perms, 6) &&
        config_region_can_access(config, addr, sz, perms, 7)
        // true // TODO:
    }

    fn regions_post_allocate_app_memory_region(region0: CortexMRegion, region1: CortexMRegion, base: int, memsz: int, appmsz: int, kernelmsz: int, perms: mpu::Permissions) -> bool {
        // region0 is set
        region0.set == true &&
        // region0 start is the base
        region0.start == base &&
        // region0 size is either the full memory block or half of it
        (region0.size == memsz || region0.size == memsz / 2) &&
        // region 0 first enabled subregion is 0
        region0.first_subregion_no == 0 &&
        // region 0 perms matched the permissions passed
        region0.perms == perms &&
        // if we have to use region 1
        if region1.set == true {
            // region1 start is base + region size
            region1.start == base + region0.size &&
            // region1 size is the same as region0
            region1.size == region0.size &&
            // region1 first enabled sub region is 0
            region1.first_subregion_no == 0 &&
            // region1 last enabled sub region is some arithmetic
            region1.last_subregion_no == (appmsz * 8) / (region1.size + 1) - 8 - 1 &&
            // and therefore region0 last enabled sub region is 7
            region0.last_subregion_no == 7 &&
            // region1 perms matched the permissions passed
            region1.perms == perms &&
            // region1 invariant holds 
            encodes_base(region1.rbar, base + region0.size, region1.region_no) &&
            encodes_attrs(region1.rasr, region1.size, region1.first_subregion_no, region1.last_subregion_no, region1.perms) &&
            // finally - the mem address corresponding to the last subregion of region1 enabled HAS to be greater or equal to the appmsz
            base + (region1.last_subregion_no + 1) * (region1.size / 8) >= appmsz && 
            // AND - the mem address corresponding to the last subregion of region1 HAS to be less than the kernel break
            base + (region1.last_subregion_no + 1) * (region1.size / 8) < base + memsz - kernelmsz
        } else {
            // so we know region 0s last enabled subregion
            // is some arithmetic based on the app break
            region0.last_subregion_no == (appmsz * 8) / (region0.size + 1) - 1 &&
            // finally - the mem address corresponding to the last subregion of region0 enabled HAS to be greater or equal to the appmsz
            base + (region0.last_subregion_no + 1) * (region0.size / 8) >= appmsz &&
            // AND - the mem address corresponding to the last subregion of region0 HAS to be less than the kernel break
            base + (region0.last_subregion_no + 1) * (region0.size / 8) < base + memsz - kernelmsz
        }
        &&
        // region0 invariant holds
        encodes_base(region0.rbar, base, region0.region_no) &&
        encodes_attrs(region0.rasr, region0.size, region0.first_subregion_no, region0.last_subregion_no, region0.perms)
    }

    fn config_post_allocate_app_memory_region(old_config: CortexMConfig, base: int, memsz: int, appmsz: int, kernelmsz: int, perms: mpu::Permissions, new_config: CortexMConfig) -> bool {
        regions_post_allocate_app_memory_region(map_get(new_config, 0), map_get(new_config, 1), base, memsz, appmsz, kernelmsz, perms) &&
        same_config(new_config, old_config, 2) &&
        same_config(new_config, old_config, 3) &&
        same_config(new_config, old_config, 4) &&
        same_config(new_config, old_config, 5) &&
        same_config(new_config, old_config, 6) &&
        same_config(new_config, old_config, 7)
    }

    fn same_config(new_config: CortexMConfig, old_config: CortexMConfig, idx: int) -> bool {
        map_get(new_config, idx) == map_get(old_config, idx)
    }

    fn all_other_regions_post_allocate_region_preserved(old_config: CortexMConfig, new_config: CortexMConfig, region_num: int) -> bool {
        region_num != 0 => same_config(new_config, old_config, 0) 
        &&
        region_num != 1 => same_config(new_config, old_config, 1) 
        &&
        region_num != 2 => same_config(new_config, old_config, 2) 
        &&
        region_num != 3 => same_config(new_config, old_config, 3) 
        &&
        region_num != 4 => same_config(new_config, old_config, 4) 
        &&
        region_num != 5 => same_config(new_config, old_config, 5) 
        &&
        region_num != 6 => same_config(new_config, old_config, 6) 
        &&
        region_num != 7 => same_config(new_config, old_config, 7) 
    }

    fn region_post_allocate_region(new_region: CortexMRegion, region_num: int, base: int, sz: int, perms: mpu::Permissions) -> bool {
        // VTOCK TODO: Talk about the subregions here
        new_region.set &&
        new_region.region_no == region_num &&
        new_region.start == base &&
        new_region.size == sz &&
        new_region.perms == perms &&
        encodes_base(new_region.rbar, base + new_region.size, new_region.region_no) &&
        encodes_attrs(new_region.rasr, new_region.size, new_region.first_subregion_no, new_region.last_subregion_no, new_region.perms)
    }

    fn config_post_allocate_region(old_config: CortexMConfig, new_config: CortexMConfig, region_num: int, base: int, sz: int, perms: mpu::Permissions) -> bool {
        region_post_allocate_region(map_get(new_config, region_num), region_num, base, sz, perms) &&
        all_other_regions_post_allocate_region_preserved(old_config, new_config, region_num)
    }

    fn encodes_base(rbar: FieldValueU32, start: int, region_num: int) -> bool {
        // rbar's address should match
        addr(value(rbar)) == bv32(start) &&
        // the region number should match
        region(value(rbar)) == bv32(region_num)
    }

    fn enabled_srd_mask(first_subregion_no: int, last_subregion_no: int) -> bitvec<32> {
        (bv32(1) << bv32(last_subregion_no - first_subregion_no + 1)) - 1
    }

    fn disabled_srd_mask(last_subregion_no: int) -> bitvec<32> {
        ((bv32(1) << (8 - bv32(last_subregion_no))) - 1) << bv32(last_subregion_no)
    }

    fn subregions_enabled(rasr: bitvec<32>, first_subregion_no: int, last_subregion_no: int) -> bool {
        // Min size = 256
        size(rasr) >= 8 &&
        // Check bits first_subregion..=end_subregion are 0
        srd(rasr) & enabled_srd_mask(first_subregion_no, last_subregion_no) == 0 &&
        // Check bits last_subregion_end..=7 are 1 if there are any bits left
        last_subregion_no < 7 => srd(rasr) & disabled_srd_mask(last_subregion_no) == disabled_srd_mask(last_subregion_no)
    }

    fn perms_match(rasr: bitvec<32>, perms: mpu::Permissions) -> bool {
        perms.r == user_can_read(rasr) &&
        perms.w == user_can_write(rasr) &&
        perms.x == !xn(rasr) 
    }

    fn size_match(rasr_size: bitvec<32>, size: int) -> bool {
        bv32(1) << (rasr_size + 1) == bv32(size)
    }

    fn encodes_attrs(rasr: FieldValueU32, sz: int, first_subregion_no: int, last_subregion_no: int, perms: mpu::Permissions) -> bool {
        // subregions properly set
        subregions_enabled(value(rasr), first_subregion_no, last_subregion_no) &&
        // size should be correct - size encoded as power of two: 2 ^ (size(rasr) + 1) == size
        size_match(size(value(rasr)), sz) &&
        // permissions match
        perms_match(value(rasr), perms) &&
        // global enable bit is set
        region_enable(value(rasr))
    }

}

// VTOCK_TODO: better solution for hardware register spooky-action-at-a-distance
/* VTOCK TODOS
    3. Implement can_service
*/

// VTOCK-TODO: supplementary proof?
#[flux_rs::sig(fn(n: u32{n < 32}) -> usize {r: r > 0 })]
#[flux_rs::trusted]
fn power_of_two(n: u32) -> usize {
    1_usize << n
}

#[flux_rs::opaque]
#[flux_rs::refined_by(regions: Map<int, CortexMRegion>)]
pub struct RegionGhostState {}
impl RegionGhostState {
    #[flux_rs::trusted]
    const fn new() -> Self {
        Self {}
    }
}

#[flux_rs::opaque]
#[flux_rs::refined_by(regions: Map<int, bitvec<32>>, attrs: Map<int, bitvec<32>>)]
pub struct HwGhostState {}
impl HwGhostState {
    #[flux_rs::trusted]
    const fn new() -> Self {
        Self {}
    }
}

/// MPU Registers for the Cortex-M3, Cortex-M4 and Cortex-M7 families
/// Described in section 4.5 of
/// <http://infocenter.arm.com/help/topic/com.arm.doc.dui0553a/DUI0553A_cortex_m4_dgug.pdf>
#[repr(C)]
#[flux_rs::refined_by(ctrl: bitvec<32>, rnr: bitvec<32>, rbar: bitvec<32>, rasr: bitvec<32>, regions: Map<int, bitvec<32>>, attrs: Map<int, bitvec<32>>)]
pub struct MpuRegisters {
    /// Indicates whether the MPU is present and, if so, how many regions it
    /// supports.
    // VTOCK-TODO: this should be read-only
    pub mpu_type: ReadWriteU32<Type::Register>,

    /// The control register:
    ///   * Enables the MPU (bit 0).
    ///   * Enables MPU in hard-fault, non-maskable interrupt (NMI).
    ///   * Enables the default memory map background region in privileged mode.
    #[field(ReadWriteU32<Control::Register>[ctrl])]
    pub ctrl: ReadWriteU32<Control::Register>,

    /// Selects the region number (zero-indexed) referenced by the region base
    /// address and region attribute and size registers.
    #[field(ReadWriteU32<RegionNumber::Register>[rnr])]
    pub rnr: ReadWriteU32<RegionNumber::Register>,

    /// Defines the base address of the currently selected MPU region.
    #[field(ReadWriteU32<RegionBaseAddress::Register>[rbar])]
    pub rbar: ReadWriteU32<RegionBaseAddress::Register>,

    /// Defines the region size and memory attributes of the selected MPU
    /// region. The bits are defined as in 4.5.5 of the Cortex-M4 user guide.
    #[field(ReadWriteU32<RegionAttributes::Register>[rasr])]
    pub rasr: ReadWriteU32<RegionAttributes::Register>,

    #[field(HwGhostState[regions, attrs])]
    hw_state: HwGhostState,
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

// const MPU_BASE_ADDRESS: StaticRef<MpuRegisters> =
//     unsafe { StaticRef::new(0xE000ED90 as *const MpuRegisters) };

/// State related to the real physical MPU.
///
/// There should only be one instantiation of this object as it represents
/// real hardware.
///
#[flux_rs::invariant(MIN_REGION_SIZE > 0 && MIN_REGION_SIZE < 2147483648)]
#[flux_rs::refined_by(ctrl: bitvec<32>, rnr: bitvec<32>, rbar: bitvec<32>, rasr: bitvec<32>, regions: Map<int, bitvec<32>>, attrs: Map<int, bitvec<32>>)]
pub struct MPU<const MIN_REGION_SIZE: usize> {
    /// MMIO reference to MPU registers.
    #[field(MpuRegisters[ctrl, rnr, rbar, rasr, regions, attrs])]
    registers: MpuRegisters,
    /// Monotonically increasing counter for allocated regions, used
    /// to assign unique IDs to `CortexMConfig` instances.
    #[field({Cell<NonZeroUsize> | MIN_REGION_SIZE > 0 && MIN_REGION_SIZE < 2147483648})]
    config_count: Cell<NonZeroUsize>,
    /// Optimization logic. This is used to indicate which application the MPU
    /// is currently configured for so that the MPU can skip updating when the
    /// kernel returns to the same app.
    hardware_is_configured_for: OptionalCell<NonZeroUsize>,
}

impl<const MIN_REGION_SIZE: usize> MPU<MIN_REGION_SIZE> {
    pub const unsafe fn new() -> Self {
        assume(MIN_REGION_SIZE > 0);
        assume(MIN_REGION_SIZE < 2147483648);
        let mpu_addr = 0xE000ED90;
        let mpu_type = ReadWriteU32::new(mpu_addr);
        let ctrl = ReadWriteU32::new(mpu_addr + 4);
        let rnr = ReadWriteU32::new(mpu_addr + 8);
        let rbar = ReadWriteU32::new(mpu_addr + 12);
        let rasr = ReadWriteU32::new(mpu_addr + 16);
        let regs = MpuRegisters {
            mpu_type,
            ctrl,
            rnr,
            rbar,
            rasr,
            hw_state: HwGhostState::new(),
        };

        Self {
            registers: regs,
            config_count: Cell::new(NonZeroUsize::MIN),
            hardware_is_configured_for: OptionalCell::empty(),
        }
    }

    // Function useful for boards where the bootloader sets up some
    // MPU configuration that conflicts with Tock's configuration:
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{mpu: mpu.ctrl & 0x00000001 == 0 })]
    pub unsafe fn clear_mpu(&mut self) {
        self.registers.ctrl.write(Control::ENABLE::CLEAR());
    }

    // VTOCK CODE
    #[flux_rs::trusted]
    #[flux_rs::sig(
        fn(self: &strg Self[@mpu], &CortexMRegion[@addr, @attrs, @loc, @no, @start, @set, @size, @fsr, @lsr, @perms]) ensures
            self: Self[mpu.ctrl, mpu.rnr, addr.value, attrs.value,
                map_store(mpu.regions, no, addr.value),
                map_store(mpu.attrs, no, attrs.value)]
    )]
    fn commit_region(&mut self, region: &CortexMRegion) {
        self.registers.rbar.write(region.base_address());
        self.registers.rasr.write(region.attributes());
    }
}

/// Per-process struct storing MPU configuration for cortex-m MPUs.
///
/// The cortex-m MPU has eight regions, all of which must be configured (though
/// unused regions may be configured as disabled). This struct caches the result
/// of region configuration calculation.

const NUM_REGIONS: usize = 8;

// #[flux_rs::refined_by(regions: Map<int, bitvec<32>>, attrs: Map<int, bitvec<32>>)]
#[flux_rs::refined_by(regions: Map<int, CortexMRegion>)]
pub struct CortexMConfig {
    /// Unique ID for this configuration, assigned from a
    /// monotonically increasing counter in the MPU struct.
    id: NonZeroUsize,
    /// The computed region configuration for this process.
    regions: [CortexMRegion; 8],
    /// Has the configuration changed since the last time the this process
    /// configuration was written to hardware?
    is_dirty: Cell<bool>,

    #[field(RegionGhostState[regions])]
    region_state: RegionGhostState,
}

/// Records the index of the last region used for application RAM memory.
/// Regions 0-APP_MEMORY_REGION_MAX_NUM are used for application RAM. Regions
/// with indices above APP_MEMORY_REGION_MAX_NUM can be used for other MPU
/// needs.
const APP_MEMORY_REGION_MAX_NUM: usize = 1;

impl fmt::Display for CortexMConfig {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "\r\n Cortex-M MPU")?;
        for (i, region) in self.regions_iter().enumerate() {
            if let Some(location) = region.location() {
                let access_bits = region.attributes().read(RegionAttributes::AP());
                let start = location.0.as_usize();
                write!(
                    f,
                    "\
                     \r\n  Region {}: [{:#010X}:{:#010X}], length: {} bytes; ({:#x})",
                    i,
                    start,
                    start + location.1,
                    location.1,
                    // access_str,
                    access_bits,
                )?;
                let subregion_bits = region.attributes().read(RegionAttributes::SRD());
                let subregion_size = location.1 / 8;
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
                write!(f, "\r\n  Region {}: Unused", i)?;
            }
        }
        write!(f, "\r\n")
    }
}

impl CortexMConfig {
    fn id(&self) -> NonZeroUsize {
        self.id
    }

    fn is_dirty(&self) -> bool {
        self.is_dirty.get()
    }

    fn set_dirty(&self, b: bool) {
        self.is_dirty.set(b)
    }

    #[flux_rs::trusted]
    // #[flux_rs::sig(fn(self: &Self, idx: usize, region: CortexMRegion))]
    #[flux_rs::sig(fn(&CortexMConfig[@self], {usize[@idx] | idx < 8}) -> &CortexMRegion{r:
        r.region_no == idx &&
        value(r.rbar) == rbar(map_get(self.regions, idx)) &&
        value(r.rasr) == rasr(map_get(self.regions, idx))
    })]
    fn get_region(&self, idx: usize) -> &CortexMRegion {
        &self.regions[idx]
    }

    // map_set
    #[flux_rs::sig(fn(self: &strg Self[@regions], idx: usize, region: CortexMRegion[@r]) ensures self: Self[map_set(regions, idx, r)])]
    #[flux_rs::trusted] // needs a spec for index
    fn region_set(&mut self, idx: usize, region: CortexMRegion) {
        self.regions[idx] = region
    }

    #[flux_rs::trusted]
    fn regions_iter(&self) -> core::slice::Iter<'_, CortexMRegion> {
        self.regions.iter()
    }

    #[flux_rs::sig(fn(&CortexMConfig[@c]) -> Option<usize{idx: idx > 1 && idx < 8 }>)]
    #[flux_rs::trusted] // need spec for enumerate for this to work
    fn unused_region_number(&self) -> Option<usize> {
        for (number, region) in self.regions_iter().enumerate() {
            if number <= APP_MEMORY_REGION_MAX_NUM {
                continue;
            }
            if let None = region.location() {
                return Some(number);
            }
        }
        None
    }
}

#[derive(Copy, Clone)]
#[flux_rs::refined_by(addr: int, size: int)]
struct CortexMLocation {
    #[field(FluxPtrU8[addr])]
    pub addr: FluxPtrU8,
    #[field({usize[size] | size >= 8})]
    pub size: usize,
}

// flux tracking the actual region size rather than
// the "logical region"
#[derive(Copy, Clone)]
#[flux_rs::opaque]
#[flux_rs::refined_by(region_no: int, set: bool, start: int, size: int, first_subregion_no: int, last_subregion_no: int, perms: mpu::Permissions)]
struct GhostRegionState {}

/// Struct storing configuration for a Cortex-M MPU region.
#[derive(Copy, Clone)]
// invariant says that if the region is set, the rbar bits encode the start & region_num properly and the rasr bits encode the size and permissions properly
#[flux_rs::invariant((set => (encodes_base(rbar, start, region_no) && encodes_attrs(rasr, size, first_subregion_no, last_subregion_no, perms))) && loc == set )]
#[flux_rs::refined_by(rbar: FieldValueU32, rasr: FieldValueU32, loc: bool, region_no: int, set: bool, start: int, size: int, first_subregion_no: int, last_subregion_no: int, perms: mpu::Permissions)]
pub struct CortexMRegion {
    #[field(Option<CortexMLocation>[loc])]
    location: Option<CortexMLocation>,
    #[field({FieldValueU32<RegionBaseAddress::Register>[rbar] | encodes_base(rbar, start, region_no) })]
    base_address: FieldValueU32<RegionBaseAddress::Register>,
    #[field({FieldValueU32<RegionAttributes::Register>[rasr] | encodes_attrs(rasr, size, first_subregion_no, last_subregion_no, perms) })]
    attributes: FieldValueU32<RegionAttributes::Register>,
    // Flux tracking of actual region rather than logical region
    #[field(GhostRegionState[region_no, set, start, size, first_subregion_no, last_subregion_no, perms])]
    ghost_region_state: GhostRegionState,
}

impl PartialEq<mpu::Region> for CortexMRegion {
    fn eq(&self, other: &mpu::Region) -> bool {
        self.location().map_or(false, |(addr, size)| {
            addr == other.start_address() && size == other.size()
        })
    }
}

impl CortexMRegion {

    fn compute_base(region_start: FluxPtrU8, region_num: usize) -> FieldValueU32<RegionBaseAddress::Register> {
        RegionBaseAddress::ADDR().val((region_start.as_u32()) >> 5)
            + RegionBaseAddress::VALID::UseRBAR()
            + RegionBaseAddress::REGION().val(region_num as u32)
    }

    fn compute_attributes(region_size: usize, permissions: mpu::Permissions) -> FieldValueU32<RegionAttributes::Register> {
        assume(region_size > 1 && region_size < (u32::MAX as usize));

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
        let size_value = math::log_base_two_u32_usize(region_size) - 1;

        // Attributes register
        RegionAttributes::ENABLE::SET()
            + RegionAttributes::SIZE().val(size_value)
            + access
            + execute
    }

    #[flux_rs::sig(fn(
        FluxPtrU8,
        usize,
        FluxPtrU8[@rstart],
        usize[@rsize],
        usize[@region_num],
        mpu::Permissions[@perms]
    ) -> Self { r: 
            encodes_base(r.rbar, rstart, region_num) &&
            encodes_attrs(r.rasr, rsize, 0, 7, perms) &&
            r.region_no == region_num &&
            r.set == true &&
            r.start == rstart &&
            r.size == rsize &&
            r.first_subregion_no == 0 &&
            r.last_subregion_no == 7 &&
            r.perms == perms 
        } 
    )]
    fn new_without_subregions(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        permissions: mpu::Permissions,
    ) -> Self {
        assume(region_size > 1 && region_size < (u32::MAX as usize));
        assume(logical_size >= 8);

        // Base address register
        let base_address = Self::compute_base(region_start, region_num);
        let attributes = Self::compute_attributes(region_size, permissions);

        Self::into_region(
            Some(CortexMLocation {
                addr: logical_start,
                size: logical_size,
            }),
            base_address,
            attributes,
            region_num,
            region_start,
            region_size,
            0, // all subregions are enabled
            7, // all subregions are enabled
            permissions,
        )
    }

    #[flux_rs::sig(fn(
        FluxPtrU8,
        usize,
        FluxPtrU8[@rstart],
        usize[@rsize],
        usize[@region_num],
        usize[@subregion_start],
        usize[@subregion_end],
        mpu::Permissions[@perms]
    ) -> Self { r: 
            encodes_base(r.rbar, rstart, region_num) &&
            encodes_attrs(r.rasr, rsize, subregion_start, subregion_end, perms) &&
            r.region_no == region_num &&
            r.set == true &&
            r.start == rstart &&
            r.size == rsize &&
            r.first_subregion_no == subregion_start &&
            r.last_subregion_no == subregion_end &&
            r.perms == perms 
        } 
    )]
    fn new_with_subregions(
        logical_start: FluxPtrU8,
        logical_size: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        region_num: usize,
        min_subregion: usize,
        max_subregion: usize,
        permissions: mpu::Permissions,
    ) -> CortexMRegion {
        assume(region_size > 1 && region_size < (u32::MAX as usize));
        assume(logical_size >= 8);

        let base_address = Self::compute_base(region_start, region_num);
        let mut attributes = Self::compute_attributes(region_size, permissions);

        let mask = (min_subregion..=max_subregion).fold(u8::MAX, |res, i| {
            // Enable subregions bit by bit (1 ^ 1 == 0)
            res ^ (1 << i)
        });

        attributes += RegionAttributes::SRD().val(mask as u32);
        Self::into_region(
            Some(CortexMLocation {
                addr: logical_start,
                size: logical_size,
            }),
            base_address,
            attributes,
            region_num,
            region_start,
            region_size,
            min_subregion,
            max_subregion,
            permissions,
        )
    }

    // trusted intializer for ghost state stuff
    #[flux_rs::trusted]
    #[flux_rs::sig(fn (
        Option<CortexMLocation>[@loc],
        FieldValueU32<RegionBaseAddress::Register>[@base_address],
        FieldValueU32<RegionAttributes::Register>[@attributes],
        usize[@region_num],
        FluxPtrU8[@region_start],
        usize[@region_size],
        usize[@min_subregion_num],
        usize[@max_subregion_num],
        mpu::Permissions[@perms]
    ) -> Self[
        base_address,
        attributes,
        loc,
        region_num, 
        true,
        region_start, 
        region_size, 
        min_subregion_num,
        max_subregion_num, 
        perms
        ]
        requires loc 
    )] 
    fn into_region(
        location: Option<CortexMLocation>,
        base_address: FieldValueU32<RegionBaseAddress::Register>,
        attributes: FieldValueU32<RegionAttributes::Register>,
        region_num: usize,
        region_start: FluxPtrU8,
        region_size: usize,
        min_subregion_num: usize,
        max_subregion_num: usize,
        permissions: mpu::Permissions,
    ) -> Self {
        Self {
            location,
            base_address,
            attributes,
            ghost_region_state: GhostRegionState {},
        }
    }

    // trusted intializer for ghost state stuff
    #[flux_rs::trusted]
    #[flux_rs::sig(fn (usize[@region_num]) -> Self {r: r.region_no == region_num && r.set == false && r.loc == false })]
    fn empty(region_num: usize) -> CortexMRegion {
        CortexMRegion {
            location: None,
            base_address: RegionBaseAddress::VALID::UseRBAR()
                + RegionBaseAddress::REGION().val(region_num as u32),
            attributes: RegionAttributes::ENABLE::CLEAR(),
            ghost_region_state: GhostRegionState {} 
        }
    }

    fn location(&self) -> Option<(FluxPtrU8, usize)> {
        let loc = self.location?;
        Some((loc.addr, loc.size))
    }

    #[flux_rs::sig(fn(&CortexMRegion[@addr, @attrs, @loc, @no, @set, @start, @size, @fsr, @lsr, @perms]) -> FieldValueU32<RegionBaseAddress::Register>[addr])]
    fn base_address(&self) -> FieldValueU32<RegionBaseAddress::Register> {
        self.base_address
    }

    #[flux_rs::sig(fn(&CortexMRegion[@addr, @attrs, @loc, @no, @set, @start, @size, @fsr, @lsr, @perms]) -> FieldValueU32<RegionAttributes::Register>[attrs])]
    fn attributes(&self) -> FieldValueU32<RegionAttributes::Register> {
        self.attributes
    }

    fn overlaps(&self, other_start: FluxPtrU8, other_size: usize) -> bool {
        let other_start = other_start.as_usize();
        let other_end = other_start + other_size;

        let (region_start, region_end) = match self.location() {
            Some((region_start, region_size)) => {
                let region_start = region_start.as_usize();
                let region_end = region_start + region_size;
                (region_start, region_end)
            }
            None => return false,
        };

        region_start < other_end && other_start < region_end
    }
}

#[flux_rs::assoc(fn enabled(self: Self) -> bool {enable(self.ctrl)} )]
#[flux_rs::assoc(fn configured_for(self: Self, config: CortexMConfig) -> bool {mpu_configured_for(self, config)} )]
// #[flux_rs::assoc(fn config_access_correct(old_c: CortexMConfig, start_addr: int, memsz: int, minsz: int, perms: mpu::Permissions, new_c: CortexMConfig) -> bool {config_access_correct(old_c, start_addr, memsz, minsz, perms, new_c)})]
// #[flux_rs::assoc(fn can_access(self: Self, addr: int, sz: int, perms: Permissions) -> bool {false} )]
impl<const MIN_REGION_SIZE: usize> mpu::MPU for MPU<MIN_REGION_SIZE> {
    type MpuConfig = CortexMConfig;

    // #[flux_rs::sig(fn(self: &strg Self) ensures self: Self)]
    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{mpu: enable(mpu.ctrl)})]
    fn enable_app_mpu(&mut self) {
        // Enable the MPU, disable it during HardFault/NMI handlers, and allow
        // privileged code access to all unprotected memory.
        self.registers.ctrl.write(
            Control::ENABLE::SET() + Control::HFNMIENA::CLEAR() + Control::PRIVDEFENA::SET(),
        );
    }

    #[flux_rs::sig(fn(self: &strg Self) ensures self: Self{mpu: !enable(mpu.ctrl)})]
    fn disable_app_mpu(&mut self) {
        // The MPU is not enabled for privileged mode, so we don't have to do
        // anything
        self.registers.ctrl.write(Control::ENABLE::CLEAR());
    }

    fn number_total_regions(&self) -> usize {
        self.registers.mpu_type.read(Type::DREGION()) as usize
    }

    fn new_config(&self) -> Option<Self::MpuConfig> {
        let id = self.config_count.get();
        self.config_count.set(id.checked_add(1)?);

        // Allocate the regions with index `0` first, then use `reset_config` to
        // write the properly-indexed `CortexMRegion`s:
        let mut ret = CortexMConfig {
            id,
            regions: [CortexMRegion::empty(0); 8],
            is_dirty: Cell::new(true),
            region_state: RegionGhostState::new(),
        };

        self.reset_config(&mut ret);

        Some(ret)
    }

    fn reset_config(&self, config: &mut Self::MpuConfig) {
        config.region_set(0, CortexMRegion::empty(0));
        config.region_set(1, CortexMRegion::empty(1));
        config.region_set(2, CortexMRegion::empty(2));
        config.region_set(3, CortexMRegion::empty(3));
        config.region_set(4, CortexMRegion::empty(4));
        config.region_set(5, CortexMRegion::empty(5));
        config.region_set(6, CortexMRegion::empty(6));
        config.region_set(7, CortexMRegion::empty(7));

        config.set_dirty(true);
    }

    #[flux_rs::sig(fn(
        _,
        FluxPtrU8[@memstart],
        usize[@memsz],
        usize[@minsz],
        mpu::Permissions[@perms],
        config: &strg CortexMConfig[@old_c],
    ) -> Option<{r, rnum. (mpu::Region[r], usize[rnum]) | config_post_allocate_region(old_c, new_c, rnum, r.ptr, r.sz)}>
        ensures config: CortexMConfig[#new_c] 
    )]
    fn allocate_region(
        &self,
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_region_size: usize,
        permissions: mpu::Permissions,
        config: &mut CortexMConfig,
    ) -> Option<(mpu::Region, usize)> {
        assume(min_region_size < 2147483648);

        // Check that no previously allocated regions overlap the unallocated memory.
        for region in config.regions_iter() {
            if region.overlaps(unallocated_memory_start, unallocated_memory_size) {
                return None;
            }
        }

        let region_num = config.unused_region_number()?;

        // Logical region
        let mut start = unallocated_memory_start.as_usize();
        let mut size = min_region_size;

        // Region start always has to align to minimum region size bytes
        if start % MIN_REGION_SIZE != 0 {
            start += MIN_REGION_SIZE - (start % MIN_REGION_SIZE);
        }

        // Regions must be at least minimum region size bytes
        if size < MIN_REGION_SIZE {
            size = MIN_REGION_SIZE;
        }

        // Physical MPU region (might be larger than logical region if some subregions are disabled)
        let mut region_start = start;
        let mut region_size = size;
        let mut subregions = None;
        // We can only create an MPU region if the size is a power of two and it divides
        // the start address. If this is not the case, the first thing we try to do to
        // cover the memory region is to use a larger MPU region and expose certain subregions.
        if size.count_ones() > 1 || start % size != 0 {
            // Which (power-of-two) subregion size would align with the start
            // address?
            //
            // We find this by taking smallest binary substring of the start
            // address with exactly one bit:
            //
            //      1 << (start.trailing_zeros())
            let subregion_size = {
                let tz = start.trailing_zeros();
                if tz < 32 {
                    // Find the largest power of two that divides `start`
                    // 1_usize << tz
                    power_of_two(tz)
                } else {
                    // This case means `start` is 0.
                    let mut ceil = math::closest_power_of_two(size as u32) as usize;
                    if ceil < 256 {
                        ceil = 256
                    }
                    ceil / 8
                }
            };

            // Once we have a subregion size, we get a region size by
            // multiplying it by the number of subregions per region.
            let underlying_region_size = subregion_size * 8;

            // Finally, we calculate the region base by finding the nearest
            // address below `start` that aligns with the region size.
            let underlying_region_start = start - (start % underlying_region_size);

            // If `size` doesn't align to the subregion size, extend it.
            if size % subregion_size != 0 {
                size += subregion_size - (size % subregion_size);
            }

            assume(size < 2147483648);

            let end = start + size;
            let underlying_region_end = underlying_region_start + underlying_region_size;

            // To use subregions, the region must be at least 256 bytes. Also, we need
            // the amount of left over space in the region after `start` to be at least as
            // large as the memory region we want to cover.
            if subregion_size >= 32 && underlying_region_end >= end {
                // The index of the first subregion to activate is the number of
                // regions between `region_start` (MPU) and `start` (memory).
                let min_subregion = (start - underlying_region_start) / subregion_size;

                // The index of the last subregion to activate is the number of
                // regions that fit in `len`, plus the `min_subregion`, minus one
                // (because subregions are zero-indexed).
                let max_subregion = min_subregion + size / subregion_size - 1;

                region_start = underlying_region_start;
                region_size = underlying_region_size;
                subregions = Some((min_subregion, max_subregion));
            } else {
                // In this case, we can't use subregions to solve the alignment
                // problem. Instead, we round up `size` to a power of two and
                // shift `start` up in memory to make it align with `size`.

                size = math::closest_power_of_two_usize(size);
                start += size - (start % size);

                region_start = start;
                region_size = size;
            }
        }

        // Check that our logical region fits in memory.
        if start + size > (unallocated_memory_start.as_usize()) + unallocated_memory_size {
            return None;
        }

        let region = match subregions {
            Some((start, end)) => CortexMRegion::new_with_subregions(
                start.as_fluxptr(),
                size,
                region_start.as_fluxptr(),
                region_size,
                region_num,
                start,
                end,
                permissions,
            ),
            None => CortexMRegion::new_without_subregions(
                start.as_fluxptr(),
                size,
                region_start.as_fluxptr(),
                region_size,
                region_num,
                permissions
            )
        };

        config.region_set(region_num, region);
        config.set_dirty(true);

        Some((mpu::Region::new(start.as_fluxptr(), size), region_num))
    }

    #[flux_rs::sig(fn(
        _,
        region: mpu::Region[@memstart, @memsz],
        config: &strg CortexMConfig[@c],
    ) -> Result<(), ()>
    ensures config: CortexMConfig)]
    fn remove_memory_region(
        &self,
        region: mpu::Region,
        config: &mut CortexMConfig,
    ) -> Result<(), ()> {
        let (idx, _r) = config
            .regions_iter()
            .enumerate()
            .find(|(_idx, r)| **r == region)
            .ok_or(())?;

        if idx <= APP_MEMORY_REGION_MAX_NUM {
            return Err(());
        }
        assume(idx < 8); // need spec for find

        config.region_set(idx, CortexMRegion::empty(idx));
        config.set_dirty(true);

        Ok(())
    }

    // When allocating memory for apps, we use two regions, each a power of two
    // in size. By using two regions we halve their size, and also halve their
    // alignment restrictions.
    #[flux_rs::sig(
        fn (
            &Self,
            FluxPtrU8[@memstart],
            usize[@memsz],
            usize[@minsz],
            usize[@appmsz],
            usize[@kernelmsz],
            mpu::Permissions[@perms],
            config: &strg CortexMConfig[@old_c],
        ) -> Option<{base, memsz. (FluxPtrU8[base], usize[memsz]) | config_post_allocate_app_memory_region(old_c, base, memsz, appmsz, kernelmsz, perms, new_c) }>
        ensures config: CortexMConfig[#new_c]
    )]
    fn allocate_app_memory_region(
        &self,
        unallocated_memory_start: FluxPtrU8,
        unallocated_memory_size: usize,
        min_memory_size: usize,
        initial_app_memory_size: usize,
        initial_kernel_memory_size: usize,
        permissions: mpu::Permissions,
        config: &mut CortexMConfig,
    ) -> Option<(FluxPtrU8, usize)> {
        // Check that no previously allocated regions overlap the unallocated
        // memory.
        for region in config.regions_iter() {
            if region.overlaps(unallocated_memory_start, unallocated_memory_size) {
                return None;
            }
        }

        // Make sure there is enough memory for app memory and kernel memory.
        let memory_size = cmp::max(
            min_memory_size,
            initial_app_memory_size + initial_kernel_memory_size,
        );
        assume(memory_size > 1 && memory_size < 2147483648);

        // Size must be a power of two, so:
        // https://www.youtube.com/watch?v=ovo6zwv6DX4.
        let mut memory_size_po2 = math::closest_power_of_two_usize(memory_size);
        let exponent = math::log_base_two(memory_size_po2 as u32);

        // Check for compliance with the constraints of the MPU.
        if exponent < 9 {
            // Region sizes must be 256 bytes or larger to support subregions.
            // Since we are using two regions, and each must be at least 256
            // bytes, we need the entire memory region to be at least 512 bytes.
            memory_size_po2 = 512;
        } else if exponent > 32 {
            // Region sizes must be 4GB or smaller.
            return None;
        }

        // Region size is the actual size the MPU region will be set to, and is
        // half of the total power of two size we are allocating to the app.

        let mut region_size = memory_size_po2 / 2;

        // The region should start as close as possible to the start of the
        // unallocated memory.
        let mut region_start = unallocated_memory_start.as_usize();

        // If the start and length don't align, move region up until it does.
        if region_start % region_size != 0 {
            region_start += region_size - (region_start % region_size);
        }

        // We allocate two MPU regions exactly over the process memory block,
        // and we disable subregions at the end of this region to disallow
        // access to the memory past the app break. As the app break later
        // increases, we will be able to linearly grow the logical region
        // covering app-owned memory by enabling more and more subregions. The
        // Cortex-M MPU supports 8 subregions per region, so the size of this
        // logical region is always a multiple of a sixteenth of the MPU region
        // length.

        // Determine the number of subregions to enable.
        // Want `round_up(app_memory_size / subregion_size)`.
        let mut num_enabled_subregions = initial_app_memory_size * 8 / region_size + 1;

        let subregion_size = region_size / 8;

        // Calculates the end address of the enabled subregions and the initial
        // kernel memory break.
        let subregions_enabled_end = region_start + num_enabled_subregions * subregion_size;
        //let kernel_memory_break = region_start + memory_size_po2 - initial_kernel_memory_size;

        let kernel_memory_break =
            (region_start + memory_size_po2).checked_sub(initial_kernel_memory_size)?;

        // If the last subregion covering app-owned memory overlaps the start of
        // kernel-owned memory, we make the entire process memory block twice as
        // big so there is plenty of space between app-owned and kernel-owned
        // memory.
        if subregions_enabled_end > kernel_memory_break {
            region_size *= 2;

            if region_start % region_size != 0 {
                region_start += region_size - (region_start % region_size);
            }

            num_enabled_subregions = initial_app_memory_size * 8 / region_size + 1;
        }

        // Make sure the region fits in the unallocated memory.
        if region_start + memory_size_po2
            > (unallocated_memory_start.as_usize()) + unallocated_memory_size
        {
            return None;
        }

        // Get the number of subregions enabled in each of the two MPU regions.
        let num_enabled_subregions0 = cmp::min(num_enabled_subregions, 8);
        let num_enabled_subregions1 = num_enabled_subregions.saturating_sub(8);

        assume(num_enabled_subregions0 > 0);

        let region0 = CortexMRegion::new_with_subregions(
            region_start.as_fluxptr(),
            region_size,
            region_start.as_fluxptr(),
            region_size,
            0,
            0,
            num_enabled_subregions0 - 1,
            permissions,
        );

        // We cannot have a completely unused MPU region
        let region1 = if num_enabled_subregions1 == 0 {
            CortexMRegion::empty(1)
        } else {
            CortexMRegion::new_with_subregions(
                (region_start + region_size).as_fluxptr(),
                region_size,
                (region_start + region_size).as_fluxptr(),
                region_size,
                1,
                0, 
                num_enabled_subregions1 - 1,
                permissions,
            )
        };

        config.region_set(0, region0);
        config.region_set(1, region1);
        config.set_dirty(true);

        Some((region_start.as_fluxptr(), memory_size_po2))
    }

    fn update_app_memory_region(
        &self,
        app_memory_break: FluxPtrU8,
        kernel_memory_break: FluxPtrU8,
        permissions: mpu::Permissions,
        config: &mut Self::MpuConfig,
    ) -> Result<(), ()> {
        // Get first region, or error if the process tried to update app memory
        // MPU region before it was created.
        let (region_start_ptr, region_size) = config.get_region(0).location().ok_or(())?;
        let region_start = region_start_ptr.as_usize();

        let app_memory_break = app_memory_break.as_usize();
        let kernel_memory_break = kernel_memory_break.as_usize();

        assume(app_memory_break > region_start);
        assume(region_size > 7);

        // Out of memory
        if app_memory_break > kernel_memory_break {
            return Err(());
        }

        // Number of bytes the process wants access to.
        let app_memory_size = app_memory_break - region_start;

        // There are eight subregions for every region in the Cortex-M3/4 MPU.
        let subregion_size = region_size / 8;

        // Determine the number of subregions to enable.
        // Want `round_up(app_memory_size / subregion_size)`.
        let num_enabled_subregions = (app_memory_size + subregion_size - 1) / subregion_size;

        let subregions_enabled_end = region_start + subregion_size * num_enabled_subregions;

        // If we can no longer cover app memory with an MPU region without
        // overlapping kernel memory, we fail.
        if subregions_enabled_end > kernel_memory_break {
            return Err(());
        }

        // Get the number of subregions enabled in each of the two MPU regions.
        let num_enabled_subregions0 = cmp::min(num_enabled_subregions, 8);
        assume(num_enabled_subregions0 >= 8);
        let num_enabled_subregions1 = num_enabled_subregions.saturating_sub(8);

        let region0 = CortexMRegion::new_with_subregions(
            region_start.as_fluxptr(),
            region_size,
            region_start.as_fluxptr(),
            region_size,
            0,
            0,
            num_enabled_subregions0 - 1,
            permissions,
        );

        let region1 = if num_enabled_subregions1 == 0 {
            CortexMRegion::empty(1)
        } else {
            CortexMRegion::new_with_subregions(
                (region_start + region_size).as_fluxptr(),
                region_size,
                (region_start + region_size).as_fluxptr(),
                region_size,
                1,
                0, 
                num_enabled_subregions1 - 1,
                permissions,
            )
        };

        config.region_set(0, region0);
        config.region_set(1, region1);
        config.set_dirty(true);

        Ok(())
    }

    // TODO: reimplement dirty tracking
    // TODO: add for loop back in
    #[flux_rs::sig(fn(self: &strg Self, &CortexMConfig[@config]) ensures self: Self{mpu: mpu_configured_for(mpu, config)})]
    fn configure_mpu(&mut self, config: &CortexMConfig) {
        // If the hardware is already configured for this app and the app's MPU
        // configuration has not changed, then skip the hardware update.
        // if !self.hardware_is_configured_for.contains(&config.id()) || config.is_dirty() {
        // Set MPU regions
        self.commit_region(config.get_region(0));
        self.commit_region(config.get_region(1));
        self.commit_region(config.get_region(2));
        self.commit_region(config.get_region(3));
        self.commit_region(config.get_region(4));
        self.commit_region(config.get_region(5));
        self.commit_region(config.get_region(6));
        self.commit_region(config.get_region(7));
        // for region in config.regions_iter() {
        //     self.commit_region(region);
        // }
        // self.hardware_is_configured_for.set(config.id());
        // config.set_dirty(false);
        // }
    }
}

// TODO: simplify configured_for
// -- requires proving that beyond 8, everything is the same
// -- alternately, just requires a special macro
// TODO: better solution than trusted `get_region`?
// TODO: once there is support for double projections in specs, remove `value()` function
// -- alternately, dont refine CortexMRegion by FieldValue but just by bitvec?
