// Licensed under the Apache License, Version 2.0 or the MIT License.
// SPDX-License-Identifier: Apache-2.0 OR MIT
// Copyright Tock Contributors 2022.

extern crate flux_core;

use core::cell::Cell;
use core::fmt;
use core::num::NonZeroUsize;

use crate::csr;
use flux_support::capability::MpuEnabledCapability;
use flux_support::{register_bitfields_u8, FluxPtr, FluxPtrU8, FluxRange, Pair, RArray};
use flux_support::{FieldValueU32, LocalRegisterCopyU8, RegisterLongName};
use kernel::platform::mpu::{self, RegionDescriptor};
use kernel::utilities::cells::OptionalCell;
use kernel::utilities::registers::FieldValue;

flux_rs::defs! {

    fn valid_size(x: int) -> bool { 0 <= x && x <= u32::MAX }

    fn is_empty(r: PMPUserRegion) -> bool {
        r.start >= r.end
    }

    fn contains(r: PMPUserRegion, i: int) -> bool {
        r.start <= i && i < r.end
    }

    fn saturating_sub(a: int, b: int) -> int {
        if a > b {
            a - b
        } else {
            0
        }
    }

    fn max(x: int, y: int) -> int {
        if x > y {
            x
        } else {
            y
        }
    }

    fn min(x: int, y: int) -> int {
        if x > y {
            y
        } else {
            x
        }
    }

    fn region_overlaps(range1: PMPUserRegion, start: int, end: int) -> bool {
        if !range1.is_set || is_empty(range1) || start >= end {
            false
        } else {
            max(range1.start, start) < min(range1.end, end)
        }
    }

    // PMP specific model
    fn bit(reg: bitvec<32>, power_of_two: bitvec<32>) -> bool { reg & power_of_two != 0}
    fn extract(reg: bitvec<32>, mask:int, offset: int) -> bitvec<32> { (reg & bv_int_to_bv32(mask)) >> bv_int_to_bv32(offset) }

    // See Figure 34. PMP configuration register format. in the RISCV ISA (Section 3.7)
    // For TORUserCFG

    fn permissions_match(perms: mpu::Permissions, reg: LocalRegisterCopyU8) -> bool {
        if (perms.x && perms.w && perms.r) {
            bit(reg.val, 1) && bit(reg.val, 2) && bit(reg.val, 4)
        } else if (perms.r && perms.w) {
            bit(reg.val, 1) && bit(reg.val, 2) && !bit(reg.val, 4)
        } else if (perms.r && perms.x) {
            bit(reg.val, 1) && !bit(reg.val, 2) && bit(reg.val, 4)
        } else if (perms.r) {
            bit(reg.val, 1) && !bit(reg.val, 2) && !bit(reg.val, 4)
        } else if (perms.x) {
            !bit(reg.val, 1) && !bit(reg.val, 2) && bit(reg.val, 4)
        } else {
            // nothing else supported
            false
        }
    }

    fn active_pmp_user_cfg_correct(cfg: TORUserPMPCFG, perms: mpu::Permissions) -> bool {
        // the permissions are correct encoded in the CFG reg.
        permissions_match(perms, cfg.reg) &&
        // L bit is clear - meaning the entry can be modified later
        !bit(cfg.reg.val, 1 << 7) &&
        // Addressing mode is Top of Range (TOR)
        extract(cfg.reg.val, 0b11000, 3) == 1
    }

    fn inactive_pmp_user_cfg_correct(cfg: TORUserPMPCFG) -> bool {
        // L bit is clear - meaning the entry can be modified later
        !bit(cfg.reg.val, 1 << 7) &&
        // Addressing mode is OFF - indicating a disabled region
        extract(cfg.reg.val, 0b11000, 3) == 0
    }

    fn cfg_reg_configured_correctly(cfg_reg: bitvec<32>, region: PMPUserRegion, idx: int) -> bool {
        // 4 regions can be packed into a cfg register -
        // the code packs the odd region in the first 4 bytes
        // and the even region in the third 4 bytes
        if (idx % 2 == 0) {
            // extract the first cfg region
            let odd_region_bits = extract(cfg_reg, 0x0000FF00, 8); // extracts bits 15 - 8 of the register because it's stored as BE
            odd_region_bits == region.tor_cfg.reg.val
        } else {
            // extract the third cfg region
            let even_region_bits = extract(cfg_reg, 0xFF000000, 24); // extracts bits 31 - 24 of the register because it's stored as BE
            even_region_bits == region.tor_cfg.reg.val
        }
    }

    fn addr_reg_configured_correctly(addr_registers: Map<int, bitvec<32>>, region: PMPUserRegion, idx: int) -> bool {
        if (idx % 2 == 0) {
            let even_addr_start_idx = idx * 2;
            let even_addr_end_idx = idx * 2 + 1;
            if region.tor_cfg.reg.val != 0 {
                let even_start_reg = map_select(addr_registers, even_addr_start_idx);
                let even_end_reg = map_select(addr_registers, even_addr_end_idx);

                // top of range - sanity check
                even_addr_start_idx + 1 == even_addr_end_idx &&
                even_start_reg == bv_int_to_bv32(region.start) >> 2 &&
                even_end_reg == bv_int_to_bv32(region.end) >> 2
            } else {
                true
            }
        } else {
            let odd_addr_start_idx = (idx - 1) * 2 + 2;
            let odd_addr_end_idx = (idx - 1) * 2 + 3;
            if region.tor_cfg.reg.val != 0 {
                let odd_start_reg = map_select(addr_registers, odd_addr_start_idx);
                let odd_end_reg = map_select(addr_registers, odd_addr_end_idx);

                // top of range - sanity check
                odd_addr_start_idx + 1 == odd_addr_end_idx &&
                odd_start_reg == bv_int_to_bv32(region.start) >> 2 &&
                odd_end_reg == bv_int_to_bv32(region.end) >> 2
            } else {
                true
            }
        }
    }

    fn region_configured_correctly(region: PMPUserRegion, old: HardwareState, new: HardwareState, idx: int) -> bool {
        let cfg_reg_idx = idx / 2;
        let cfg_reg = map_select(new.pmpcfg_registers, cfg_reg_idx);
        cfg_reg_configured_correctly(cfg_reg, region, idx) && addr_reg_configured_correctly(new.pmpaddr_registers, region, idx)
    }

    // uninterpreted since we don't have forall:
    // forall i. i >= 0 && i < bound, region_configured_correctly(hardware_state, i)
    fn all_regions_configured_correctly_up_to(bound: int, hardware_state: HardwareState) -> bool;
}

// Some axioms and verification state
//
// We want to prove that all regions up to a const generic are configured
// correctly but we don't have a forall.
//
// So instead, we do the classic inductive evidence trick

#[flux_rs::opaque]
#[flux_rs::refined_by(pmpcfg_registers: Map<int, bitvec<32>>, pmpaddr_registers: Map<int, bitvec<32>>)]
pub struct HardwareState {}

#[flux_rs::trusted(reason = "Flux Wrappers")]
impl HardwareState {
    pub fn new() -> Self {
        Self {}
    }

    #[flux_rs::sig(fn (&HardwareState[@hw]) -> HardwareState[hw])]
    pub fn snapshot(&self) -> Self {
        Self {}
    }
}

#[flux_rs::trusted(reason = "Proof Code")]
#[flux_rs::sig(fn (&HardwareState[@hw]) ensures all_regions_configured_correctly_up_to(0, hw))]
fn all_regions_configured_correctly_base(hardware_state: &HardwareState) {}

#[flux_rs::trusted(reason = "Proof Code")]
#[flux_rs::sig(fn (&PMPUserRegion[@region], &HardwareState[@old], &HardwareState[@new], i: usize)
    requires all_regions_configured_correctly_up_to(i, old) && region_configured_correctly(region, old, new, i)
    ensures all_regions_configured_correctly_up_to(i + 1, new)
)]
fn all_regions_configured_correctly_step(
    region: &PMPUserRegion,
    old_hw: &HardwareState,
    new_hw: &HardwareState,
    i: usize,
) {
}

#[flux_rs::trusted(reason = "TCB")]
#[flux_rs::sig(
    fn (idx: usize, bits: usize, hw_state: &strg HardwareState[@hw])
        ensures hw_state: HardwareState[{
            pmpaddr_registers: map_store(hw.pmpaddr_registers, idx, bv_int_to_bv32(bits)),
            ..hw
        }]
)]
fn pmpaddr_set(idx: usize, bits: usize, hardware_state: &mut HardwareState) {
    csr::CSR.pmpaddr_set(idx, bits);
}

#[flux_rs::trusted(reason = "TCB")]
#[flux_rs::sig(
    fn (idx: usize, bits: usize, hw_state: &strg HardwareState[@hw])
        ensures hw_state: HardwareState[{
            pmpcfg_registers: map_store(hw.pmpcfg_registers, idx, bv_int_to_bv32(bits)),
            ..hw
        }]
)]
fn pmpconfig_set(idx: usize, bits: usize, hardware_state: &mut HardwareState) {
    csr::CSR.pmpconfig_set(idx, bits);
}

#[flux_rs::trusted(reason = "TCB")]
#[flux_rs::sig(
    fn (idx: usize, FieldValueU32<_>[@mask, @value], hw_state: &strg HardwareState[@hw])
        ensures hw_state: HardwareState[{
            pmpcfg_registers: map_store(
                hw.pmpcfg_registers,
                idx,
                (map_select(hw.pmpcfg_registers, idx) & bv_not(mask)) | value
            ),
            ..hw
        }]
)]
fn pmpconfig_modify(
    idx: usize,
    bits: FieldValueU32<csr::pmpconfig::pmpcfg::Register>,
    hardware_state: &mut HardwareState,
) {
    // SUPER annoying :(
    let bits_inner = bits.into_inner();
    let as_usize = FieldValue::<usize, csr::pmpconfig::pmpcfg::Register>::new(
        bits_inner.mask as usize,
        0,
        bits_inner.value as usize,
    );
    csr::CSR.pmpconfig_modify(idx, as_usize);
}

#[flux_rs::trusted(reason = "TCB")]
#[flux_rs::sig(fn (byte0: u8, byte1: u8, byte2: u8, byte3: u8) -> u32{b:
    extract(bv_int_to_bv32(b), 0xFF000000, 24) == bv_int_to_bv32(byte0) &&
    extract(bv_int_to_bv32(b), 0x00FF0000, 16) == bv_int_to_bv32(byte1) &&
    extract(bv_int_to_bv32(b), 0x0000FF00, 8) == bv_int_to_bv32(byte2) &&
    extract(bv_int_to_bv32(b), 0x000000FF, 0) == bv_int_to_bv32(byte3)
})]
fn u32_from_be_bytes(byte0: u8, byte1: u8, byte2: u8, byte3: u8) -> u32 {
    u32::from_be_bytes([byte0, byte1, byte2, byte3])
}

// We can't use an extern spec here because of the tuple! :(
#[flux_rs::trusted(reason = "Extern Spec")]
#[flux_rs::sig(fn (usize[@fst], u32[@snd]) -> usize[
    if (snd >= 32) {
        bv_bv32_to_int(bv_int_to_bv32(fst) >> bv_int_to_bv32(snd) & 31)
    } else {
        bv_bv32_to_int(bv_int_to_bv32(fst) >> bv_int_to_bv32(snd))
    }
])]
fn overflowing_shr(lhs: usize, rhs: u32) -> usize {
    return lhs.overflowing_shr(rhs).0 as usize;
}

register_bitfields_u8![u8,
    /// Generic `pmpcfg` octet.
    ///
    /// A PMP entry is configured through `pmpaddrX` and `pmpcfgX` CSRs, where a
    /// single `pmpcfgX` CSRs holds multiple octets, each affecting the access
    /// permission, addressing mode and "lock" attributes of a single `pmpaddrX`
    /// CSR. This bitfield definition represents a single, `u8`-backed `pmpcfg`
    /// octet affecting a single `pmpaddr` entry.
    pub pmpcfg_octet [
        r OFFSET(0) NUMBITS(1) [],
        w OFFSET(1) NUMBITS(1) [],
        x OFFSET(2) NUMBITS(1) [],
        a OFFSET(3) NUMBITS(2) [
            OFF = 0,
            TOR = 1,
            NA4 = 2,
            NAPOT = 3
        ],
        l OFFSET(7) NUMBITS(1) []
    ]
];

/// A `pmpcfg` octet for a user-mode (non-locked) TOR-addressed PMP region.
///
/// This is a wrapper around a [`pmpcfg_octet`] (`u8`) register type, which
/// guarantees that the wrapped `pmpcfg` octet is always set to be either
/// [`TORUserPMPCFG::OFF`] (set to `0x00`), or in a non-locked, TOR-addressed
/// configuration.
///
/// By accepting this type, PMP implements can rely on the above properties to
/// hold by construction and avoid runtime checks. For example, this type is
/// used in the [`TORUserPMP::configure_pmp`] method.
#[derive(Copy, Clone)]
#[flux_rs::refined_by(reg: LocalRegisterCopyU8)]
pub struct TORUserPMPCFG(
    #[field(LocalRegisterCopyU8<pmpcfg_octet::Register>[reg])]
    LocalRegisterCopyU8<pmpcfg_octet::Register>,
);

impl TORUserPMPCFG {
    #[flux_rs::sig(fn () -> TORUserPMPCFG{ cfg: inactive_pmp_user_cfg_correct(cfg) && cfg.reg.val == 0 })]
    pub const fn OFF() -> TORUserPMPCFG {
        TORUserPMPCFG(LocalRegisterCopyU8::new(0))
    }

    /// Extract the `u8` representation of the [`pmpcfg_octet`] register.
    #[flux_rs::sig(fn (&Self[@cfg]) -> u8[bv_bv32_to_int(cfg.reg.val)])]
    pub fn get(&self) -> u8 {
        self.0.get()
    }

    /// Extract a copy of the contained [`pmpcfg_octet`] register.
    pub fn get_reg(&self) -> LocalRegisterCopyU8<pmpcfg_octet::Register> {
        self.0
    }
}

impl PartialEq<TORUserPMPCFG> for TORUserPMPCFG {
    #[flux_rs::sig(fn (&Self[@this], &Self[@other]) -> bool[this.reg.val == other.reg.val])]
    fn eq(&self, other: &Self) -> bool {
        self.0.get() == other.0.get()
    }

    #[flux_rs::sig(fn (&Self[@this], &Self[@other]) -> bool[this.reg.val != other.reg.val])]
    fn ne(&self, other: &Self) -> bool {
        self.0.get() != other.0.get()
    }
}

impl Eq for TORUserPMPCFG {}

#[flux_rs::sig(fn (p: mpu::Permissions) -> TORUserPMPCFG{cfg: active_pmp_user_cfg_correct(cfg, p)})]
fn permissions_to_pmpcfg(p: mpu::Permissions) -> TORUserPMPCFG {
    let fv = match p {
        mpu::Permissions::ReadWriteExecute => {
            pmpcfg_octet::r::SET() + pmpcfg_octet::w::SET() + pmpcfg_octet::x::SET()
        }
        mpu::Permissions::ReadWriteOnly => {
            pmpcfg_octet::r::SET() + pmpcfg_octet::w::SET() + pmpcfg_octet::x::CLEAR()
        }
        mpu::Permissions::ReadExecuteOnly => {
            pmpcfg_octet::r::SET() + pmpcfg_octet::w::CLEAR() + pmpcfg_octet::x::SET()
        }
        mpu::Permissions::ReadOnly => {
            pmpcfg_octet::r::SET() + pmpcfg_octet::w::CLEAR() + pmpcfg_octet::x::CLEAR()
        }
        mpu::Permissions::ExecuteOnly => {
            pmpcfg_octet::r::CLEAR() + pmpcfg_octet::w::CLEAR() + pmpcfg_octet::x::SET()
        }
    };

    TORUserPMPCFG(LocalRegisterCopyU8::new(
        (fv + pmpcfg_octet::l::CLEAR() + pmpcfg_octet::a::TOR()).value(),
    ))
}

// impl From<mpu::Permissions> for TORUserPMPCFG {
//     fn from(p: mpu::Permissions) -> Self {
//         let fv = match p {
//             mpu::Permissions::ReadWriteExecute => {
//                 pmpcfg_octet::r::SET + pmpcfg_octet::w::SET + pmpcfg_octet::x::SET
//             }
//             mpu::Permissions::ReadWriteOnly => {
//                 pmpcfg_octet::r::SET + pmpcfg_octet::w::SET + pmpcfg_octet::x::CLEAR
//             }
//             mpu::Permissions::ReadExecuteOnly => {
//                 pmpcfg_octet::r::SET + pmpcfg_octet::w::CLEAR + pmpcfg_octet::x::SET
//             }
//             mpu::Permissions::ReadOnly => {
//                 pmpcfg_octet::r::SET + pmpcfg_octet::w::CLEAR + pmpcfg_octet::x::CLEAR
//             }
//             mpu::Permissions::ExecuteOnly => {
//                 pmpcfg_octet::r::CLEAR + pmpcfg_octet::w::CLEAR + pmpcfg_octet::x::SET
//             }
//         };

//         TORUserPMPCFG(LocalRegisterCopy::new(
//             (fv + pmpcfg_octet::l::CLEAR + pmpcfg_octet::a::TOR).value,
//         ))
//     }
// }

/// A RISC-V PMP memory region specification, configured in NAPOT mode.
///
/// This type checks that the supplied `start` and `size` values meet the RISC-V
/// NAPOT requirements, namely that
///
/// - the region is a power of two bytes in size
/// - the region's start address is aligned to the region size
/// - the region is at least 8 bytes long
///
/// By accepting this type, PMP implementations can rely on these requirements
/// to be verified. Furthermore, they can use the
/// [`NAPOTRegionSpec::napot_addr`] convenience method to retrieve an `pmpaddrX`
/// CSR value encoding this region's address and length.
#[derive(Copy, Clone, Debug)]
#[flux_rs::refined_by(start: int, size: int)]
#[flux_rs::invariant(size > 0)]
#[flux_rs::invariant(start + size <= usize::MAX)]
pub struct NAPOTRegionSpec {
    #[field(FluxPtrU8[start])]
    start: FluxPtrU8,
    #[field(usize[size])]
    size: usize,
}

impl NAPOTRegionSpec {
    /// Construct a new [`NAPOTRegionSpec`]
    ///
    /// This method accepts a `start` address and a region length. It returns
    /// `Some(region)` when all constraints specified in the
    /// [`NAPOTRegionSpec`]'s documentation are satisfied, otherwise `None`.
    #[flux_rs::sig(fn (start: FluxPtrU8, {usize[@size] | size > 0 && start + size <= usize::MAX}) -> Option<Self>)]
    pub fn new(start: FluxPtrU8, size: usize) -> Option<Self> {
        if !size.is_power_of_two() || start.as_usize() % size != 0 || size < 8 {
            None
        } else {
            Some(NAPOTRegionSpec { start, size })
        }
    }

    /// Retrieve the start address of this [`NAPOTRegionSpec`].
    pub fn start(&self) -> FluxPtrU8 {
        self.start
    }

    /// Retrieve the size of this [`NAPOTRegionSpec`].
    pub fn size(&self) -> usize {
        self.size
    }

    /// Retrieve the end address of this [`NAPOTRegionSpec`].
    pub fn end(&self) -> FluxPtrU8 {
        unsafe { self.start.add(self.size) }
    }

    /// Retrieve a `pmpaddrX`-CSR compatible representation of this
    /// [`NAPOTRegionSpec`]'s address and length. For this value to be valid in
    /// a `CSR` register, the `pmpcfgX` octet's `A` (address mode) value
    /// belonging to this `pmpaddrX`-CSR must be set to `NAPOT` (0b11).
    pub fn napot_addr(&self) -> usize {
        (self.start.as_usize() + (self.size - 1).overflowing_shr(1).0)
            .overflowing_shr(2)
            .0
    }
}

/// A RISC-V PMP memory region specification, configured in TOR mode.
///
/// This type checks that the supplied `start` and `end` addresses meet the
/// RISC-V TOR requirements, namely that
///
/// - the region's start address is aligned to a 4-byte boundary
/// - the region's end address is aligned to a 4-byte boundary
/// - the region is at least 4 bytes long
///
/// By accepting this type, PMP implementations can rely on these requirements
/// to be verified.
#[derive(Copy, Clone, Debug)]
pub struct TORRegionSpec {
    start: *const u8,
    end: *const u8,
}

impl TORRegionSpec {
    /// Construct a new [`TORRegionSpec`]
    ///
    /// This method accepts a `start` and `end` address. It returns
    /// `Some(region)` when all constraints specified in the [`TORRegionSpec`]'s
    /// documentation are satisfied, otherwise `None`.
    pub fn new(start: *const u8, end: *const u8) -> Option<Self> {
        if (start as usize) % 4 != 0
            || (end as usize) % 4 != 0
            || (end as usize)
                .checked_sub(start as usize)
                .map_or(true, |size| size < 4)
        {
            None
        } else {
            Some(TORRegionSpec { start, end })
        }
    }

    /// Retrieve the start address of this [`TORRegionSpec`].
    pub fn start(&self) -> *const u8 {
        self.start
    }

    /// Retrieve the end address of this [`TORRegionSpec`].
    pub fn end(&self) -> *const u8 {
        self.end
    }
}

/// Helper method to check if a [`PMPUserMPUConfig`] region overlaps with a
/// region specified by `other_start` and `other_size`.
///
/// Matching the RISC-V spec this checks `pmpaddr[i-i] <= y < pmpaddr[i]` for TOR
/// ranges.
#[flux_rs::sig(fn (&PMPUserRegion[@r], start: usize, end: usize) -> bool[region_overlaps(r, start, end)])]
fn region_overlaps(region: &PMPUserRegion, start: usize, end: usize) -> bool {
    // PMP TOR regions are not inclusive on the high end, that is
    //     pmpaddr[i-i] <= y < pmpaddr[i].
    //
    // This happens to coincide with the definition of the Rust half-open Range
    // type, which provides a convenient `.contains()` method:

    // TODO: Use Range for real? Problem is the implementation is crazy
    let region_range = match (region.start, region.end) {
        (Some(start), Some(end)) => FluxRange {
            start: start.as_usize(),
            end: end.as_usize(),
        },
        _ => return false,
    };

    let other_range = FluxRange { start, end };

    // For a range A to overlap with a range B, either B's first or B's last
    // element must be contained in A, or A's first or A's last element must be
    // contained in B. As we deal with half-open ranges, ensure that neither
    // range is empty.
    //
    // This implementation is simple and stupid, and can be optimized. We leave
    // that as an exercise to the compiler.
    !region_range.is_empty()
        && !other_range.is_empty()
        && (region_range.contains(&other_range.start)
            || region_range.contains(&other_range.end.saturating_sub(1))
            || other_range.contains(&region_range.start)
            || other_range.contains(&region_range.end.saturating_sub(1)))
}

/// Print a table of the configured PMP regions, read from  the HW CSRs.
///
/// # Safety
///
/// This function is unsafe, as it relies on the PMP CSRs to be accessible, and
/// the hardware to feature `PHYSICAL_ENTRIES` PMP CSR entries. If these
/// conditions are not met, calling this function can result in undefinied
/// behavior (e.g., cause a system trap).
#[flux_rs::trusted(reason = "just used for debugging so who cares")]
pub unsafe fn format_pmp_entries<const PHYSICAL_ENTRIES: usize>(
    f: &mut fmt::Formatter<'_>,
) -> fmt::Result {
    for i in 0..PHYSICAL_ENTRIES {
        // Extract the entry's pmpcfgX register value. The pmpcfgX CSRs are
        // tightly packed and contain 4 octets beloging to individual
        // entries. Convert this into a u8-wide LocalRegisterCopy<u8,
        // pmpcfg_octet> as a generic register type, independent of the entry's
        // offset.
        let pmpcfg: LocalRegisterCopyU8<pmpcfg_octet::Register> = LocalRegisterCopyU8::new(
            csr::CSR
                .pmpconfig_get(i / 4)
                .overflowing_shr(((i % 4) * 8) as u32)
                .0 as u8,
        );

        // The address interpretation is different for every mode. Return both a
        // string indicating the PMP entry's mode, as well as the effective
        // start and end address (inclusive) affected by the region. For regions
        // that are OFF, we still want to expose the pmpaddrX register value --
        // thus return the raw unshifted value as the addr, and 0 as the
        // region's end.
        let (start_label, start, end, mode) = match pmpcfg.read_as_enum(pmpcfg_octet::a()) {
            Some(pmpcfg_octet::a::Value::OFF) => {
                let addr = csr::CSR.pmpaddr_get(i);
                ("pmpaddr", addr, 0, "OFF  ")
            }

            Some(pmpcfg_octet::a::Value::TOR) => {
                let start = if i > 0 {
                    csr::CSR.pmpaddr_get(i - 1)
                } else {
                    0
                };

                (
                    "  start",
                    start.overflowing_shl(2).0,
                    csr::CSR.pmpaddr_get(i).overflowing_shl(2).0.wrapping_sub(1),
                    "TOR  ",
                )
            }

            Some(pmpcfg_octet::a::Value::NA4) => {
                let addr = csr::CSR.pmpaddr_get(i).overflowing_shl(2).0;
                ("  start", addr, addr | 0b11, "NA4  ")
            }

            Some(pmpcfg_octet::a::Value::NAPOT) => {
                let pmpaddr = csr::CSR.pmpaddr_get(i);
                let encoded_size = pmpaddr.trailing_ones();
                let size_of_pmp_addr = core::mem::size_of_val(&pmpaddr);
                flux_support::assume(size_of_pmp_addr > 0); // TODO: sizeof
                if (encoded_size as usize) < (size_of_pmp_addr * 8 - 1) {
                    let start = pmpaddr - ((1 << encoded_size) - 1);
                    let end = start + (1 << (encoded_size + 1)) - 1;
                    (
                        "  start",
                        start.overflowing_shl(2).0,
                        end.overflowing_shl(2).0 | 0b11,
                        "NAPOT",
                    )
                } else {
                    ("  start", usize::MIN, usize::MAX, "NAPOT")
                }
            }

            None => {
                // We match on a 2-bit value with 4 variants, so this is
                // unreachable. However, don't insert a panic in case this
                // doesn't get optimized away:
                ("", 0, 0, "")
            }
        };

        // Ternary operator shortcut function, to avoid bulky formatting...
        fn t<T>(cond: bool, a: T, b: T) -> T {
            if cond {
                a
            } else {
                b
            }
        }

        write!(
            f,
            "  [{:02}]: {}={:#010X}, end={:#010X}, cfg={:#04X} ({}) ({}{}{}{})\r\n",
            i,
            start_label,
            start,
            end,
            pmpcfg.get(),
            mode,
            t(pmpcfg.is_set(pmpcfg_octet::l()), "l", "-"),
            t(pmpcfg.is_set(pmpcfg_octet::r()), "r", "-"),
            t(pmpcfg.is_set(pmpcfg_octet::w()), "w", "-"),
            t(pmpcfg.is_set(pmpcfg_octet::x()), "x", "-"),
        )?;
    }

    Ok(())
}

/// A RISC-V PMP implementation exposing a number of TOR memory protection
/// regions to the [`PMPUserMPU`].
///
/// The RISC-V PMP is complex and can be used to enforce memory protection in
/// various modes (Machine, Supervisor and User mode). Depending on the exact
/// extension set present (e.g., ePMP) and the machine's security configuration
/// bits, it may expose a vastly different set of constraints and application
/// semantics.
///
/// Because we can't possibly capture all of this in a single readable,
/// maintainable and efficient implementation, we implement a two-layer system:
///
/// - a [`TORUserPMP`] is a simple abstraction over some underlying PMP hardware
///   implementation, which exposes an interface to configure regions that are
///   active (enforced) in user-mode and can be configured for arbitrary
///   addresses on a 4-byte granularity.
///
/// - the [`PMPUserMPU`] takes this abstraction and implements the Tock kernel's
///   [`mpu::MPU`] trait. It worries about re-configuring memory protection when
///   switching processes, allocating memory regions of an appropriate size,
///   etc.
///
/// Implementors of a chip are free to define their own [`TORUserPMP`]
/// implementations, adhering to their specific PMP layout & constraints,
/// provided they implement this trait.
///
/// The `MAX_REGIONS` const generic is used to indicate the maximum number of
/// TOR PMP regions available to the [`PMPUserMPU`]. The PMP implementation may
/// provide less regions than indicated through `MAX_REGIONS`, for instance when
/// entries are enforced (locked) in machine mode. The number of available
/// regions may change at runtime. The current number of regions available to
/// the [`PMPUserMPU`] is indicated by the [`TORUserPMP::available_regions`]
/// method. However, when it is known that a number of regions are not available
/// for userspace protection, `MAX_REGIONS` can be used to reduce the memory
/// footprint allocated by stored PMP configurations, as well as the
/// re-configuration overhead.
pub trait TORUserPMP<const MAX_REGIONS: usize> {
    /// A placeholder to define const-assertions which are evaluated in
    /// [`PMPUserMPU::new`]. This can be used to, for instance, assert that the
    /// number of userspace regions does not exceed the number of hardware
    /// regions.
    const CONST_ASSERT_CHECK: ();

    /// The number of TOR regions currently available for userspace memory
    /// protection. Within `[0; MAX_REGIONS]`.
    ///
    /// The PMP implementation may provide less regions than indicated through
    /// `MAX_REGIONS`, for instance when entries are enforced (locked) in
    /// machine mode. The number of available regions may change at runtime. The
    /// implementation is free to map these regions to arbitrary PMP entries
    /// (and change this mapping at runtime), provided that they are enforced
    /// when the hart is in user-mode, and other memory regions are generally
    /// inaccessible when in user-mode.
    ///
    /// When allocating regions for kernel-mode protection, and thus reducing
    /// the number of regions available to userspace, re-configuring the PMP may
    /// fail. This is allowed behavior. However, the PMP must not remove any
    /// regions from the user-mode current configuration while it is active
    /// ([`TORUserPMP::enable_user_pmp`] has been called, and it has not been
    /// disabled through [`TORUserPMP::disable_user_pmp`]).
    fn available_regions(&self) -> usize;

    /// Configure the user-mode memory protection.
    ///
    /// This method configures the user-mode memory protection, to be enforced
    /// on a call to [`TORUserPMP::enable_user_pmp`].
    ///
    /// PMP implementations where configured regions are only enforced in
    /// user-mode may re-configure the PMP on this function invocation and
    /// implement [`TORUserPMP::enable_user_pmp`] as a no-op. If configured
    /// regions are enforced in machine-mode (for instance when using an ePMP
    /// with the machine-mode whitelist policy), the new configuration rules
    /// must not apply until [`TORUserPMP::enable_user_pmp`].
    ///
    /// The tuples as passed in the `regions` parameter are defined as follows:
    ///
    /// - first value ([`TORUserPMPCFG`]): the memory protection mode as
    ///   enforced on the region. A `TORUserPMPCFG` can be created from the
    ///   [`mpu::Permissions`] type. It is in a format compatible to the pmpcfgX
    ///   register, guaranteed to not have the lock (`L`) bit set, and
    ///   configured either as a TOR region (`A = 0b01`), or disabled (all bits
    ///   set to `0`).
    ///
    /// - second value (`*const u8`): the region's start addres. As a PMP TOR
    ///   region has a 4-byte address granularity, this address is rounded down
    ///   to the next 4-byte boundary.
    ///
    /// - third value (`*const u8`): the region's end addres. As a PMP TOR
    ///   region has a 4-byte address granularity, this address is rounded down
    ///   to the next 4-byte boundary.
    ///
    /// To disable a region, set its configuration to [`TORUserPMPCFG::OFF`]. In
    /// this case, the start and end addresses are ignored and can be set to
    /// arbitrary values.
    #[flux_rs::sig(fn (&Self, &[PMPUserRegion; _], hw_state: &strg HardwareState) -> Result<(), ()>[#ok] ensures hw_state: HardwareState {hw:
        ok => all_regions_configured_correctly_up_to(MAX_REGIONS, hw)
    })]
    fn configure_pmp(
        &self,
        regions: &[PMPUserRegion; MAX_REGIONS],
        hardware_state: &mut HardwareState,
    ) -> Result<(), ()>;

    /// Enable the user-mode memory protection.
    ///
    /// Enables the memory protection for user-mode, as configured through
    /// [`TORUserPMP::configure_pmp`]. Enabling the PMP for user-mode may make
    /// the user-mode accessible regions inaccessible to the kernel. For PMP
    /// implementations where configured regions are only enforced in user-mode,
    /// this method may be implemented as a no-op.
    ///
    /// If enabling the current configuration is not possible (e.g., because
    /// regions have been allocated to the kernel), this function must return
    /// `Err(())`. Otherwise, this function returns `Ok(())`.
    fn enable_user_pmp(&self) -> Result<(), ()>;

    /// Disable the user-mode memory protection.
    ///
    /// Disables the memory protection for user-mode. If enabling the user-mode
    /// memory protetion made user-mode accessible regions inaccessible to
    /// machine-mode, this method should make these regions accessible again.
    ///
    /// For PMP implementations where configured regions are only enforced in
    /// user-mode, this method may be implemented as a no-op. This method is not
    /// responsible for making regions inaccessible to user-mode. If previously
    /// configured regions must be made inaccessible,
    /// [`TORUserPMP::configure_pmp`] must be used to re-configure the PMP
    /// accordingly.
    fn disable_user_pmp(&self);
}

/// Struct storing userspace memory protection regions for the [`PMPUserMPU`].
pub struct PMPUserMPUConfig<const MAX_REGIONS: usize> {
    /// PMP config identifier, as generated by the issuing PMP implementation.
    id: NonZeroUsize,
    /// Indicates if the configuration has changed since the last time it was
    /// written to hardware.
    is_dirty: Cell<bool>,
    /// Array of MPU regions. Each region requires two physical PMP entries.
    regions: [(TORUserPMPCFG, *const u8, *const u8); MAX_REGIONS],
    /// Which region index (into the `regions` array above) is used
    /// for app memory (if it has been configured).
    app_memory_region: OptionalCell<usize>,
}

#[derive(Clone, Copy)]
#[flux_rs::opaque]
#[flux_rs::refined_by(start: int, end: int, perms: mpu::Permissions)]
pub struct RegionGhost {}

#[flux_rs::trusted]
impl RegionGhost {
    #[flux_rs::sig(fn (start: FluxPtr, end: FluxPtr, perms: mpu::Permissions) -> Self[start, end, perms])]
    pub fn new(_start: FluxPtr, _end: FluxPtr, _perms: mpu::Permissions) -> Self {
        Self {}
    }

    #[flux_rs::sig(fn () -> Self)]
    pub fn empty() -> Self {
        Self {}
    }
}

#[derive(Clone, Copy)]
#[flux_rs::refined_by(
    region_number: int,
    tor_cfg: TORUserPMPCFG,
    start: int,
    end: int,
    perms: mpu::Permissions,
    is_set: bool
)]
#[flux_rs::invariant(is_set => valid_size(end))]
#[flux_rs::invariant(is_set => end >= start)]
pub struct PMPUserRegion {
    #[field(usize[region_number])]
    pub region_number: usize,
    #[field({TORUserPMPCFG[tor_cfg] |
        (is_set => active_pmp_user_cfg_correct(tor_cfg, perms)) &&
        (!is_set => inactive_pmp_user_cfg_correct(tor_cfg) && tor_cfg.reg.val == 0)
    })]
    pub tor: TORUserPMPCFG,
    #[field(Option<FluxPtrU8[start]>[is_set])]
    pub start: Option<FluxPtrU8>,
    #[field(Option<FluxPtrU8[end]>[is_set])]
    pub end: Option<FluxPtrU8>,
    #[field({ RegionGhost[start, end, perms] | is_set => start % 4 == 0 && end % 4 == 0 })]
    pub ghost: RegionGhost,
}

impl PMPUserRegion {
    #[flux_rs::sig(
        fn (region_number: usize, tor: TORUserPMPCFG, start: FluxPtrU8, end: FluxPtrU8, perms: mpu::Permissions) -> Self[region_number, tor, start, end, perms, true]
            requires end >= start && active_pmp_user_cfg_correct(tor, perms) && start % 4 == 0 && end % 4 == 0
    )]
    pub fn new(
        region_number: usize,
        tor: TORUserPMPCFG,
        start: FluxPtrU8,
        end: FluxPtrU8,
        perms: mpu::Permissions,
    ) -> Self {
        Self {
            region_number,
            tor,
            start: Some(start),
            end: Some(end),
            ghost: RegionGhost::new(start, end, perms),
        }
    }
}

#[flux_rs::assoc(fn start(r: Self) -> int { r.start })]
#[flux_rs::assoc(fn size(r: Self) -> int { r.end - r.start })]
#[flux_rs::assoc(fn is_set(r: Self) -> bool { r.is_set })]
#[flux_rs::assoc(fn rnum(r: Self) -> int { r.region_number })]
#[flux_rs::assoc(fn perms(r: Self) -> mpu::Permissions { r.perms })]
#[flux_rs::assoc(fn overlaps(r1: Self, start: int, end: int) -> bool { region_overlaps(r1, start, end) })]
impl RegionDescriptor for PMPUserRegion {
    #[flux_rs::sig(fn (&Self[@r]) -> Option<FluxPtrU8{ptr: <Self as RegionDescriptor>::start(r) == ptr}>[<Self as RegionDescriptor>::is_set(r)])]
    fn start(&self) -> Option<FluxPtrU8> {
        self.start
    }

    #[flux_rs::sig(fn (&Self[@r]) -> Option<usize{sz: <Self as RegionDescriptor>::size(r) == sz && valid_size(sz) && valid_size(<Self as RegionDescriptor>::start(r) + sz)}>[<Self as RegionDescriptor>::is_set(r)])]
    fn size(&self) -> Option<usize> {
        match (self.start, self.end) {
            (Some(start), Some(end)) => Some(end.as_usize() - start.as_usize()),
            _ => None,
        }
    }

    #[flux_rs::sig(fn (&Self[@r]) -> bool[<Self as RegionDescriptor>::is_set(r)])]
    fn is_set(&self) -> bool {
        self.start.is_some() && self.end.is_some()
    }

    #[flux_rs::sig(fn (rnum: usize) -> Self {r: !<Self as RegionDescriptor>::is_set(r) && <Self as RegionDescriptor>::rnum(r) == rnum})]
    fn default(region_number: usize) -> Self {
        Self {
            region_number,
            tor: TORUserPMPCFG::OFF(),
            start: None,
            end: None,
            ghost: RegionGhost::empty(),
        }
    }

    #[flux_rs::sig(fn (&Self[@r], start: usize, end: usize) -> bool[<Self as RegionDescriptor>::overlaps(r, start, end)])]
    fn overlaps(&self, start: usize, end: usize) -> bool {
        region_overlaps(self, start, end)
    }

    #[flux_rs::sig(
        fn (
            region_number: usize,
            start: FluxPtrU8,
            size: usize,
            permissions: mpu::Permissions,
        ) -> Option<Self{r: <Self as RegionDescriptor>::region_can_access_exactly(r, start, start + size, permissions)}>
        requires region_number < 8
    )]
    fn create_exact_region(
        region_num: usize,
        start: FluxPtrU8,
        size: usize,
        permissions: mpu::Permissions,
    ) -> Option<Self> {
        let start = start.as_usize();
        let size = size;

        // Region start always has to align to 4 bytes. Round up to a 4 byte
        // boundary if required:
        if start % 4 != 0 {
            return None;
        }

        // Region size always has to align to 4 bytes. Round up to a 4 byte
        // boundary if required:
        if size % 4 != 0 {
            return None;
        }

        // Regions must be at least 4 bytes in size.
        if size < 4 {
            return None;
        }

        let region = PMPUserRegion::new(
            region_num,
            permissions_to_pmpcfg(permissions),
            FluxPtrU8::from(start),
            FluxPtrU8::from(start + size),
            permissions,
        );

        Some(region)
    }

    #[flux_rs::sig(fn (
        max_region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: mpu::Permissions,
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
            ) &&
            !<Self as RegionDescriptor>::is_set(p.snd)
        }> requires max_region_number > 0 && max_region_number < 8
    )]
    fn allocate_regions(
        region_number: usize,
        available_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<Self, Self>> {
        // Meet the PMP TOR region constraints. For this, start with the
        // provided start address and size, transform them to meet the
        // constraints, and then check that we're still within the bounds of the
        // provided values:
        let mut start = available_start.as_usize();
        let mut size = region_size;

        // Region start always has to align to 4 bytes. Round up to a 4 byte
        // boundary if required:
        if start % 4 != 0 {
            start += 4 - (start % 4);
        }

        // Region size always has to align to 4 bytes. Round up to a 4 byte
        // boundary if required:
        if size % 4 != 0 {
            size += 4 - (size % 4);
        }

        // Regions must be at least 4 bytes in size.
        if size < 4 {
            size = 4;
        }

        // Now, check to see whether the adjusted start and size still meet the
        // allocation constraints, namely ensure that
        //
        //     start + size <= unallocated_memory_start + unallocated_memory_size
        if start + size > available_start.as_usize() + available_size {
            // // We're overflowing the provided memory region, can't make
            // // allocation. Normally, we'd abort here.
            // //
            // // However, a previous implementation of this code was incorrect in
            // // that performed this check before adjusting the requested region
            // // size to meet PMP region layout constraints (4 byte alignment for
            // // start and end address). Existing applications whose end-address
            // // is aligned on a less than 4-byte bondary would thus be given
            // // access to additional memory which should be inaccessible.
            // // Unfortunately, we can't fix this without breaking existing
            // // applications. Thus, we perform the same insecure hack here, and
            // // give the apps at most an extra 3 bytes of memory, as long as the
            // // requested region as no write privileges.
            // //
            // // TODO: Remove this logic with as part of
            // // https://github.com/tock/tock/issues/3544
            // let writeable = match permissions {
            //     mpu::Permissions::ReadWriteExecute => true,
            //     mpu::Permissions::ReadWriteOnly => true,
            //     mpu::Permissions::ReadExecuteOnly => false,
            //     mpu::Permissions::ReadOnly => false,
            //     mpu::Permissions::ExecuteOnly => false,
            // };

            // if writeable || (start + size > available_start.as_usize() + available_size + 3) {
            //     return None;
            // }
            return None;
        }
        let region = PMPUserRegion::new(
            region_number,
            permissions_to_pmpcfg(permissions),
            FluxPtrU8::from(start),
            FluxPtrU8::from(start + size),
            permissions,
        );
        Some(Pair {
            fst: region,
            snd: RegionDescriptor::default(region_number + 1),
        })
    }

    #[flux_rs::sig(fn (
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: mpu::Permissions,
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
    }> requires max_region_number > 0 && max_region_number < 8)]
    fn update_regions(
        region_start: FluxPtrU8,
        available_size: usize,
        region_size: usize,
        max_region_number: usize,
        permissions: mpu::Permissions,
    ) -> Option<Pair<Self, Self>> {
        // For this: We should get this from region_start's invariant.
        // It may be worth updating this function to take in the region
        // as a whole
        if region_start.as_usize() % 4 != 0 {
            return None;
        }

        if region_size == 0 {
            return None;
        }

        let mut end = region_start.as_usize() + region_size;
        // Ensure that the requested app_memory_break complies with PMP
        // alignment constraints, namely that the region's end address is 4 byte
        // aligned:
        if end % 4 != 0 {
            end += 4 - (end % 4);
        }

        // Check if there is space for this region
        if end > region_start.as_usize() + available_size {
            return None;
        }

        // If we're not out of memory, return the region
        Some(Pair {
            fst: PMPUserRegion::new(
                max_region_number - 1,
                permissions_to_pmpcfg(permissions),
                region_start,
                FluxPtrU8::from(end),
                permissions,
            ),
            snd: RegionDescriptor::default(max_region_number),
        })
    }

    #[flux_rs::sig(fn (&Self[@r], start: FluxPtrU8, end: FluxPtrU8, perms: mpu::Permissions)
        requires <Self as RegionDescriptor>::region_can_access_exactly(r, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r, end, u32::MAX)
    )]
    fn lemma_region_can_access_exactly_implies_no_overlap(
        &self,
        _start: FluxPtrU8,
        _end: FluxPtrU8,
        _perms: mpu::Permissions,
    ) {
    }

    #[flux_rs::sig(fn (&Self[@r1], &Self[@r2], start: FluxPtrU8, end: FluxPtrU8, perms: mpu::Permissions)
        requires <Self as RegionDescriptor>::regions_can_access_exactly(r1, r2, start, end, perms)
        ensures
            !<Self as RegionDescriptor>::overlaps(r1, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r1, end, u32::MAX) &&
            !<Self as RegionDescriptor>::overlaps(r2, 0, start) &&
            !<Self as RegionDescriptor>::overlaps(r2, end, u32::MAX)
    )]
    fn lemma_regions_can_access_exactly_implies_no_overlap(
        _r1: &Self,
        r2: &Self,
        start: FluxPtrU8,
        end: FluxPtrU8,
        _perms: mpu::Permissions,
    ) {
        if !r2.is_set() {
            r2.lemma_region_not_set_implies_no_overlap(start, end);
        }
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
    fn lemma_region_not_set_implies_no_overlap(&self, start: FluxPtrU8, end: FluxPtrU8) {}

    #[flux_rs::sig(fn (&Self[@r],
            flash_start: FluxPtrU8,
            flash_end: FluxPtrU8,
            mem_start: FluxPtrU8,
            mem_end: FluxPtrU8
        )
        requires
            <Self as RegionDescriptor>::region_can_access_exactly(r, flash_start, flash_end, mpu::Permissions { r: true, x: true, w: false })
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

impl fmt::Display for PMPUserRegion {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Ternary operator shortcut function, to avoid bulky formatting...
        fn t<T>(cond: bool, a: T, b: T) -> T {
            if cond {
                a
            } else {
                b
            }
        }
        let tor_user_pmpcfg = self.tor;
        let pmpcfg = tor_user_pmpcfg.get_reg();
        write!(
            f,
            "     #{:02}: start={:#010X}, end={:#010X}, cfg={:#04X} ({}) (-{}{}{})\r\n",
            self.region_number,
            self.start.unwrap_or(FluxPtrU8::null()).as_usize(),
            self.end.unwrap_or(FluxPtrU8::null()).as_usize(),
            pmpcfg.get(),
            t(pmpcfg.is_set(pmpcfg_octet::a()), "TOR", "OFF"),
            t(pmpcfg.is_set(pmpcfg_octet::r()), "r", "-"),
            t(pmpcfg.is_set(pmpcfg_octet::w()), "w", "-"),
            t(pmpcfg.is_set(pmpcfg_octet::x()), "x", "-"),
        )?;

        write!(f, " }}\r\n")?;
        Ok(())
    }
}

/// Adapter from a generic PMP implementation exposing TOR-type regions to the
/// Tock [`mpu::MPU`] trait. See [`TORUserPMP`].
pub struct PMPUserMPU<const MAX_REGIONS: usize, P: TORUserPMP<MAX_REGIONS> + 'static> {
    /// Monotonically increasing counter for allocated configurations, used to
    /// assign unique IDs to `PMPUserMPUConfig` instances.
    config_count: Cell<NonZeroUsize>,
    /// The configuration that the PMP was last configured for. Used (along with
    /// the `is_dirty` flag) to determine if PMP can skip writing the
    /// configuration to hardware.
    last_configured_for: OptionalCell<NonZeroUsize>,
    /// Underlying hardware PMP implementation, exposing a number (up to
    /// `P::MAX_REGIONS`) of memory protection regions with a 4-byte enforcement
    /// granularity.
    pub pmp: P,
}

impl<const MAX_REGIONS: usize, P: TORUserPMP<MAX_REGIONS> + 'static> PMPUserMPU<MAX_REGIONS, P> {
    pub fn new(pmp: P) -> Self {
        // Assigning this constant here ensures evaluation of the const
        // expression at compile time, and can thus be used to enforce
        // compile-time assertions based on the desired PMP configuration.
        #[allow(clippy::let_unit_value)]
        let _: () = P::CONST_ASSERT_CHECK;

        PMPUserMPU {
            config_count: Cell::new(NonZeroUsize::MIN),
            last_configured_for: OptionalCell::empty(),
            pmp,
        }
    }
}

impl<const MAX_REGIONS: usize, P: TORUserPMP<MAX_REGIONS> + 'static> kernel::platform::mpu::MPU
    for PMPUserMPU<MAX_REGIONS, P>
{
    // type MpuConfig = PMPUserMPUConfig<MAX_REGIONS>;
    type Region = PMPUserRegion;

    fn enable_app_mpu(&self) -> MpuEnabledCapability {
        // TODO: This operation may fail when the PMP is not exclusively used
        // for userspace. Instead of panicing, we should handle this case more
        // gracefully and return an error in the `MPU` trait. Process
        // infrastructure can then attempt to re-schedule the process later on,
        // try to revoke some optional shared memory regions, or suspend the
        // process.
        self.pmp.enable_user_pmp().unwrap();
        MpuEnabledCapability {}
    }

    fn disable_app_mpu(&self) {
        self.pmp.disable_user_pmp()
    }

    fn number_total_regions(&self) -> usize {
        self.pmp.available_regions()
    }

    #[flux_rs::trusted(reason = "fixpoint encoding error")]
    fn configure_mpu(&self, config: &RArray<Self::Region>, id: usize, is_dirty: bool) {
        let mut ac_config: [Self::Region; MAX_REGIONS] =
            core::array::from_fn(|i| <Self::Region as mpu::RegionDescriptor>::default(i));
        for i in 0..MAX_REGIONS {
            if i < 8 {
                ac_config[i] = config.get(i);
            } else {
                ac_config[i] = <Self::Region as mpu::RegionDescriptor>::default(i);
            }
        }
        let mut hw = HardwareState::new();
        self.pmp.configure_pmp(&ac_config, &mut hw).unwrap();
    }
}


pub mod simple {
    use super::{pmpcfg_octet, HardwareState, PMPUserRegion, TORUserPMP, TORUserPMPCFG};
    use crate::{
        csr,
        pmp::{
            all_regions_configured_correctly_base, all_regions_configured_correctly_step,
            u32_from_be_bytes,
        },
    };
    use core::fmt;
    use flux_support::FluxPtr;
    use flux_support::{FieldValueU32, LocalRegisterCopyU8};

    /// A "simple" RISC-V PMP implementation.
    ///
    /// The SimplePMP does not support locked regions, kernel memory protection,
    /// or any ePMP features (using the mseccfg CSR). It is generic over the
    /// number of hardware PMP regions available. `AVAILABLE_ENTRIES` is
    /// expected to be set to the number of available entries.
    ///
    /// [`SimplePMP`] implements [`TORUserPMP`] to expose all of its regions as
    /// "top of range" (TOR) regions (each taking up two physical PMP entires)
    /// for use as a user-mode memory protection mechanism.
    ///
    /// Notably, [`SimplePMP`] implements `TORUserPMP<MPU_REGIONS>` over a
    /// generic `MPU_REGIONS` where `MPU_REGIONS <= (AVAILABLE_ENTRIES / 2)`. As
    /// PMP re-configuration can have a significiant runtime overhead, users are
    /// free to specify a small `MPU_REGIONS` const-generic parameter to reduce
    /// the runtime overhead induced through PMP configuration, at the cost of
    /// having less PMP regions available to use for userspace memory
    /// protection.
    #[flux_rs::refined_by(hw_state: HardwareState)]
    pub struct SimplePMP<const AVAILABLE_ENTRIES: usize> {
        #[field(HardwareState[hw_state])]
        hardware_state: HardwareState,
    }

    flux_rs::defs! {

        fn available_region_setup(i: int, old: HardwareState, new: HardwareState) -> bool {
            let cfg = map_select(new.pmpcfg_registers, i / 4);
            let region_offset = i % 4;

            if region_offset == 0 {
                extract(cfg, 0x00000018, 3) == 0 && !bit(cfg, 1 << 7)
            } else if region_offset == 1 {
                extract(cfg, 0x00001800, 11) == 0 && !bit(cfg, 1 << 15)
            } else if region_offset == 2 {
                extract(cfg, 0x00180000, 19) == 0 && !bit(cfg, 1 << 23)
            } else if region_offset == 3 {
                extract(cfg, 0x18000000, 27) == 0 && !bit(cfg, 1 << 31)
            } else {
                false
            }
        }

        // forall j, j >= 0 && j < i -> available_region_setup(i, hardware_state)
        fn all_available_regions_setup_up_to(i: int, hw: HardwareState) -> bool;
    }

    #[flux_rs::trusted(reason = "Proof Code")]
    #[flux_rs::sig(fn (&HardwareState[@hw]) ensures all_available_regions_setup_up_to(0, hw))]
    fn all_available_regions_setup_up_to_base(_: &HardwareState) {}

    #[flux_rs::trusted(reason = "Proof Code")]
    #[flux_rs::sig(fn (i: usize, &HardwareState[@old], &HardwareState[@new])
        requires all_available_regions_setup_up_to(i, old) && available_region_setup(i, old, new)
        ensures all_available_regions_setup_up_to(i + 1, new)
    )]
    fn all_available_regions_setup_up_to_step(i: usize, old: &HardwareState, new: &HardwareState) {}

    impl<const AVAILABLE_ENTRIES: usize> SimplePMP<AVAILABLE_ENTRIES> {
        pub unsafe fn new() -> Result<Self, ()> {
            // The SimplePMP does not support locked regions, kernel memory
            // protection, or any ePMP features (using the mseccfg CSR). Ensure
            // that we don't find any locked regions. If we don't have locked
            // regions and can still successfully execute code, this means that
            // we're not in the ePMP machine-mode lockdown mode, and can treat
            // our hardware as a regular PMP.
            //
            // Furthermore, we test whether we can use each entry (i.e. whether
            // it actually exists in HW) by flipping the RWX bits. If we can't
            // flip them, then `AVAILABLE_ENTRIES` is incorrect.  However, this
            // is not sufficient to check for locked regions, because of the
            // ePMP's rule-lock-bypass bit. If a rule is locked, it might be the
            // reason why we can execute code or read-write data in machine mode
            // right now. Thus, never try to touch a locked region, as we might
            // well revoke access to a kernel region!

            #[flux_rs::sig(fn (i: usize, hw_state: &strg HardwareState[@old])
                -> Result<{ i32 |  all_available_regions_setup_up_to(i + 1, new) }, ()>
                requires all_available_regions_setup_up_to(i, old)
                ensures hw_state: HardwareState[#new]
            )]
            #[flux_rs::trusted(reason = "VR:HANG")]
            fn configure_initial_pmp_idx(
                i: usize,
                hardware_state: &mut HardwareState,
            ) -> Result<i32, ()> {
                // NOTE: works over PMP entries - hence the mod 4 arithmetic when
                // checking a PMPCFG

                let old: HardwareState = hardware_state.snapshot();

                // Read the entry's CSR:
                #[flux_rs::trusted(reason = "TCB")]
                #[flux_rs::sig(fn (i: usize, &HardwareState[@hw]) -> usize[bv_bv32_to_int(map_select(hw.pmpcfg_registers, i))])]
                fn pmpconfig_get(i: usize, _: &HardwareState) -> usize {
                    csr::CSR.pmpconfig_get(i)
                }

                let pmpcfg_csr = pmpconfig_get(i / 4, &hardware_state);

                #[flux_rs::trusted(reason = "Flux integer conversion")]
                #[flux_rs::sig(fn (x: usize) -> u8[bv_bv32_to_int(extract(bv_int_to_bv32(x), 0xFF, 0))])]
                fn usize_to_u8_truncate(x: usize) -> u8 {
                    x as u8
                }

                #[flux_rs::trusted(reason = "Flux integer conversion")]
                // NOTE: trusted because usize == u32 here
                #[flux_rs::sig(fn (x: usize) -> u32[x] requires x <= u32::MAX)]
                fn usize_to_u32(x: usize) -> u32 {
                    x as u32
                }

                flux_rs::assert((i % 4) * 8 <= 24);

                // Extract the entry's pmpcfg octet:
                let pmpcfg: LocalRegisterCopyU8<pmpcfg_octet::Register> =
                    LocalRegisterCopyU8::new(usize_to_u8_truncate(super::overflowing_shr(
                        pmpcfg_csr,
                        usize_to_u32((i % 4) * 8),
                    )));

                // As outlined above, we never touch a locked region. Thus, bail
                // out if it's locked:
                if pmpcfg.is_set(pmpcfg_octet::l()) {
                    return Err(());
                }

                // Now that it's not locked, we can be sure that regardless of
                // any ePMP bits, this region is either ignored or entirely
                // denied for machine-mode access. Hence, we can change it in
                // arbitrary ways without breaking our own memory access. Try to
                // flip the R/W/X bits:
                use flux_rs::bitvec::BV32;
                // pmpcfg_csr ^ (7 << ((i % 4) * 8))
                // change xor to (a | b) & !(a & b)

                #[flux_rs::sig(fn (x: BV32, y: BV32) -> BV32[(x | y) & bv_not(x & y)])]
                fn xor(x: BV32, y: BV32) -> BV32 {
                    (x | y) & !(x & y)
                }

                let rwx_bits = xor(
                    BV32::from(pmpcfg_csr as u32),
                    BV32::from(7) << BV32::from(usize_to_u32((i % 4) * 8)),
                );
                let rwx_bits: u32 = rwx_bits.into();
                super::pmpconfig_set(i / 4, rwx_bits as usize, hardware_state);

                // Check if the CSR changed:
                if pmpcfg_csr == csr::CSR.pmpconfig_get(i / 4) {
                    // Didn't change! This means that this region is not backed
                    // by HW. Return an error as `AVAILABLE_ENTRIES` is
                    // incorrect:
                    return Err(());
                }

                // Finally, turn the region off:
                let off_bits = BV32::from(pmpcfg_csr as u32)
                    & !(BV32::from(0x18) << BV32::from(usize_to_u32((i % 4) * 8)));
                let off_bits: u32 = off_bits.into();

                super::pmpconfig_set(i / 4, off_bits as usize, hardware_state);

                all_available_regions_setup_up_to_step(i, &old, hardware_state);
                Ok(1669)
            }

            #[flux_rs::sig(fn (idx: usize, &HardwareState[@hw]) requires all_available_regions_setup_up_to(idx, hw))]
            fn assert_setup(idx: usize, _: &HardwareState) {}

            #[flux_rs::sig(fn (idx: usize, hw_state: &strg HardwareState[@og_hw], available_entries: usize)
                -> Result<{ i32 | all_available_regions_setup_up_to(available_entries, hw) }, ()>[#ok]
                requires
                    all_available_regions_setup_up_to(idx, og_hw)
                    && (idx >= available_entries => all_available_regions_setup_up_to(available_entries, og_hw))
                ensures hw_state: HardwareState[#hw]
            )]
            fn configure_initial_pmp_tail(
                i: usize,
                hardware_state: &mut HardwareState,
                available_entries: usize,
            ) -> Result<i32, ()> {
                if i >= available_entries {
                    flux_rs::assert(i >= available_entries);
                    assert_setup(available_entries, hardware_state);
                    return Ok(99);
                }
                let old = hardware_state.snapshot();
                configure_initial_pmp_idx(i, hardware_state)?;
                assert_setup(i + 1, &hardware_state);
                match configure_initial_pmp_tail(i + 1, hardware_state, available_entries) {
                    Ok(_) => return Ok(100),
                    Err(()) => return Err(()),
                }
            }

            // establish some verification specific details
            let mut hardware_state = HardwareState::new();
            all_available_regions_setup_up_to_base(&hardware_state);
            flux_support::const_assume!(AVAILABLE_ENTRIES > 0);

            configure_initial_pmp_tail(0, &mut hardware_state, AVAILABLE_ENTRIES)?;

            // Hardware PMP is verified to be in a compatible mode / state, and
            // has at least `AVAILABLE_ENTRIES` entries.
            Ok(SimplePMP { hardware_state })
        }
    }

    impl<const AVAILABLE_ENTRIES: usize, const MPU_REGIONS: usize> TORUserPMP<MPU_REGIONS>
        for SimplePMP<AVAILABLE_ENTRIES>
    {
        // Ensure that the MPU_REGIONS (starting at entry, and occupying two
        // entries per region) don't overflow the available entires.
        const CONST_ASSERT_CHECK: () = assert!(MPU_REGIONS <= (AVAILABLE_ENTRIES / 2));

        fn available_regions(&self) -> usize {
            // Always assume to have `MPU_REGIONS` usable TOR regions. We don't
            // support locked regions, or kernel protection.
            MPU_REGIONS
        }

        // This implementation is specific for 32-bit systems. We use
        // `u32::from_be_bytes` and then cast to usize, as it manages to compile
        // on 64-bit systems as well. However, this implementation will not work
        // on RV64I systems, due to the changed pmpcfgX CSR layout.
        #[flux_rs::sig(fn (&Self, &[PMPUserRegion; _], hw_state: &strg HardwareState) -> Result<(), ()>[#ok] ensures hw_state: HardwareState {hw:
            ok => all_regions_configured_correctly_up_to(MPU_REGIONS, hw)
        })]
        fn configure_pmp(
            &self,
            regions: &[PMPUserRegion; MPU_REGIONS],
            hardware_state: &mut HardwareState,
        ) -> Result<(), ()> {
            // configures region `i` and region `i + 1` correctly
            #[flux_rs::sig(fn (i: usize, &PMPUserRegion[@er], &PMPUserRegion[@or], hw_state: &strg HardwareState[@og_hw])
                // Note: these pre and post conditions (all_regions_configured) seem silly
                // but we need them because otherwise Flux forgets
                // all state after we return
                requires all_regions_configured_correctly_up_to(i, og_hw) && i % 2 == 0
                ensures hw_state: HardwareState{new_hw: all_regions_configured_correctly_up_to(i + 2, new_hw) }
            )]
            fn configure_region_pair(
                i: usize,
                even_region: &PMPUserRegion,
                odd_region: &PMPUserRegion,
                hardware_state: &mut HardwareState,
            ) {
                let old = hardware_state.snapshot();
                let even_region_start = match even_region.start {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };
                let even_region_end = match even_region.end {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };
                let odd_region_start = match odd_region.start {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };
                let odd_region_end = match odd_region.end {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };

                // We can configure two regions at once which, given that we
                // start at index 0 (an even offset), translates to a single
                // CSR write for the pmpcfgX register:
                super::pmpconfig_set(
                    i / 2,
                    u32_from_be_bytes(
                        odd_region.tor.get(),
                        TORUserPMPCFG::OFF().get(),
                        even_region.tor.get(),
                        TORUserPMPCFG::OFF().get(),
                    ) as usize,
                    hardware_state,
                );

                // Now, set the addresses of the respective regions, if they
                // are enabled, respectively:
                if even_region.tor != TORUserPMPCFG::OFF() {
                    super::pmpaddr_set(
                        i * 2 + 0,
                        super::overflowing_shr(even_region_start.as_usize(), 2),
                        hardware_state,
                    );

                    super::pmpaddr_set(
                        i * 2 + 1,
                        super::overflowing_shr(even_region_end.as_usize(), 2),
                        hardware_state,
                    );
                }

                if odd_region.tor != TORUserPMPCFG::OFF() {
                    super::pmpaddr_set(
                        i * 2 + 2,
                        super::overflowing_shr(odd_region_start.as_usize(), 2),
                        hardware_state,
                    );
                    super::pmpaddr_set(
                        i * 2 + 3,
                        super::overflowing_shr(odd_region_end.as_usize(), 2),
                        hardware_state,
                    );
                }
                all_regions_configured_correctly_step(even_region, &old, &hardware_state, i);
                all_regions_configured_correctly_step(
                    odd_region,
                    &hardware_state,
                    &hardware_state,
                    i + 1,
                );
            }

            // configures region `i` correctly
            #[flux_rs::sig(fn (i: usize, &PMPUserRegion[@er], hw_state: &strg HardwareState[@og_hw])
                // Note: these pre and post conditions (all_regions_configured) seem silly
                // but we need them because otherwise Flux forgets
                // all state after we return
                requires all_regions_configured_correctly_up_to(i, og_hw) && i % 2 == 0
                ensures hw_state: HardwareState{new_hw:
                    all_regions_configured_correctly_up_to(i + 1, new_hw)
                }
            )]
            fn configure_region(
                i: usize,
                even_region: &PMPUserRegion,
                hardware_state: &mut HardwareState,
            ) {
                let old = hardware_state.snapshot();
                let even_region_start = match even_region.start {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };
                let even_region_end = match even_region.end {
                    Some(r) => r,
                    None => FluxPtr::null(),
                };

                // TODO: check overhead of code
                // Modify the first two pmpcfgX octets for this region:
                let bits = FieldValueU32::<csr::pmpconfig::pmpcfg::Register>::new(
                    0x0000FFFF,
                    0,
                    u32_from_be_bytes(0, 0, even_region.tor.get(), TORUserPMPCFG::OFF().get()),
                );

                super::pmpconfig_modify(i / 2, bits, hardware_state);

                // Set the addresses if the region is enabled:
                if even_region.tor != TORUserPMPCFG::OFF() {
                    super::pmpaddr_set(
                        i * 2 + 0,
                        super::overflowing_shr(even_region_start.as_usize(), 2),
                        hardware_state,
                    );
                    super::pmpaddr_set(
                        i * 2 + 1,
                        super::overflowing_shr(even_region_end.as_usize(), 2),
                        hardware_state,
                    );
                }
                all_regions_configured_correctly_step(even_region, &old, &hardware_state, i);
            }

            #[flux_rs::sig(
                fn (i: usize, core::slice::Iter<PMPUserRegion>[@idx, @len], max_regions: usize, hw_state: &strg HardwareState[@og_hw])
                requires
                    all_regions_configured_correctly_up_to(i, og_hw)
                    && len == max_regions
                    && (idx < len => i == idx && i % 2 == 0)
                    && (idx >= len => all_regions_configured_correctly_up_to(max_regions, og_hw))
                ensures hw_state: HardwareState{new_hw: all_regions_configured_correctly_up_to(max_regions, new_hw)}
            )]
            fn configure_all_regions_tail(
                i: usize,
                mut regions_iter: core::slice::Iter<'_, PMPUserRegion>,
                max_regions: usize,
                hardware_state: &mut HardwareState,
            ) {
                if let Some(even_region) = regions_iter.next() {
                    let odd_region_opt = regions_iter.next();

                    match odd_region_opt {
                        None => {
                            configure_region(i, even_region, hardware_state);
                            configure_all_regions_tail(
                                i + 1,
                                regions_iter,
                                max_regions,
                                hardware_state,
                            );
                        }
                        Some(odd_region) => {
                            configure_region_pair(i, even_region, odd_region, hardware_state);
                            configure_all_regions_tail(
                                i + 2,
                                regions_iter,
                                max_regions,
                                hardware_state,
                            );
                        }
                    }
                }
            }

            // this should be an invariant but it's on a trait so things are weird
            if regions.len() == 0 {
                return Err(());
            }
            let regions_iter = regions.iter();
            // call lemma to establish the original precondition
            all_regions_configured_correctly_base(hardware_state);
            configure_all_regions_tail(0, regions_iter, MPU_REGIONS, hardware_state);

            Ok(())
        }

        fn enable_user_pmp(&self) -> Result<(), ()> {
            // No-op. The SimplePMP does not have any kernel-enforced regions.
            Ok(())
        }

        fn disable_user_pmp(&self) {
            // No-op. The SimplePMP does not have any kernel-enforced regions.
        }
    }

    impl<const AVAILABLE_ENTRIES: usize> fmt::Display for SimplePMP<AVAILABLE_ENTRIES> {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            write!(f, " PMP hardware configuration -- entries: \r\n")?;
            unsafe { super::format_pmp_entries::<AVAILABLE_ENTRIES>(f) }
        }
    }
}
