use crate::mpu::{CortexMRegion, RegionAttributes};
use flux_support::FieldValueU32;
use flux_support::FluxPtr;
use kernel::platform::mpu;

/* extern specs have to live here because the defs for these specs are defined here */
#[flux_rs::extern_spec]
impl usize {
    #[flux_rs::sig(fn (num: usize) -> usize{r: r >= num && pow2(r) && half_max(r)} requires half_max(num))]
    fn next_power_of_two(self) -> usize;

    #[flux_rs::sig(fn (num: usize) -> bool[pow2(num)])]
    fn is_power_of_two(self) -> bool;

    #[sig(fn(num: usize{num <= u32::MAX}) -> u32{r: r <= 32 && (num > 0 => r < 32) && aligned(num, to_pow2(r)) && (aligned(num, 2) => r > 0)})]
    fn trailing_zeros(self) -> u32;
}

/* a bunch of theorems and proof code */
#[flux_rs::reveal(aligned)]
#[flux_rs::sig(fn (usize[@x], usize[@y]) requires x > 0 && aligned(x, y) ensures x >= y)]
pub fn theorem_aligned_ge(_x: usize, _y: usize) {}

#[flux_rs::reveal(aligned)]
#[flux_rs::sig(fn (usize[@x], usize[@y]) requires x == 0 && y > 0 ensures aligned(x, y))]
pub fn theorem_aligned0(_x: usize, _y: usize) {}

#[flux_rs::reveal(to_pow2)]
#[flux_rs::sig(fn (x: usize) requires x > 0 && x < 32 ensures to_pow2(x) > 1)]
pub fn theorem_to_pow2_gt1(x: usize) {}

#[flux_rs::reveal(pow2, to_pow2)]
#[flux_rs::sig(fn (usize[@n]) requires n < 32 ensures pow2(to_pow2(n)))]
pub fn theorem_to_pow2_is_pow2(_n: usize) {}

#[flux_rs::trusted(reason = "math")]
#[flux_rs::sig(fn (usize[@x], usize[@y], usize[@z]) requires aligned(x, y) && z <= y && pow2(y) && pow2(z) ensures aligned(x, z))]
pub fn theorem_pow2_le_aligned(x: usize, y: usize, z: usize) {}

#[flux_rs::trusted(reason = "math")]
#[flux_rs::sig(fn (r:usize) requires pow2(r) && r >= 8 ensures octet(r))]
pub fn theorem_pow2_octet(_n: usize) {}

#[flux_rs::trusted(reason = "math")]
#[flux_rs::sig(fn (n:usize) requires pow2(n) && n >= 4 ensures pow2(n / 2))]
pub fn theorem_pow2_div2_pow2(_n: usize) {}

#[flux_rs::reveal(octet)]
#[flux_rs::sig(fn (r:usize) requires octet(r) ensures 8 * (r / 8) == r)]
pub fn theorem_div_octet(_n: usize) {}

#[flux_rs::reveal(aligned)]
#[flux_rs::sig(fn (x: usize, y: usize) requires aligned(x, y) ensures aligned(x + y, y))]
pub fn theorem_aligned_plus_aligned_to_is_aligned(_x: usize, _y: usize) {}

#[flux_rs::trusted(reason = "math")]
#[flux_rs::sig(fn (x: usize, y: usize) requires y >= 32 && pow2(y) && aligned(x, y) ensures least_five_bits(bv32(x)) == 0)]
pub fn theorem_aligned_value_ge32_lowest_five_bits0(x: usize, y: usize) {}

#[flux_rs::reveal(octet, first_subregion_from_logical)]
#[flux_rs::sig(fn (rstart: FluxPtr, rsize: usize, astart: FluxPtr, asize: usize)
    requires rstart == astart && rsize == asize && rsize >= 32
    ensures first_subregion_from_logical(rstart, rsize, astart, asize) == 0
)]
pub fn theorem_first_subregion_0(rstart: FluxPtr, rsize: usize, astart: FluxPtr, asize: usize) {}

#[flux_rs::reveal(octet, last_subregion_from_logical)]
#[flux_rs::sig(fn (rstart: FluxPtr, rsize: usize, astart: FluxPtr, asize: usize)
    requires rstart == astart && rsize == asize && rsize >= 32 && octet(rsize)
    ensures last_subregion_from_logical(rstart, rsize, astart, asize) == 7
)]
pub fn theorem_last_subregion_7(rstart: FluxPtr, rsize: usize, astart: FluxPtr, asize: usize) {}

#[flux_rs::reveal(octet, subregions_disabled_bit_set)]
#[flux_rs::sig(fn (&FieldValueU32<RegionAttributes::Register>[@rasr])
    ensures
        enabled_srd_mask(0, 7) == 255 &&
        disabled_srd_mask(0, 7) == 0 &&
        subregions_disabled_bit_set(rasr.value, 0, 7)
)]
pub fn theorem_subregions_disabled_bit_set_0_7(
    attributes: &FieldValueU32<RegionAttributes::Register>,
) {
}

#[flux_rs::sig(fn (&FieldValueU32<RegionAttributes::Register>[@rasr])
    requires
        subregions_enabled_bit_set(rasr.value, 0, 7)
    ensures
        enabled_srd_mask(0, 7) == 255 &&
        disabled_srd_mask(0, 7) == 0
)]
pub fn theorem_subregions_enabled_bit_set_0_7(
    attributes: &FieldValueU32<RegionAttributes::Register>,
) {
}

/* our actual flux defs */

flux_rs::defs! {
    fn half_max(r: int) -> bool { r <= u32::MAX / 2 + 1}

    fn bv32(x:int) -> bitvec<32> { bv_int_to_bv32(x) }
    fn bit(reg: bitvec<32>, power_of_two: bitvec<32>) -> bool { reg & power_of_two != 0}
    fn extract(reg: bitvec<32>, mask:int, offset: int) -> bitvec<32> { (reg & bv32(mask)) >> bv32(offset) }

    fn least_five_bits(val: bitvec<32>) -> bitvec<32> { val & 0x1F }

    // rbar
    fn rbar_valid_bit_set(reg: bitvec<32>) -> bool { bit(reg, 0x10) }
    fn rbar_region_number(reg: bitvec<32>) -> bitvec<32> { reg & 0xF }
    // NOTE: don't shift by 5 because we need the last 5 bits as all 0
    fn rbar_region_start(reg: bitvec<32>) -> bitvec<32> { reg & 0xFFFF_FFE0 }

    // rasr
    fn rasr_global_region_enabled(reg: bitvec<32>) -> bool { bit(reg, 0x1) }
    fn exp2(n:bitvec<32>) -> bitvec<32> { (1 << n) }
    fn size_from_base2(base2_value:bitvec<32>) -> bitvec<32> { exp2 (base2_value + 1) }
    fn rasr_region_size(reg: bitvec<32>) -> bitvec<32> { size_from_base2(extract(reg, 0x0000003e, 1))}

    // fn rasr_region_size(reg: bitvec<32>) -> bitvec<32>      { 1 << (extract(reg, 0x0000003e, 1) + 1) }
    fn rasr_srd(reg: bitvec<32>) -> bitvec<32> { extract(reg, 0x0000_FF00, 8) }
    fn rasr_ap(reg: bitvec<32>) -> bitvec<32> { extract(reg, 0x0700_0000, 24) }
    fn rasr_xn(reg: bitvec<32>) -> bool { bit(reg, 0x10000000) }

    // ctrl
    fn enable(reg:bitvec<32>) -> bool { bit(reg, 0x00000001)}

    fn enabled_srd_mask(first_subregion: bitvec<32>, last_subregion: bitvec<32>) -> bitvec<32> {
        ((bv32(1) << ((last_subregion - first_subregion) + 1)) - 1) << first_subregion
    }

    fn disabled_srd_mask(first_subregion: bitvec<32>, last_subregion: bitvec<32>) -> bitvec<32> {
        bv_xor(0xff, enabled_srd_mask(first_subregion, last_subregion))
    }

    fn perms_match_exactly(rasr: bitvec<32>, perms: mpu::Permissions) -> bool {
        let ap = rasr_ap(rasr);
        let xn = rasr_xn(rasr);
        if perms.r && perms.w && perms.x {
            // read write exec
            ap == 3 && !xn
        } else if perms.r && perms.w && !perms.x {
            // read write
            ap == 3 && xn
        } else if perms.r && !perms.w && perms.x {
            // read exec
            (ap == 2 || ap == 6 || ap == 7) && !xn
        } else if perms.r && !perms.w && !perms.x {
            // read only
            (ap == 2 || ap == 6 || ap == 7) && xn
        } else if !perms.r && !perms.w && perms.x {
            (ap == 0 || ap == 1) && !xn
        } else {
            false
        }
    }

    #[hide]
    fn subregions_enabled_bit_set(rasr: bitvec<32>, first_subregion_no: bitvec<32>, last_subregion_no: bitvec<32>) -> bool {
        let emask = enabled_srd_mask(first_subregion_no, last_subregion_no);
        let srd = rasr_srd(rasr);
        ((srd & emask) == 0)
    }

    #[hide]
    fn subregions_disabled_bit_set(rasr: bitvec<32>, first_subregion_no: bitvec<32>, last_subregion_no: bitvec<32>) -> bool {
        let dmask = disabled_srd_mask(first_subregion_no, last_subregion_no);
        let srd = rasr_srd(rasr);
        ((srd & dmask) == dmask)
    }

    fn subregions_enabled_exactly(rasr: bitvec<32>, first_subregion_no: bitvec<32>, last_subregion_no: bitvec<32>) -> bool {
       subregions_enabled_bit_set(rasr, first_subregion_no, last_subregion_no) &&
       subregions_disabled_bit_set(rasr, first_subregion_no, last_subregion_no)
    }

    #[hide]
    fn to_pow2(n: int) -> int {
        let bv = bv32(n);
        bv_bv32_to_int(bv32(1) << bv)
    }

    #[hide]
    fn pow2(n:int) -> bool {
        let bv = bv32(n);
        n > 0 && (bv & (bv - 1)) == 0
    }

    #[hide]
    fn aligned(x: int, y: int) -> bool {
        x % y == 0
    }

    #[hide]
    fn octet(n: int) -> bool {
        n % 8 == 0
    }

    #[hide]
    fn first_subregion_from_logical(rstart: int, rsize: int, astart: int, asize: int) -> int {
        let subregion_size = rsize / 8;
        (astart - rstart) / subregion_size
    }

    #[hide]
    fn last_subregion_from_logical(rstart: int, rsize: int, astart: int, asize: int) -> int {
        let subregion_size = rsize / 8;
        (((astart + asize) - rstart) / subregion_size) - 1
    }

    fn rnum(region: CortexMRegion) -> int { region.region_no}
    fn rbar(region: CortexMRegion) -> bitvec<32>{ region.rbar.value }
    fn rasr(region: CortexMRegion) -> bitvec<32> { region.rasr.value }


    // region specific
    fn region_overlaps(region1: CortexMRegion, start: int, end: int) -> bool {
        if region1.set {
            let fst_region_start = region1.astart;
            let fst_region_end = region1.astart + region1.asize;
            let snd_region_start = start;
            let snd_region_end = end;
            fst_region_start < snd_region_end && snd_region_start < fst_region_end
        } else {
            false
        }
    }
}
