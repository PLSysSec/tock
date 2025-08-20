#![allow(unused_variables)]
use crate::mpu::RegionAttributes;
use flux_support::{FieldValueU32, FluxPtr};

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

#[flux_rs::trusted(reason = "math")]
#[flux_rs::sig(fn (n:usize) requires pow2(n) && n >= 2 ensures (n / 2) * 2 == n)]
pub fn theorem_div2_pow2(_n: usize) {}

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

// #[flux_rs::sig(fn (&FieldValueU32<RegionAttributes::Register>[@rasr])
//     requires
//         subregions_enabled_bit_set(rasr.value, 0, 7)
//     ensures
//         enabled_srd_mask(0, 7) == 255 &&
//         disabled_srd_mask(0, 7) == 0
// )]
// pub fn theorem_subregions_enabled_bit_set_0_7(
//     attributes: &FieldValueU32<RegionAttributes::Register>,
// ) {
// }
