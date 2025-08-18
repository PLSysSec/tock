#[allow(unused_imports)]
use crate::mpu::{CortexMRegion, RegionAttributes};
use kernel::platform::mpu;

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
