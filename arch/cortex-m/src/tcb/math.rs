

 use flux_support::FluxPtrU8;

#[flux_rs::trusted(reason = "bitwise arith")]
#[flux_rs::sig(fn(num: u32) -> u32{r: (r < 32) && (num > 1 => r > 0) && (pow2(num) => (bv32(num) == exp2(bv32(r))))})]
pub fn log_base_two(num: u32) -> u32 {
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
pub fn subregion_mask(min_subregion: usize, max_subregion: usize) -> u8 {
    let enabled_mask = ((1 << (max_subregion - min_subregion + 1)) - 1) << min_subregion;
    if enabled_mask == 0 {
        enabled_mask
    } else {
        u8::MAX ^ enabled_mask
    }
}

#[flux_rs::trusted]
#[flux_rs::sig(fn (region_start: FluxPtrU8) -> u32{r: least_five_bits(bv32(region_start)) == 0 => bv32(r) << 5 == bv32(region_start)})]
pub fn region_start_rs32(region_start: FluxPtrU8) -> u32 {
    region_start.as_u32() >> 5
}


#[flux_rs::trusted(reason = "solver hanging")]
#[flux_rs::sig(fn (start: usize, size: usize) -> usize{r: r >= start && aligned(r, size)} requires size > 0 && start + size <= usize::MAX)]
pub fn align(start: usize, size: usize) -> usize {
    start + size - (start % size)
}

#[flux_rs::reveal(aligned)]
#[flux_rs::sig(fn (start: usize, size: usize) -> bool[aligned(start, size)] requires size > 0)]
pub fn is_aligned(start: usize, size: usize) -> bool {
    start % size == 0
}

// VTOCK-TODO: supplementary proof?
#[flux_rs::trusted(reason = "math support (bitwise arithmetic fact)")]
#[flux_rs::sig(fn(n: u32{n < 32}) -> usize{r: r == to_pow2(n) && r > 0 && r <= u32::MAX})]
pub fn power_of_two(n: u32) -> usize {
    1_usize << n
}

#[flux_rs::reveal(valid_size)]
#[flux_rs::sig(fn (x: usize, y: usize) -> bool[valid_size(x + y)] requires y <= u32::MAX)]
pub fn check_valid_size(x: usize, y: usize) -> bool {
    x <= u32::MAX as usize - y
}

#[flux_rs::trusted(reason = "math support (valid usize to u32 cast)")]
#[flux_rs::sig(fn ({ usize[@n] | n <= u32::MAX }) -> u32[n])]
pub fn usize_to_u32(n: usize) -> u32 {
    n as u32
}

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
