flux_rs::defs! {
    fn bv32(x:int) -> bitvec<32> { bv_int_to_bv32(x) }
    fn least_five_bits(val: bitvec<32>) -> bitvec<32> { val & 0x1F }

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
}

#[flux_rs::proven_externally]
#[flux_rs::sig(fn (usize[@x], usize[@y], usize[@z]) requires aligned(x, y) && z <= y && pow2(y) && pow2(z) ensures aligned(x, z))]
pub fn theorem_pow2_le_aligned(x: usize, y: usize, z: usize) {}

#[flux_rs::proven_externally]
#[flux_rs::sig(fn (r:usize) requires pow2(r) && r >= 8 ensures octet(r))]
pub fn theorem_pow2_octet(_n: usize) {}

#[flux_rs::proven_externally]
#[flux_rs::sig(fn (n:usize) requires pow2(n) && n >= 4 ensures pow2(n / 2))]
pub fn theorem_pow2_div2_pow2(_n: usize) {}

#[flux_rs::proven_externally]
#[flux_rs::sig(fn (n:usize) requires pow2(n) && n >= 2 ensures (n / 2) * 2 == n)]
pub fn theorem_div2_pow2(_n: usize) {}

#[flux_rs::proven_externally]
#[flux_rs::sig(fn (x: usize, y: usize) requires y >= 32 && pow2(y) && aligned(x, y) ensures least_five_bits(bv32(x)) == 0)]
pub fn theorem_aligned_value_ge32_lowest_five_bits0(x: usize, y: usize) {}


fn main() {}
