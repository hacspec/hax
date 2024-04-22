use hax_lib::{ensures, fstar_expr, requires};

const FIELD_MODULUS: i32 = 3329;
const UNSIGNED_FIELD_MODULUS: u32 = FIELD_MODULUS as u32;

#[requires(n == 4 || n == 5 || n == 10 || n == 11 || n == 16)]
#[ensures(|result| result < 2u32.pow(n as u32))]
fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
    let nth_bit = 1 << n;
    let mask = nth_bit - 1;
    fstar_expr!("Rust_primitives.Integers.logand_mask_lemma $value (v $n)");
    value & mask
}

#[
  requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16))]
#[
  ensures(|result| result < 1 << coefficient_bits)]
pub fn compress_unsafe(coefficient_bits: u8, fe: u16) -> i32 {
    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += UNSIGNED_FIELD_MODULUS;
    compressed /= UNSIGNED_FIELD_MODULUS << 1;
    compressed &= (1 << coefficient_bits) - 1;
    fstar_expr!("Rust_primitives.Integers.logand_mask_lemma $compressed (v $coefficient_bits)");
    get_n_least_significant_bits(coefficient_bits, compressed) as i32
}

#[
  requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16))]
#[
  ensures(|result| result < 1 << coefficient_bits)]
pub fn compress(coefficient_bits: u8, fe: u16) -> i32 {
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;
    compressed *= 10_321_340;
    compressed >>= 35;
    compressed &= (1 << coefficient_bits) - 1;
    fstar_expr!("Rust_primitives.Integers.logand_mask_lemma $compressed (v $coefficient_bits)");
    let compressed = compressed as u32;
    get_n_least_significant_bits(coefficient_bits, compressed) as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        fn test(coefficient_bits: u8, fe: u16) {
            let c1 = compress_unsafe(coefficient_bits, fe);
            let c2 = compress(coefficient_bits, fe);
            assert_eq!(c1, c2);
        }

        for bits in [4u8, 5, 10, 11] {
            for fe in 0..3329 {
                test(bits, fe);
            }
        }
    }
}
