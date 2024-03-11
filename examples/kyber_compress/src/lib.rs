use hax_lib_macros::{ensures, requires};

const FIELD_MODULUS: i32 = 3329;
const UNSIGNED_FIELD_MODULUS: u32 = FIELD_MODULUS as u32;

#[
  requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16))]
pub fn compress_unsafe(coefficient_bits: u8, fe: u16) -> u32 {
    let mut compressed = (fe as u32) << (coefficient_bits + 1);
    compressed += UNSIGNED_FIELD_MODULUS;
    compressed / (UNSIGNED_FIELD_MODULUS << 1)
}

#[
  requires(
        (coefficient_bits == 4 ||
         coefficient_bits == 5 ||
         coefficient_bits == 10 ||
         coefficient_bits == 11) &&
         fe < (FIELD_MODULUS as u16))]
pub fn compress(coefficient_bits: u8, fe: u16) -> u32 {
    let mut compressed = (fe as u64) << coefficient_bits;
    compressed += 1664 as u64;
    compressed *= 10_321_340;
    compressed >>= 35;
    compressed as u32
}

// /// Values having this type hold a representative 'x' of the Kyber field.
// /// We use 'fe' as a shorthand for this type.
// pub(crate) type FieldElement = i32;

// const MONTGOMERY_SHIFT: u8 = 16;

// #[requires(n == 4 || n == 5 || n == 10 || n == 11 || n == MONTGOMERY_SHIFT)]
// #[ensures(|result| result < 2u32.pow(n as u32))]
// fn get_n_least_significant_bits(n: u8, value: u32) -> u32 {
//     let nth_bit = 1 << n;
//     let mask = nth_bit - 1;
//     value & mask
// }

// #[
//   requires(
//         (coefficient_bits == 4 ||
//          coefficient_bits == 5 ||
//          coefficient_bits == 10 ||
//          coefficient_bits == 11) &&
//          fe < (FIELD_MODULUS as u16))]
// #[
//   ensures(
//      |result| result >= 0 && result < 2i32.pow(coefficient_bits as u32))]
// pub fn compress_ciphertext_coefficient_unsafe(coefficient_bits: u8, fe: u16) -> FieldElement {
//     let compressed = compress_unsafe(coefficient_bits, fe);
//     get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
// }

// #[
//   requires(
//         (coefficient_bits == 4 ||
//          coefficient_bits == 5 ||
//          coefficient_bits == 10 ||
//          coefficient_bits == 11) &&
//          fe < (FIELD_MODULUS as u16))]
// #[
//   ensures(
//      |result| result >= 0 && result < 2i32.pow(coefficient_bits as u32))]
// pub fn compress_ciphertext_coefficient(coefficient_bits: u8, fe: u16) -> FieldElement {
//     debug_assert!(
//         coefficient_bits == 4
//             || coefficient_bits == 5
//             || coefficient_bits == 10
//             || coefficient_bits == 11
//     );
//     debug_assert!(fe <= (FIELD_MODULUS as u16));

//     // This has to be constant time:
//     let mut compressed = (fe as u64) << coefficient_bits;
//     compressed += 1664 as u64;

//     compressed *= 10_321_340;
//     compressed >>= 35;

//     get_n_least_significant_bits(coefficient_bits, compressed as u32) as FieldElement
// }

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
