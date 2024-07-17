// ANCHOR: square
fn square(x: u8) -> u8 {
    x * x
}
// ANCHOR_END: square

// ANCHOR: square_option
fn square_option(x: u8) -> Option<u8> {
    if x >= 16 {
        None
    } else {
        Some(x * x)
    }
}
// ANCHOR_END: square_option

// ANCHOR: square_requires
#[hax_lib::requires(x < 16)]
fn square_requires(x: u8) -> u8 {
    x * x
}
// ANCHOR_END: square_requires

// ANCHOR: square_ensures
#[hax_lib::requires(x < 16)]
#[hax_lib::ensures(|result| result >= x)]
fn square_ensures(x: u8) -> u8 {
    x * x
}
// ANCHOR_END: square_ensures

// ANCHOR: barrett
type FieldElement = i32;
const FIELD_MODULUS: i32 = 3329;
const BARRETT_SHIFT: i64 = 26;
const BARRETT_R: i64 = 0x4000000; // 2^26
const BARRETT_MULTIPLIER: i64 = 20159; // ⌊(BARRETT_R / FIELD_MODULUS) + 1/2⌋

#[hax_lib::requires((i64::from(value) >= -BARRETT_R && i64::from(value) <= BARRETT_R))]
#[hax_lib::ensures(|result| result > -FIELD_MODULUS && result < FIELD_MODULUS
                     && result %  FIELD_MODULUS ==  value % FIELD_MODULUS)]
fn barrett_reduce(value: i32) -> i32 {
    let t = i64::from(value) * BARRETT_MULTIPLIER;
    let t = t + (BARRETT_R >> 1);

    let quotient = t >> BARRETT_SHIFT;
    let quotient = quotient as i32;

    let sub = quotient * FIELD_MODULUS;

    // Here a lemma to prove that `(quotient * 3329) % 3329 = 0`
    // may have to be called in F*.

    value - sub
}
// ANCHOR_END: barrett

#[hax_lib::exclude]
pub(crate) mod math {
    pub(crate) mod lemmas {
        pub(crate) fn cancel_mul_mod(a: i32, n: i32) {}
    }
}

// ANCHOR: encrypt_decrypt
fn encrypt(plaintext: u32, key: u32) -> u32 {
    plaintext ^ key
}

fn decrypt(ciphertext: u32, key: u32) -> u32 {
    ciphertext ^ key
}
// ANCHOR_END: encrypt_decrypt

// ANCHOR: encrypt_decrypt_identity
#[hax_lib::lemma]
#[hax_lib::requires(true)]
fn encrypt_decrypt_identity(
    key: u32,
    plaintext: u32,
) -> Proof<{ decrypt(encrypt(plaintext, key), key) == plaintext }> {
}
// ANCHOR_END: encrypt_decrypt_identity

// ANCHOR: F3
enum F3 {
    E1,
    E2,
    E3,
}
// ANCHOR_END: F3

// ANCHOR: F
pub const Q: u16 = 2347;

#[hax_lib::attributes]
pub struct F {
    #[hax_lib::refine(v < Q)]
    pub v: u16,
}
// ANCHOR_END: F

// ANCHOR: AddF
use core::ops::Add;

impl Add for F {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            v: (self.v + rhs.v) % Q,
        }
    }
}
// ANCHOR_END: AddF

// fn is_divisible_by(lhs: u32, rhs: u32) -> bool {
//     if rhs == 0 {
//         return false;
//     }

//     lhs % rhs == 0
// }

// fn encrypt(plaintext: u32, key: u32) -> u32 {
//     plaintext ^ key
// }

// fn decrypt(ciphertext: u32, key: u32) -> u32 {
//     ciphertext ^ key
// }

// #[hax_lib::lemma]
// #[hax_lib::requires(true)]
// fn encrypt_decrypt_identity(
//     plaintext: u32,
//     key: u32,
// ) -> Proof<{ decrypt(encrypt(plaintext, key), key) == plaintext }> {
// }
