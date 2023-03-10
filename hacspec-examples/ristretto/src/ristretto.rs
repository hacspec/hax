#![allow(non_snake_case)]
/*
* A hacspec Ristretto implementation modelled on the curve25519_dalek rust library.
* Functions are modelled and tested against their dalek counterparts
* using Quickcheck.
*
* This ensures, with reasonable probability, that the
* these functions and the dalek functions work identically. With this
* assumption, properties about the dalek library can be proven in
* hacspec target languages, and allows hacspec implementations to use
* the defined ristretto operations.
*
* Each internal representation of a point is kept in its Twisted Edwards
* representation, while each encoded point is a byte-string of length 32.
*
* Each public function in the library is based on the IETF-standard for Ristretto
* while all helper functions are private. It is also important to note that
* the internal representation of each point is kept hidden and inaccessible
* to the outside in order to avoid giving incorrect encodings.
*
* For more information see the aforementioned IETF-standard here:
* https://www.ietf.org/archive/id/draft-irtf-cfrg-ristretto255-00.html#name-negative-field-elements/
*
* And the ristretto documentation:
* https://ristretto.group/ristretto.html/
*
* Information about Twisted Edwards curves, see the "Twisted Edwards Curves Revisited" (TECR, henceforth):
* https://eprint.iacr.org/2008/522
*/

use hacspec_lib::*;

// Ristretto points are represented here by Extended Twisted Edwards Coordinates:
// https://eprint.iacr.org/2008/522.pdf
pub type RistrettoPoint = (FieldElement, FieldElement, FieldElement, FieldElement);

type DecodeResult = Result<RistrettoPoint, u8>;

// Ristretto points in their encoded form.
bytes!(RistrettoPointEncoded, 32);

// Bytestrings are used as the input of the one-way-map function.
bytes!(ByteString, 64);

public_nat_mod!(
    type_name: FieldElement,
    type_of_canvas: FieldCanvas,
    bit_size_of_field: 256,
    modulo_value: "7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed"
);

// The Scalar type is used for scaling Ristretto Points.
public_nat_mod!(
    type_name: Scalar,
    type_of_canvas: ScalarCanvas,
    bit_size_of_field: 256,
    modulo_value: "1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed"
);

// === Constants === //

const DECODING_ERROR: u8 = 20u8;

fn P() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x7fu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xedu8
    ))
}

fn D() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x52u8, 0x03u8, 0x6cu8, 0xeeu8, 0x2bu8, 0x6fu8, 0xfeu8, 0x73u8, 0x8cu8, 0xc7u8, 0x40u8,
        0x79u8, 0x77u8, 0x79u8, 0xe8u8, 0x98u8, 0x00u8, 0x70u8, 0x0au8, 0x4du8, 0x41u8, 0x41u8,
        0xd8u8, 0xabu8, 0x75u8, 0xebu8, 0x4du8, 0xcau8, 0x13u8, 0x59u8, 0x78u8, 0xa3u8
    ))
}

fn SQRT_M1() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x2bu8, 0x83u8, 0x24u8, 0x80u8, 0x4fu8, 0xc1u8, 0xdfu8, 0x0bu8, 0x2bu8, 0x4du8, 0x00u8,
        0x99u8, 0x3du8, 0xfbu8, 0xd7u8, 0xa7u8, 0x2fu8, 0x43u8, 0x18u8, 0x06u8, 0xadu8, 0x2fu8,
        0xe4u8, 0x78u8, 0xc4u8, 0xeeu8, 0x1bu8, 0x27u8, 0x4au8, 0x0eu8, 0xa0u8, 0xb0u8
    ))
}

fn INVSQRT_A_MINUS_D() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x78u8, 0x6cu8, 0x89u8, 0x05u8, 0xcfu8, 0xafu8, 0xfcu8, 0xa2u8, 0x16u8, 0xc2u8, 0x7bu8,
        0x91u8, 0xfeu8, 0x01u8, 0xd8u8, 0x40u8, 0x9du8, 0x2fu8, 0x16u8, 0x17u8, 0x5au8, 0x41u8,
        0x72u8, 0xbeu8, 0x99u8, 0xc8u8, 0xfdu8, 0xaau8, 0x80u8, 0x5du8, 0x40u8, 0xeau8
    ))
}

fn SQRT_AD_MINUS_ONE() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x37u8, 0x69u8, 0x31u8, 0xbfu8, 0x2bu8, 0x83u8, 0x48u8, 0xacu8, 0x0fu8, 0x3cu8, 0xfcu8,
        0xc9u8, 0x31u8, 0xf5u8, 0xd1u8, 0xfdu8, 0xafu8, 0x9du8, 0x8eu8, 0x0cu8, 0x1bu8, 0x78u8,
        0x54u8, 0xbdu8, 0x7eu8, 0x97u8, 0xf6u8, 0xa0u8, 0x49u8, 0x7bu8, 0x2eu8, 0x1bu8
    ))
}

fn ONE_MINUS_D_SQ() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x02u8, 0x90u8, 0x72u8, 0xa8u8, 0xb2u8, 0xb3u8, 0xe0u8, 0xd7u8, 0x99u8, 0x94u8, 0xabu8,
        0xddu8, 0xbeu8, 0x70u8, 0xdfu8, 0xe4u8, 0x2cu8, 0x81u8, 0xa1u8, 0x38u8, 0xcdu8, 0x5eu8,
        0x35u8, 0x0fu8, 0xe2u8, 0x7cu8, 0x09u8, 0xc1u8, 0x94u8, 0x5fu8, 0xc1u8, 0x76u8
    ))
}

fn D_MINUS_ONE_SQ() -> FieldElement {
    FieldElement::from_byte_seq_be(&byte_seq!(
        0x59u8, 0x68u8, 0xb3u8, 0x7au8, 0xf6u8, 0x6cu8, 0x22u8, 0x41u8, 0x4cu8, 0xdcu8, 0xd3u8,
        0x2fu8, 0x52u8, 0x9bu8, 0x4eu8, 0xebu8, 0xd2u8, 0x9eu8, 0x4au8, 0x2cu8, 0xb0u8, 0x1eu8,
        0x19u8, 0x99u8, 0x31u8, 0xadu8, 0x5au8, 0xaau8, 0x44u8, 0xedu8, 0x4du8, 0x20u8
    ))
}

// === Special points === //

pub fn BASE_POINT_ENCODED() -> RistrettoPointEncoded {
    RistrettoPointEncoded::from_seq(&byte_seq!(
        0xe2u8, 0xf2u8, 0xaeu8, 0x0au8, 0x6au8, 0xbcu8, 0x4eu8, 0x71u8, 0xa8u8, 0x84u8, 0xa9u8,
        0x61u8, 0xc5u8, 0x00u8, 0x51u8, 0x5fu8, 0x58u8, 0xe3u8, 0x0bu8, 0x6au8, 0xa5u8, 0x82u8,
        0xddu8, 0x8du8, 0xb6u8, 0xa6u8, 0x59u8, 0x45u8, 0xe0u8, 0x8du8, 0x2du8, 0x76u8
    ))
}

pub fn BASE_POINT() -> RistrettoPoint {
    decode(BASE_POINT_ENCODED()).unwrap()
}

pub fn IDENTITY_POINT() -> RistrettoPoint {
    (fe(0), fe(1), fe(1), fe(0))
}

// === Helper functions === //

// Creates a field element from the given literal.
fn fe(x: usize) -> FieldElement {
    FieldElement::from_literal(x as u128)
}

// Checks if a secret byte_seq is greater than or equal to p.
fn geq_p(x: Seq<U8>) -> bool {
    let p_seq = byte_seq!(
        0xedu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8,
        0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0xffu8, 0x7fu8
    );
    let mut res = true;

    for index in 0..p_seq.len() {
        let x_index = x[index].declassify();
        let p_index = p_seq[index].declassify();
        if x_index != p_index {
            res = x_index > p_index;
        }
    }
    res
}

// === Internal Utility Functions === //

// Checks if a given field element is negative. A negative field element is defined as an odd number.
fn is_negative(e: FieldElement) -> bool {
    e % fe(2) == fe(1)
}

// Checks if two given field elements are equal.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn eq(u: FieldElement, v: FieldElement) -> bool {
    u == v
}

// Given a condition it selects u if the condition is true and v if it is false.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn select(u: FieldElement, cond: bool, v: FieldElement) -> FieldElement {
    if cond {
        u
    } else {
        v
    }
}

// Computes the additive negation of the given field element.
fn neg_fe(u: FieldElement) -> FieldElement {
    fe(0) - u
}

// Returns the absolute value of the given field element.
// Should run constant time, which will be possible if FieldElement is changed to Secret Ints
fn abs(u: FieldElement) -> FieldElement {
    select(neg_fe(u), is_negative(u), u)
}

// Computes if the division of the two given field elements is square and returns said square.
// This function has four different cases, for which it returns different values:
// 1: if u, the numerator is 0 it returns (true,0).
// 2: if v, the denominator is 0 it returns (false, 0) as you cannot divide by 0.
// 3: if both are non-zero and u/v is square it returns (true, square).
// 4: if both are non-zero and u/v is not square it returns (false, SQRT_M1*(u/v)).
fn sqrt_ratio_m1(u: FieldElement, v: FieldElement) -> (bool, FieldElement) {
    let v3 = v.pow(2u128) * v;
    let v7 = v3.pow(2u128) * v;
    let mut r = (u * v3) * (u * v7).pow_felem((P() - fe(5)) / fe(8));
    let check = v * r.pow(2u128);

    let correct_sign_sqrt = eq(check, u);
    let flipped_sign_sqrt = eq(check, neg_fe(u));
    let flipped_sign_sqrt_i = eq(check, neg_fe(u) * SQRT_M1());

    let r_prime = SQRT_M1() * r;
    r = select(r_prime, flipped_sign_sqrt || flipped_sign_sqrt_i, r);

    // Choose the nonnegative square root.
    r = abs(r);

    let was_square = correct_sign_sqrt || flipped_sign_sqrt;

    (was_square, r)
}

// A helper function for the one-way-map function.
// Computes a Ristretto point using the given field element.
fn map(t: FieldElement) -> RistrettoPoint {
    let one = fe(1);
    let minus_one = neg_fe(one);
    let r = SQRT_M1() * t.pow(2u128);
    let u = (r + one) * ONE_MINUS_D_SQ();
    let v = (minus_one - r * D()) * (r + D());

    let (was_square, mut s) = sqrt_ratio_m1(u, v);
    let s_prime = neg_fe(abs(s * t));
    s = select(s, was_square, s_prime);
    let c = select(minus_one, was_square, r);

    let N = c * (r - one) * D_MINUS_ONE_SQ() - v;

    let w0 = fe(2) * s * v;
    let w1 = N * SQRT_AD_MINUS_ONE();
    let w2 = one - s.pow(2u128);
    let w3 = one + s.pow(2u128);
    (w0 * w3, w2 * w1, w1 * w3, w0 * w2)
}

// === External Functions === //

/// Takes a uniformly distributed Bytestring of length 64.
/// Returns a pseudo-randomly generated Ristretto point following the defined IETF standard.
/// While this function is not used for any point computations, it is useful for generating points.
pub fn one_way_map(b: ByteString) -> RistrettoPoint {
    let r0_bytes = b.slice(0, 32);
    let r1_bytes = b.slice(32, 32);

    let mut r0_bytes = r0_bytes.declassify();
    let mut r1_bytes = r1_bytes.declassify();

    // The specification states:
    // Set r0 to the low 255 bits of b[ 0..32], taken mod p
    // Set r1 to the low 255 bits of b[32..64], taken mod p
    // Note the low 255 bits. NOT 256 bits! This is why we mod the most significant byte
    r0_bytes[31] = r0_bytes[31] % 128u8;
    r1_bytes[31] = r1_bytes[31] % 128u8;

    let r0 = FieldElement::from_public_byte_seq_le(r0_bytes);
    let r1 = FieldElement::from_public_byte_seq_le(r1_bytes);

    let P1 = map(r0);
    let P2 = map(r1);

    add(P1, P2)
}

/// Encodes the given point
pub fn encode(u: RistrettoPoint) -> RistrettoPointEncoded {
    let (x0, y0, z0, t0) = u;

    let u1 = (z0 + y0) * (z0 - y0);
    let u2 = x0 * y0;

    // Ignore was_square since this is always square
    let (_, invsqrt) = sqrt_ratio_m1(fe(1), u1 * u2.pow(2u128));

    let den1 = invsqrt * u1;
    let den2 = invsqrt * u2;
    let z_inv = den1 * den2 * t0;

    let ix0 = x0 * SQRT_M1();
    let iy0 = y0 * SQRT_M1();
    let enchanted_denominator = den1 * INVSQRT_A_MINUS_D();

    let rotate = is_negative(t0 * z_inv);

    let x = select(iy0, rotate, x0);
    let mut y = select(ix0, rotate, y0);
    let z = z0;
    let den_inv = select(enchanted_denominator, rotate, den2);

    y = select(neg_fe(y), is_negative(x * z_inv), y);

    let s = abs(den_inv * (z - y));

    RistrettoPointEncoded::new().update_start(&s.to_byte_seq_le())
}

/// Decodes the given point in accordance with the IETF standard.
/// Note: There are many byte-strings resulting in incorrect decodings.
/// These all checked for, in accordance with the IETF standard.
/// See https://www.ietf.org/archive/id/draft-irtf-cfrg-ristretto255-decaf448-03.html#name-decode
pub fn decode(u: RistrettoPointEncoded) -> DecodeResult {
    let mut ret = DecodeResult::Err(DECODING_ERROR);

    let s = FieldElement::from_byte_seq_le(u);

    if !geq_p(u.to_le_bytes()) && !is_negative(s) {
        let one = fe(1);
        let ss = s.pow(2u128);
        let u1 = one - ss;
        let u2 = one + ss;
        let u2_sqr = u2.pow(2u128);

        let v = neg_fe(D() * u1.pow(2u128)) - u2_sqr;

        let (was_square, invsqrt) = sqrt_ratio_m1(one, v * u2_sqr);

        let den_x = invsqrt * u2;
        let den_y = invsqrt * den_x * v;

        let x = abs((s + s) * den_x);
        let y = u1 * den_y;
        let t = x * y;

        if !(!was_square || is_negative(t) || y == fe(0)) {
            ret = DecodeResult::Ok((x, y, one, t));
        }
    }
    ret
}

/// Checks that two points are equivalent.
pub fn equals(u: RistrettoPoint, v: RistrettoPoint) -> bool {
    let (x1, y1, _, _) = u;
    let (x2, y2, _, _) = v;
    x1 * y2 == x2 * y1 || y1 * y2 == x1 * x2
}

/// Adds two points together.
// See section 3.2 of the TECR paper
pub fn add(u: RistrettoPoint, v: RistrettoPoint) -> RistrettoPoint {
    let (x1, y1, z1, t1) = u;
    let (x2, y2, z2, t2) = v;

    let a = (y1 - x1) * (y2 + x2);
    let b = (y1 + x1) * (y2 - x2);
    let c = fe(2) * z1 * t2;
    let d = fe(2) * t1 * z2;
    let e = d + c;
    let f = b - a;
    let g = b + a;
    let h = d - c;
    let x3 = e * f;
    let y3 = g * h;
    let t3 = e * h;
    let z3 = f * g;

    (x3, y3, z3, t3)
}

/// Computes the negation of the given point.
// See section 3 of the TECR paper
pub fn neg(u: RistrettoPoint) -> RistrettoPoint {
    let (x1, y1, z1, t1) = u;
    (neg_fe(x1), y1, neg_fe(z1), t1)
}

/// Subtracts v from u, using negation on v and then adding.
pub fn sub(u: RistrettoPoint, v: RistrettoPoint) -> RistrettoPoint {
    add(u, neg(v))
}

/// Doubles the given point. Note, this is faster than
/// adding a point to itself.
// See section 3.3 of TECR
pub fn double(u: RistrettoPoint) -> RistrettoPoint {
    let (x1, y1, z1, _) = u;

    let a = x1.pow(2u128);
    let b = y1.pow(2u128);
    let c = fe(2) * (z1.pow(2u128));
    let h = a + b;
    let e = h - ((x1 + y1).pow(2u128));
    let g = a - b;
    let f = c + g;
    let x2 = e * f;
    let y2 = g * h;
    let t2 = e * h;
    let z2 = f * g;

    (x2, y2, z2, t2)
}

/// Performs scalar multiplication on a point.
pub fn mul(k: Scalar, P: RistrettoPoint) -> RistrettoPoint {
    let mut res = IDENTITY_POINT();
    let mut temp = P;
    for i in 0..256 {
        if k.get_bit(i) == Scalar::from_literal(1u128) {
            res = add(res, temp)
        }
        temp = double(temp)
    }
    res
}
