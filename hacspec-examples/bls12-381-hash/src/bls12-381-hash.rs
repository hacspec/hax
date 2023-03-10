//! Hashing to Elliptic Curves: <https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html>
//! For the BLS12-381 curve.
//! Includes both the Shallue-van de Woestijne method and the Simplified Shallue-van de Woestijne-Ulas for `AB == 0` method
//! for mapping to curve. */

use hacspec_bls12_381::*;
use hacspec_lib::*;
use hacspec_sha256::*;

public_nat_mod!( //Need a bigger canvas than the 384 bits from the Fp natmod from bls12-381 to do a random 512 bit number modulo p
    type_name: FpHash,
    type_of_canvas: FpHashCanvas,
    bit_size_of_field: 512,
    modulo_value: "1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab"
);

array!(ArrFp, 6, U64);

const B_IN_BYTES: usize = 32;
const S_IN_BYTES: usize = 64;
const L: usize = 64;

// (p - 1) / 2
const P_1_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0d0088f51cbff34du64,
        0x258dd3db21a5d66bu64,
        0xb23ba5c279c2895fu64,
        0xb39869507b587b12u64,
        0x0f55ffff58a9ffffu64,
        0xdcff7fffffffd555u64
    ]
));

// (p + 1) / 4
const P_1_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64,
        0x92c6e9ed90d2eb35u64,
        0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64,
        0x07aaffffac54ffffu64,
        0xee7fbfffffffeaabu64
    ]
));

// (p - 3) / 4
const P_3_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0680447a8e5ff9a6u64,
        0x92c6e9ed90d2eb35u64,
        0xd91dd2e13ce144afu64,
        0xd9cc34a83dac3d89u64,
        0x07aaffffac54ffffu64,
        0xee7fbfffffffeaaau64
    ]
));

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.4.1
pub fn expand_message_xmd(msg: &ByteSeq, dst: &ByteSeq, len_in_bytes: usize) -> ByteSeq {
    let ell = (len_in_bytes + B_IN_BYTES - 1) / B_IN_BYTES; // ceil(len_in_bytes / b_in_bytes)
                                                            // must be that ell <= 255
    let dst_prime = dst.push(&U8_from_usize(dst.len())); // DST || I2OSP(len(DST), 1)
    let z_pad = ByteSeq::new(S_IN_BYTES); // I2OSP(0, s_in_bytes)
    let mut l_i_b_str = ByteSeq::new(2);
    l_i_b_str[0] = U8_from_usize(len_in_bytes / 256);
    l_i_b_str[1] = U8_from_usize(len_in_bytes); // I2OSP(len_in_bytes, 2)
    let msg_prime = z_pad
        .concat(msg)
        .concat(&l_i_b_str)
        .concat(&ByteSeq::new(1))
        .concat(&dst_prime); // Z_pad || msg || l_i_b_str || 0 || dst_prime
    let b_0 = ByteSeq::from_seq(&hash(&msg_prime)); // H(msg_prime)
    let mut b_i = ByteSeq::from_seq(&hash(&b_0.push(&U8(1u8)).concat(&dst_prime))); // H(b_0 || 1 || dst_prime)
    let mut uniform_bytes = ByteSeq::from_seq(&b_i);
    for i in 2..(ell + 1) {
        let t = ByteSeq::from_seq(&b_0);
        b_i = ByteSeq::from_seq(&hash(&(t ^ b_i).push(&U8_from_usize(i)).concat(&dst_prime))); //H((b_0 ^ b_(i-1)) || 1 || dst_prime)
        uniform_bytes = uniform_bytes.concat(&b_i);
    }
    uniform_bytes.truncate(len_in_bytes)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.3
pub fn fp_hash_to_field(msg: &ByteSeq, dst: &ByteSeq, count: usize) -> Seq<Fp> {
    let len_in_bytes = count * L; // count * m * L
    let uniform_bytes = expand_message_xmd(msg, dst, len_in_bytes);
    let mut output = Seq::<Fp>::new(count);
    for i in 0..count {
        // m = 1, so no loop
        let elm_offset = L * i; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let u_i =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output[i] = u_i;
    }
    output
}

//Returns true if x is odd and false otherwise
fn fp_sgn0(x: Fp) -> bool {
    x % Fp::TWO() == Fp::ONE()
}

fn fp_is_square(x: Fp) -> bool {
    let c1 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let tv = x.pow_self(c1);
    tv == Fp::ZERO() || tv == Fp::ONE()
}

fn fp_sqrt(x: Fp) -> Fp {
    let c1 = Fp::from_byte_seq_be(&P_1_4.to_be_bytes()); // (p + 1) / 4
    x.pow_self(c1)
}

// y^2 = g(x) = x^3 + 4
fn g1_curve_func(x: Fp) -> Fp {
    x * x * x + Fp::from_literal(4u128)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.1
fn g1_map_to_curve_svdw(u: Fp) -> G1 {
    let z = Fp::ZERO() - Fp::from_literal(3u128);
    let gz = g1_curve_func(z);
    let tv1 = u * u * gz;
    let tv2 = Fp::ONE() + tv1;
    let tv1 = Fp::ONE() - tv1;
    let tv3 = (tv1 * tv2).inv();
    let mut tv4 = fp_sqrt((Fp::ZERO() - gz) * (Fp::from_literal(3u128) * z * z)); // sqrt(-g(Z) * (3 * Z^2 + 4 * A)) #Could be pre-computed
    if fp_sgn0(tv4) {
        tv4 = Fp::ZERO() - tv4;
    }
    let tv5 = u * tv1 * tv3 * tv4;
    let tv6 = (Fp::ZERO() - Fp::from_literal(4u128)) * gz * (Fp::from_literal(3u128) * z * z).inv(); // -4 * g(Z) / (3 * Z^2 + 4 * A) #Could be pre-computed
    let x1 = (Fp::ZERO() - z) * Fp::TWO().inv() - tv5;
    let x2 = (Fp::ZERO() - z) * Fp::TWO().inv() + tv5;
    let x3 = z + tv6 * (tv2 * tv2 * tv3) * (tv2 * tv2 * tv3);
    let x = if fp_is_square(g1_curve_func(x1)) {
        x1
    } else {
        if fp_is_square(g1_curve_func(x2)) {
            x2
        } else {
            x3
        }
    };
    let mut y = fp_sqrt(g1_curve_func(x));
    if fp_sgn0(u) != fp_sgn0(y) {
        y = Fp::ZERO() - y;
    }
    (x, y, false)
}

fn g1_clear_cofactor(x: G1) -> G1 {
    let h_eff = Scalar::from_literal(0xd201000000010001u128);
    g1mul(h_eff, x)
}

//  https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g1_hash_to_curve_svdw(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 2);
    let q0 = g1_map_to_curve_svdw(u[0]);
    let q1 = g1_map_to_curve_svdw(u[1]);
    let r = g1add(q0, q1);
    let p = g1_clear_cofactor(r);
    p
}

pub fn g1_encode_to_curve_svdw(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 1);
    let q = g1_map_to_curve_svdw(u[0]);
    let p = g1_clear_cofactor(q);
    p
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-5.3
pub fn fp2_hash_to_field(msg: &ByteSeq, dst: &ByteSeq, count: usize) -> Seq<Fp2> {
    let len_in_bytes = count * 2 * L; // count * m * L
    let uniform_bytes = expand_message_xmd(msg, dst, len_in_bytes);
    let mut output = Seq::<Fp2>::new(count);
    for i in 0..count {
        // m = 2
        let elm_offset = L * i * 2; // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_1 =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p

        let elm_offset = L * (1 + i * 2); // L * (j + i * m)
        let tv = uniform_bytes.slice(elm_offset, L); //substr(uniform_bytes, elm_offset, L)
        let e_2 =
            Fp::from_byte_seq_be(&FpHash::from_byte_seq_be(&tv).to_byte_seq_be().slice(16, 48)); // OS2IP(tv) mod p
        output[i] = (e_1, e_2);
    }
    output
}

pub fn fp2_sgn0(x: Fp2) -> bool {
    let (x0, x1) = x;
    let sign_0 = fp_sgn0(x0);
    let zero_0 = x0 == Fp::ZERO();
    let sign_1 = fp_sgn0(x1);
    sign_0 || (zero_0 && sign_1)
}

pub fn fp2_is_square(x: Fp2) -> bool {
    let c1 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let (x1, x2) = x;
    let tv1 = x1 * x1;
    let tv2 = x2 * x2;
    let tv1 = tv1 + tv2;
    let tv1 = tv1.pow_self(c1);
    let neg1 = Fp::ZERO() - Fp::ONE();
    tv1 != neg1
}

fn fp2exp(n: Fp2, k: Fp) -> Fp2 {
    let mut c = fp2fromfp(Fp::ONE());
    for i in 0..381 {
        c = fp2mul(c, c);
        if k.bit(380 - i) {
            c = fp2mul(c, n);
        }
    }
    c
}

// Algorithm 9 from https://eprint.iacr.org/2012/685.pdf
pub fn fp2_sqrt(a: Fp2) -> Fp2 {
    let c1 = Fp::from_byte_seq_be(&P_3_4.to_be_bytes()); // (p - 3) / 4
    let c2 = Fp::from_byte_seq_be(&P_1_2.to_be_bytes()); // (p - 1) / 2
    let a1 = fp2exp(a, c1); // a ^ ((q-3)/4)
    let alpha = fp2mul(a1, fp2mul(a1, a)); // a1(a1(a))
                                           //let a0 = fp2mul(fp2conjugate(alpha), alpha); //alpha^q * alpha
    let x0 = fp2mul(a1, a); //a1 * a
    let neg1 = (Fp::ZERO() - Fp::ONE(), Fp::ZERO());
    let b = fp2exp(fp2add(fp2fromfp(Fp::ONE()), alpha), c2); // (1 + alpha) ^ ((q-1)/2)
    if alpha == neg1 {
        fp2mul((Fp::ZERO(), Fp::ONE()), x0) // i * x0
    } else {
        fp2mul(b, x0) // b * x0
    }
}

// y^2 = g(x) = x^3 + 4(1 + I)
pub fn g2_curve_func(x: Fp2) -> Fp2 {
    fp2add(
        fp2mul(x, fp2mul(x, x)),
        (Fp::from_literal(4u128), Fp::from_literal(4u128)),
    )
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.1
fn g2_map_to_curve_svdw(u: Fp2) -> G2 {
    let z = fp2neg(fp2fromfp(Fp::ONE())); //-1
    let gz = g2_curve_func(z); //g(z)
    let tv1 = fp2mul(fp2mul(u, u), gz); // u^2 * g(z)
    let tv2 = fp2add(fp2fromfp(Fp::ONE()), tv1); // 1 + tv1
    let tv1 = fp2sub(fp2fromfp(Fp::ONE()), tv1); // 1 - tv1
    let tv3 = fp2inv(fp2mul(tv1, tv2)); // inv0(tv1 * tv2)
    let mut tv4 = fp2_sqrt(fp2mul(
        fp2neg(gz),
        fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(z, z)),
    )); // sqrt(-g(Z) * (3 * Z^2)) #Could be pre-computed
    if fp2_sgn0(tv4) {
        tv4 = fp2neg(tv4);
    }
    let tv5 = fp2mul(fp2mul(fp2mul(u, tv1), tv3), tv4); //u * tv1 * tv3 * tv4
    let tv6 = fp2mul(
        fp2mul(fp2neg(fp2fromfp(Fp::from_literal(4u128))), gz),
        fp2inv(fp2mul(fp2fromfp(Fp::from_literal(3u128)), fp2mul(z, z))),
    ); // -4 * g(Z) / (3 * Z^2) #Could be pre-computed
    let x1 = fp2sub(fp2mul(fp2neg(z), fp2inv(fp2fromfp(Fp::TWO()))), tv5); // -Z / 2 - tv5
    let x2 = fp2add(fp2mul(fp2neg(z), fp2inv(fp2fromfp(Fp::TWO()))), tv5); // -Z / 2 - tv5
    let tv7 = fp2mul(fp2mul(tv2, tv2), tv3);
    let x3 = fp2add(z, fp2mul(tv6, fp2mul(tv7, tv7))); // z + tv6 * (tv2^2 * tv3)^2
    let x = if fp2_is_square(g2_curve_func(x1)) {
        x1
    } else {
        if fp2_is_square(g2_curve_func(x2)) {
            x2
        } else {
            x3
        }
    };
    let mut y = fp2_sqrt(g2_curve_func(x)); //sqrt(g(x))
    if fp2_sgn0(u) != fp2_sgn0(y) {
        y = fp2neg(y);
    }
    (x, y, false)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-G.3
fn psi(p: G2) -> G2 {
    let c1 = fp2inv(fp2exp(
        (Fp::ONE(), Fp::ONE()),
        (Fp::ZERO() - Fp::ONE()) * (Fp::from_literal(3u128)).inv(),
    )); // 1 / (1 + I)^((p - 1) / 3) #Could be pre-computed
    let c2 = fp2inv(fp2exp(
        (Fp::ONE(), Fp::ONE()),
        (Fp::ZERO() - Fp::ONE()) * (Fp::TWO()).inv(),
    )); // 1 / (1 + I)^((p - 1) / 2) #Could be pre-computed
    let (x, y, inf) = p;
    let qx = fp2mul(c1, fp2conjugate(x));
    let qy = fp2mul(c2, fp2conjugate(y));
    (qx, qy, inf)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-G.3
fn g2_clear_cofactor(p: G2) -> G2 {
    let c1 = Scalar::from_literal(0xd201000000010000u128);
    let t1 = g2mul(c1, p);
    let t1 = g2neg(t1); //neg since c1 is actually negative
    let t2 = psi(p);
    let t3 = g2double(p);
    let t3 = psi(psi(t3));
    let t3 = g2add(t3, g2neg(t2));
    let t2 = g2add(t1, t2);
    let t2 = g2mul(c1, t2);
    let t2 = g2neg(t2); //neg since c1 is actually negative
    let t3 = g2add(t3, t2);
    let t3 = g2add(t3, g2neg(t1));
    let q = g2add(t3, g2neg(p));
    q
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g2_hash_to_curve_svdw(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 2);
    let q0 = g2_map_to_curve_svdw(u[0]);
    let q1 = g2_map_to_curve_svdw(u[1]);
    let r = g2add(q0, q1);
    let p = g2_clear_cofactor(r);
    p
}

pub fn g2_encode_to_curve_svdw(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 1);
    let q = g2_map_to_curve_svdw(u[0]);
    let p = g2_clear_cofactor(q);
    p
}

// Simplified SWU for AB == 0 method
// Hash to G1 - Constants

#[rustfmt::skip]
const G1_ISO_A: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x00144698a3b8e943u64, 0x3d693a02c96d4982u64, 0xb0ea985383ee66a8u64,
        0xd8e8981aefd881acu64, 0x98936f8da0e0f97fu64, 0x5cf428082d584c1du64
    ]
));
#[rustfmt::skip]
const G1_ISO_B: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x12e2908d11688030u64, 0x018b12e8753eee3bu64, 0x2016c1f0f24f4070u64,
        0xa0b9c14fcef35ef5u64, 0x5a23215a316ceaa5u64, 0xd1cc48e98e172be0u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x11a05f2b1e833340u64, 0xb809101dd9981585u64, 0x6b303e88a2d7005fu64,
        0xf2627b56cdb4e2c8u64, 0x5610c2d5f2e62d6eu64, 0xaeac1662734649b7u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_1: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x17294ed3e943ab2fu64, 0x0588bab22147a81cu64, 0x7c17e75b2f6a8417u64,
        0xf565e33c70d1e86bu64, 0x4838f2a6f318c356u64, 0xe834eef1b3cb83bbu64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0d54005db97678ecu64, 0x1d1048c5d10a9a1bu64, 0xce032473295983e5u64,
        0x6878e501ec68e25cu64, 0x958c3e3d2a09729fu64, 0xe0179f9dac9edcb0u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_3: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1778e7166fcc6db7u64, 0x4e0609d307e55412u64, 0xd7f5e4656a8dbf25u64,
        0xf1b33289f1b33083u64, 0x5336e25ce3107193u64, 0xc5b388641d9b6861u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0e99726a3199f443u64, 0x6642b4b3e4118e54u64, 0x99db995a1257fb3fu64,
        0x086eeb65982fac18u64, 0x985a286f301e77c4u64, 0x51154ce9ac8895d9u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_5: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1630c3250d7313ffu64, 0x01d1201bf7a74ab5u64, 0xdb3cb17dd952799bu64,
        0x9ed3ab9097e68f90u64, 0xa0870d2dcae73d19u64, 0xcd13c1c66f652983u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_6: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0d6ed6553fe44d29u64, 0x6a3726c38ae652bfu64, 0xb11586264f0f8ce1u64,
        0x9008e218f9c86b2au64, 0x8da25128c1052ecau64, 0xddd7f225a139ed84u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_7: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x17b81e7701abdbe2u64, 0xe8743884d1117e53u64, 0x356de5ab275b4db1u64,
        0xa682c62ef0f27533u64, 0x39b7c8f8c8f475afu64, 0x9ccb5618e3f0c88eu64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_8: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x080d3cf1f9a78fc4u64, 0x7b90b33563be990du64, 0xc43b756ce79f5574u64,
        0xa2c596c928c5d1deu64, 0x4fa295f296b74e95u64, 0x6d71986a8497e317u64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_9: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x169b1f8e1bcfa7c4u64, 0x2e0c37515d138f22u64, 0xdd2ecb803a0c5c99u64,
        0x676314baf4bb1b7fu64, 0xa3190b2edc032779u64, 0x7f241067be390c9eu64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_10: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x10321da079ce07e2u64, 0x72d8ec09d2565b0du64, 0xfa7dccdde6787f96u64,
        0xd50af36003b14866u64, 0xf69b771f8c285decu64, 0xca67df3f1605fb7bu64
    ]
));
#[rustfmt::skip]
const G1_XNUM_K_11: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x06e08c248e260e70u64, 0xbd1e962381edee3du64, 0x31d79d7e22c837bcu64,
        0x23c0bf1bc24c6b68u64, 0xc24b1b80b64d391fu64, 0xa9c8ba2e8ba2d229u64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x08ca8d548cff19aeu64, 0x18b2e62f4bd3fa6fu64, 0x01d5ef4ba35b48bau64,
        0x9c9588617fc8ac62u64, 0xb558d681be343df8u64, 0x993cf9fa40d21b1cu64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_1: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x12561a5deb559c43u64, 0x48b4711298e53636u64, 0x7041e8ca0cf0800cu64,
        0x0126c2588c48bf57u64, 0x13daa8846cb026e9u64, 0xe5c8276ec82b3bffu64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0b2962fe57a3225eu64, 0x8137e629bff2991fu64, 0x6f89416f5a718cd1u64,
        0xfca64e00b11aceacu64, 0xd6a3d0967c94fedcu64, 0xfcc239ba5cb83e19u64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_3: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x03425581a58ae2feu64, 0xc83aafef7c40eb54u64, 0x5b08243f16b16551u64,
        0x54cca8abc28d6fd0u64, 0x4976d5243eecf5c4u64, 0x130de8938dc62cd8u64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x13a8e162022914a8u64, 0x0a6f1d5f43e7a07du64, 0xffdfc759a12062bbu64,
        0x8d6b44e833b306dau64, 0x9bd29ba81f35781du64, 0x539d395b3532a21eu64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_5: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0e7355f8e4e667b9u64, 0x55390f7f0506c6e9u64, 0x395735e9ce9cad4du64,
        0x0a43bcef24b8982fu64, 0x7400d24bc4228f11u64, 0xc02df9a29f6304a5u64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_6: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0772caacf1693619u64, 0x0f3e0c63e0596721u64, 0x570f5799af53a189u64,
        0x4e2e073062aede9cu64, 0xea73b3538f0de06cu64, 0xec2574496ee84a3au64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_7: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x14a7ac2a9d64a8b2u64, 0x30b3f5b074cf0199u64, 0x6e7f63c21bca68a8u64,
        0x1996e1cdf9822c58u64, 0x0fa5b9489d11e2d3u64, 0x11f7d99bbdcc5a5eu64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_8: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0a10ecf6ada54f82u64, 0x5e920b3dafc7a3ccu64, 0xe07f8d1d7161366bu64,
        0x74100da67f398835u64, 0x03826692abba4370u64, 0x4776ec3a79a1d641u64
    ]
));
#[rustfmt::skip]
const G1_XDEN_K_9: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x095fc13ab9e92ad4u64, 0x476d6e3eb3a56680u64, 0xf682b4ee96f7d037u64,
        0x76df533978f31c15u64, 0x93174e4b4b786500u64, 0x2d6384d168ecdd0au64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x090d97c81ba24ee0u64, 0x259d1f094980dcfau64, 0x11ad138e48a86952u64,
        0x2b52af6c956543d3u64, 0xcd0c7aee9b3ba3c2u64, 0xbe9845719707bb33u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_1: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x134996a104ee5811u64, 0xd51036d776fb4683u64, 0x1223e96c254f383du64,
        0x0f906343eb67ad34u64, 0xd6c56711962fa8bfu64, 0xe097e75a2e41c696u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x00cc786baa966e66u64, 0xf4a384c86a3b4994u64, 0x2552e2d658a31ce2u64,
        0xc344be4b91400da7u64, 0xd26d521628b00523u64, 0xb8dfe240c72de1f6u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_3: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x01f86376e8981c21u64, 0x7898751ad8746757u64, 0xd42aa7b90eeb791cu64,
        0x09e4a3ec03251cf9u64, 0xde405aba9ec61decu64, 0xa6355c77b0e5f4cbu64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x08cc03fdefe0ff13u64, 0x5caf4fe2a21529c4u64, 0x195536fbe3ce50b8u64,
        0x79833fd221351adcu64, 0x2ee7f8dc099040a8u64, 0x41b6daecf2e8fedbu64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_5: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x16603fca40634b6au64, 0x2211e11db8f0a6a0u64, 0x74a7d0d4afadb7bdu64,
        0x76505c3d3ad5544eu64, 0x203f6326c95a8072u64, 0x99b23ab13633a5f0u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_6: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x04ab0b9bcfac1bbcu64, 0xb2c977d027796b3cu64, 0xe75bb8ca2be184cbu64,
        0x5231413c4d634f37u64, 0x47a87ac2460f415eu64, 0xc961f8855fe9d6f2u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_7: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0987c8d5333ab86fu64, 0xde9926bd2ca6c674u64, 0x170a05bfe3bdd81fu64,
        0xfd038da6c26c8426u64, 0x42f64550fedfe935u64, 0xa15e4ca31870fb29u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_8: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x09fc4018bd96684bu64, 0xe88c9e221e4da1bbu64, 0x8f3abd16679dc26cu64,
        0x1e8b6e6a1f20cabeu64, 0x69d65201c78607a3u64, 0x60370e577bdba587u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_9: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0e1bba7a1186bdb5u64, 0x223abde7ada14a23u64, 0xc42a0ca7915af6feu64,
        0x06985e7ed1e4d43bu64, 0x9b3f7055dd4eba6fu64, 0x2bafaaebca731c30u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_10: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x19713e47937cd1beu64, 0x0dfd0b8f1d43fb93u64, 0xcd2fcbcb6caf493fu64,
        0xd1183e416389e610u64, 0x31bf3a5cce3fbafcu64, 0xe813711ad011c132u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_11: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x18b46a908f36f6deu64, 0xb918c143fed2edccu64, 0x523559b8aaf0c246u64,
        0x2e6bfe7f911f6432u64, 0x49d9cdf41b44d606u64, 0xce07c8a4d0074d8eu64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_12: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0b182cac101b9399u64, 0xd155096004f53f44u64, 0x7aa7b12a3426b08eu64,
        0xc02710e807b4633fu64, 0x06c851c1919211f2u64, 0x0d4c04f00b971ef8u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_13: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0245a394ad1eca9bu64, 0x72fc00ae7be315dcu64, 0x757b3b080d4c1580u64,
        0x13e6632d3c40659cu64, 0xc6cf90ad1c232a64u64, 0x42d9d3f5db980133u64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_14: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x05c129645e44cf11u64, 0x02a159f748c4a3fcu64, 0x5e673d81d7e86568u64,
        0xd9ab0f5d396a7ce4u64, 0x6ba1049b6579afb7u64, 0x866b1e715475224bu64
    ]
));
#[rustfmt::skip]
const G1_YNUM_K_15: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x15e6be4e990f03ceu64, 0x4ea50b3b42df2eb5u64, 0xcb181d8f84965a39u64,
        0x57add4fa95af01b2u64, 0xb665027efec01c77u64, 0x04b456be69c8b604u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x16112c4c3a9c98b2u64, 0x52181140fad0eae9u64, 0x601a6de578980be6u64,
        0xeec3232b5be72e7au64, 0x07f3688ef60c206du64, 0x01479253b03663c1u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_1: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1962d75c2381201eu64, 0x1a0cbd6c43c348b8u64, 0x85c84ff731c4d59cu64,
        0xa4a10356f453e01fu64, 0x78a4260763529e35u64, 0x32f6102c2e49a03du64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_2: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x058df3306640da27u64, 0x6faaae7d6e8eb157u64, 0x78c4855551ae7f31u64,
        0x0c35a5dd279cd2ecu64, 0xa6757cd636f96f89u64, 0x1e2538b53dbf67f2u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_3: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x16b7d288798e5395u64, 0xf20d23bf89edb4d1u64, 0xd115c5dbddbcd30eu64,
        0x123da489e726af41u64, 0x727364f2c28297adu64, 0xa8d26d98445f5416u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_4: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0be0e079545f43e4u64, 0xb00cc912f8228ddcu64, 0xc6d19c9f0f69bbb0u64,
        0x542eda0fc9dec916u64, 0xa20b15dc0fd2ededu64, 0xda39142311a5001du64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_5: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x08d9e5297186db2du64, 0x9fb266eaac783182u64, 0xb70152c65550d881u64,
        0xc5ecd87b6f0f5a64u64, 0x49f38db9dfa9cce2u64, 0x02c6477faaf9b7acu64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_6: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x166007c08a99db2fu64, 0xc3ba8734ace9824bu64, 0x5eecfdfa8d0cf8efu64,
        0x5dd365bc400a0051u64, 0xd5fa9c01a58b1fb9u64, 0x3d1a1399126a775cu64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_7: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x16a3ef08be3ea7eau64, 0x03bcddfabba6ff6eu64, 0xe5a4375efa1f4fd7u64,
        0xfeb34fd206357132u64, 0xb920f5b00801dee4u64, 0x60ee415a15812ed9u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_8: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1866c8ed336c6123u64, 0x1a1be54fd1d74cc4u64, 0xf9fb0ce4c6af5920u64,
        0xabc5750c4bf39b48u64, 0x52cfe2f7bb924883u64, 0x6b233d9d55535d4au64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_9: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x167a55cda70a6e1cu64, 0xea820597d94a8490u64, 0x3216f763e13d87bbu64,
        0x5308592e7ea7d4fbu64, 0xc7385ea3d529b35eu64, 0x346ef48bb8913f55u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_10: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x04d2f259eea405bdu64, 0x48f010a01ad2911du64, 0x9c6dd039bb61a629u64,
        0x0e591b36e636a5c8u64, 0x71a5c29f4f830604u64, 0x00f8b49cba8f6aa8u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_11: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0accbb67481d033fu64, 0xf5852c1e48c50c47u64, 0x7f94ff8aefce42d2u64,
        0x8c0f9a88cea79135u64, 0x16f968986f7ebbeau64, 0x9684b529e2561092u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_12: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0ad6b9514c767fe3u64, 0xc3613144b45f1496u64, 0x543346d98adf0226u64,
        0x7d5ceef9a00d9b86u64, 0x93000763e3b90ac1u64, 0x1e99b138573345ccu64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_13: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x02660400eb2e4f3bu64, 0x628bdd0d53cd76f2u64, 0xbf565b94e72927c1u64,
        0xcb748df27942480eu64, 0x420517bd8714cc80u64, 0xd1fadc1326ed06f7u64
    ]
));
#[rustfmt::skip]
const G1_YDEN_K_14: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x0e0fa1d816ddc03eu64, 0x6b24255e0d7819c1u64, 0x71c40f65e273b853u64,
        0x324efcd6356caa20u64, 0x5ca2f570f1349780u64, 0x4415473a1d634b8fu64
    ]
));

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.2
fn g1_simple_swu_iso(u: Fp) -> (Fp, Fp) {
    let z = Fp::from_literal(11u128);
    let a = Fp::from_byte_seq_be(&G1_ISO_A.to_be_bytes());
    let b = Fp::from_byte_seq_be(&G1_ISO_B.to_be_bytes());
    let tv1 = (z * z * u.exp(4u32) + z * u * u).inv(); // inv0(z^2 * u^4 + z * u^2)
    let mut x1 = ((Fp::ZERO() - b) * a.inv()) * (Fp::ONE() + tv1); // (-B / A) * (1 + tv1)
    if tv1 == Fp::ZERO() {
        x1 = b * (z * a).inv(); // If tv1 == 0, set x1 = B / (Z * A)
    };
    let gx1 = x1.exp(3u32) + a * x1 + b; // x1^3 + A * x1 + B
    let x2 = z * u * u * x1; // Z * u^2 * x1
    let gx2 = x2.exp(3u32) + a * x2 + b; // x2^3 + A * x2 + B
    let (x, mut y) = if fp_is_square(gx1) {
        (x1, fp_sqrt(gx1)) // If is_square(gx1), set x = x1 and y = sqrt(gx1)
    } else {
        (x2, fp_sqrt(gx2)) // Else set x = x2 and y = sqrt(gx2)
    };
    if fp_sgn0(u) != fp_sgn0(y) {
        y = Fp::ZERO() - y; // If sgn0(u) != sgn0(y), set y = -y
    };
    (x, y)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-E.2
fn g1_isogeny_map(x: Fp, y: Fp) -> G1 {
    // xnum_k
    let mut xnum_k = Seq::<Fp>::new(12);
    xnum_k[0usize] = Fp::from_byte_seq_be(&G1_XNUM_K_0.to_be_bytes());
    xnum_k[1usize] = Fp::from_byte_seq_be(&G1_XNUM_K_1.to_be_bytes());
    xnum_k[2usize] = Fp::from_byte_seq_be(&G1_XNUM_K_2.to_be_bytes());
    xnum_k[3usize] = Fp::from_byte_seq_be(&G1_XNUM_K_3.to_be_bytes());
    xnum_k[4usize] = Fp::from_byte_seq_be(&G1_XNUM_K_4.to_be_bytes());
    xnum_k[5usize] = Fp::from_byte_seq_be(&G1_XNUM_K_5.to_be_bytes());
    xnum_k[6usize] = Fp::from_byte_seq_be(&G1_XNUM_K_6.to_be_bytes());
    xnum_k[7usize] = Fp::from_byte_seq_be(&G1_XNUM_K_7.to_be_bytes());
    xnum_k[8usize] = Fp::from_byte_seq_be(&G1_XNUM_K_8.to_be_bytes());
    xnum_k[9usize] = Fp::from_byte_seq_be(&G1_XNUM_K_9.to_be_bytes());
    xnum_k[10usize] = Fp::from_byte_seq_be(&G1_XNUM_K_10.to_be_bytes());
    xnum_k[11usize] = Fp::from_byte_seq_be(&G1_XNUM_K_11.to_be_bytes());

    // xden_k
    let mut xden_k = Seq::<Fp>::new(10);
    xden_k[0usize] = Fp::from_byte_seq_be(&G1_XDEN_K_0.to_be_bytes());
    xden_k[1usize] = Fp::from_byte_seq_be(&G1_XDEN_K_1.to_be_bytes());
    xden_k[2usize] = Fp::from_byte_seq_be(&G1_XDEN_K_2.to_be_bytes());
    xden_k[3usize] = Fp::from_byte_seq_be(&G1_XDEN_K_3.to_be_bytes());
    xden_k[4usize] = Fp::from_byte_seq_be(&G1_XDEN_K_4.to_be_bytes());
    xden_k[5usize] = Fp::from_byte_seq_be(&G1_XDEN_K_5.to_be_bytes());
    xden_k[6usize] = Fp::from_byte_seq_be(&G1_XDEN_K_6.to_be_bytes());
    xden_k[7usize] = Fp::from_byte_seq_be(&G1_XDEN_K_7.to_be_bytes());
    xden_k[8usize] = Fp::from_byte_seq_be(&G1_XDEN_K_8.to_be_bytes());
    xden_k[9usize] = Fp::from_byte_seq_be(&G1_XDEN_K_9.to_be_bytes());

    // ynum_k
    let mut ynum_k = Seq::<Fp>::new(16);
    ynum_k[0usize] = Fp::from_byte_seq_be(&G1_YNUM_K_0.to_be_bytes());
    ynum_k[1usize] = Fp::from_byte_seq_be(&G1_YNUM_K_1.to_be_bytes());
    ynum_k[2usize] = Fp::from_byte_seq_be(&G1_YNUM_K_2.to_be_bytes());
    ynum_k[3usize] = Fp::from_byte_seq_be(&G1_YNUM_K_3.to_be_bytes());
    ynum_k[4usize] = Fp::from_byte_seq_be(&G1_YNUM_K_4.to_be_bytes());
    ynum_k[5usize] = Fp::from_byte_seq_be(&G1_YNUM_K_5.to_be_bytes());
    ynum_k[6usize] = Fp::from_byte_seq_be(&G1_YNUM_K_6.to_be_bytes());
    ynum_k[7usize] = Fp::from_byte_seq_be(&G1_YNUM_K_7.to_be_bytes());
    ynum_k[8usize] = Fp::from_byte_seq_be(&G1_YNUM_K_8.to_be_bytes());
    ynum_k[9usize] = Fp::from_byte_seq_be(&G1_YNUM_K_9.to_be_bytes());
    ynum_k[10usize] = Fp::from_byte_seq_be(&G1_YNUM_K_10.to_be_bytes());
    ynum_k[11usize] = Fp::from_byte_seq_be(&G1_YNUM_K_11.to_be_bytes());
    ynum_k[12usize] = Fp::from_byte_seq_be(&G1_YNUM_K_12.to_be_bytes());
    ynum_k[13usize] = Fp::from_byte_seq_be(&G1_YNUM_K_13.to_be_bytes());
    ynum_k[14usize] = Fp::from_byte_seq_be(&G1_YNUM_K_14.to_be_bytes());
    ynum_k[15usize] = Fp::from_byte_seq_be(&G1_YNUM_K_15.to_be_bytes());

    // yden_k
    let mut yden_k = Seq::<Fp>::new(15);
    yden_k[0usize] = Fp::from_byte_seq_be(&G1_YDEN_K_0.to_be_bytes());
    yden_k[1usize] = Fp::from_byte_seq_be(&G1_YDEN_K_1.to_be_bytes());
    yden_k[2usize] = Fp::from_byte_seq_be(&G1_YDEN_K_2.to_be_bytes());
    yden_k[3usize] = Fp::from_byte_seq_be(&G1_YDEN_K_3.to_be_bytes());
    yden_k[4usize] = Fp::from_byte_seq_be(&G1_YDEN_K_4.to_be_bytes());
    yden_k[5usize] = Fp::from_byte_seq_be(&G1_YDEN_K_5.to_be_bytes());
    yden_k[6usize] = Fp::from_byte_seq_be(&G1_YDEN_K_6.to_be_bytes());
    yden_k[7usize] = Fp::from_byte_seq_be(&G1_YDEN_K_7.to_be_bytes());
    yden_k[8usize] = Fp::from_byte_seq_be(&G1_YDEN_K_8.to_be_bytes());
    yden_k[9usize] = Fp::from_byte_seq_be(&G1_YDEN_K_9.to_be_bytes());
    yden_k[10usize] = Fp::from_byte_seq_be(&G1_YDEN_K_10.to_be_bytes());
    yden_k[11usize] = Fp::from_byte_seq_be(&G1_YDEN_K_11.to_be_bytes());
    yden_k[12usize] = Fp::from_byte_seq_be(&G1_YDEN_K_12.to_be_bytes());
    yden_k[13usize] = Fp::from_byte_seq_be(&G1_YDEN_K_13.to_be_bytes());
    yden_k[14usize] = Fp::from_byte_seq_be(&G1_YDEN_K_14.to_be_bytes());

    // Computation

    // x_num = k_(1,11) * x^11 + k_(1,10) * x^10 + k_(1,9) * x^9 + ... + k_(1,0)
    let mut xnum = Fp::ZERO();
    let mut xx = Fp::ONE();
    for i in 0..xnum_k.len() {
        xnum = xnum + xx * xnum_k[i];
        xx = xx * x;
    }

    // x_den = x^10 + k_(2,9) * x^9 + k_(2,8) * x^8 + ... + k_(2,0)
    let mut xden = Fp::ZERO();
    let mut xx = Fp::ONE();
    for i in 0..xden_k.len() {
        xden = xden + xx * xden_k[i];
        xx = xx * x;
    }
    xden = xden + xx;

    // y_num = k_(3,15) * x^15 + k_(3,14) * x^14 + k_(3,13) * x^13 + ... + k_(3,0)
    let mut ynum = Fp::ZERO();
    let mut xx = Fp::ONE();
    for i in 0..ynum_k.len() {
        ynum = ynum + xx * ynum_k[i];
        xx = xx * x;
    }

    // y_den = x^15 + k_(4,14) * x^14 + k_(4,13) * x^13 + ... + k_(4,0)
    let mut yden = Fp::ZERO();
    let mut xx = Fp::ONE();
    for i in 0..yden_k.len() {
        yden = yden + xx * yden_k[i];
        xx = xx * x;
    }
    yden = yden + xx;

    // xr = x_num / x_den
    let xr = xnum * xden.inv();

    // yr = y * y_num / y_den
    let yr = y * ynum * yden.inv();

    // if xden or yden is zero return point at infinity
    let mut inf = false;
    if xden == Fp::ZERO() || yden == Fp::ZERO() {
        inf = true;
    }

    (xr, yr, inf)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.3
fn g1_map_to_curve_sswu(u: Fp) -> G1 {
    let (xp, yp) = g1_simple_swu_iso(u);
    let p = g1_isogeny_map(xp, yp);
    p
}

//  https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g1_hash_to_curve_sswu(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 2);
    let q0 = g1_map_to_curve_sswu(u[0]);
    let q1 = g1_map_to_curve_sswu(u[1]);
    let r = g1add(q0, q1);
    let p = g1_clear_cofactor(r);
    p
}

pub fn g1_encode_to_curve_sswu(msg: &ByteSeq, dst: &ByteSeq) -> G1 {
    let u = fp_hash_to_field(msg, dst, 1);
    let q = g1_map_to_curve_sswu(u[0]);
    let p = g1_clear_cofactor(q);
    p
}

// Hash to G2 - Constants

#[rustfmt::skip]
const G2_XNUM_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x05c759507e8e333eu64, 0xbb5b7a9a47d7ed85u64, 0x32c52d39fd3a042au64,
        0x88b58423c50ae15du64, 0x5c2638e343d9c71cu64, 0x6238aaaaaaaa97d6u64
    ]
));
#[rustfmt::skip]
const G2_XNUM_K_1_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x11560bf17baa99bcu64, 0x32126fced787c88fu64, 0x984f87adf7ae0c7fu64,
        0x9a208c6b4f20a418u64, 0x1472aaa9cb8d5555u64, 0x26a9ffffffffc71au64
    ]
));
#[rustfmt::skip]
const G2_XNUM_K_2_R: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x11560bf17baa99bcu64, 0x32126fced787c88fu64, 0x984f87adf7ae0c7fu64,
        0x9a208c6b4f20a418u64, 0x1472aaa9cb8d5555u64, 0x26a9ffffffffc71eu64
    ]
));
#[rustfmt::skip]
const G2_XNUM_K_2_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x08ab05f8bdd54cdeu64, 0x190937e76bc3e447u64, 0xcc27c3d6fbd7063fu64,
        0xcd104635a790520cu64, 0x0a395554e5c6aaaau64, 0x9354ffffffffe38du64
    ]
));
#[rustfmt::skip]
const G2_XNUM_K_3_R: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x171d6541fa38ccfau64, 0xed6dea691f5fb614u64, 0xcb14b4e7f4e810aau64,
        0x22d6108f142b8575u64, 0x7098e38d0f671c71u64, 0x88e2aaaaaaaa5ed1u64
    ]
));

#[rustfmt::skip]
const G2_XDEN_K_0_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1a0111ea397fe69au64, 0x4b1ba7b6434bacd7u64, 0x64774b84f38512bfu64,
        0x6730d2a0f6b0f624u64, 0x1eabfffeb153ffffu64, 0xb9feffffffffaa63u64
    ]
));
#[rustfmt::skip]
const G2_XDEN_K_1_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1a0111ea397fe69au64, 0x4b1ba7b6434bacd7u64, 0x64774b84f38512bfu64,
        0x6730d2a0f6b0f624u64, 0x1eabfffeb153ffffu64, 0xb9feffffffffaa9fu64
    ]
));

#[rustfmt::skip]
const G2_YNUM_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1530477c7ab4113bu64, 0x59a4c18b076d1193u64, 0x0f7da5d4a07f649bu64,
        0xf54439d87d27e500u64, 0xfc8c25ebf8c92f68u64, 0x12cfc71c71c6d706u64
    ]
));
#[rustfmt::skip]
const G2_YNUM_K_1_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x05c759507e8e333eu64, 0xbb5b7a9a47d7ed85u64, 0x32c52d39fd3a042au64,
        0x88b58423c50ae15du64, 0x5c2638e343d9c71cu64, 0x6238aaaaaaaa97beu64
    ]
));
#[rustfmt::skip]
const G2_YNUM_K_2_R: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x11560bf17baa99bcu64, 0x32126fced787c88fu64, 0x984f87adf7ae0c7fu64,
        0x9a208c6b4f20a418u64, 0x1472aaa9cb8d5555u64, 0x26a9ffffffffc71cu64
    ]
));
#[rustfmt::skip]
const G2_YNUM_K_2_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x08ab05f8bdd54cdeu64, 0x190937e76bc3e447u64, 0xcc27c3d6fbd7063fu64,
        0xcd104635a790520cu64, 0x0a395554e5c6aaaau64, 0x9354ffffffffe38fu64
    ]
));
#[rustfmt::skip]
const G2_YNUM_K_3_R: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x124c9ad43b6cf79bu64, 0xfbf7043de3811ad0u64, 0x761b0f37a1e26286u64,
        0xb0e977c69aa27452u64, 0x4e79097a56dc4bd9u64, 0xe1b371c71c718b10u64
    ]
));

#[rustfmt::skip]
const G2_YDEN_K_0: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1a0111ea397fe69au64, 0x4b1ba7b6434bacd7u64, 0x64774b84f38512bfu64,
        0x6730d2a0f6b0f624u64, 0x1eabfffeb153ffffu64, 0xb9feffffffffa8fbu64
    ]
));
#[rustfmt::skip]
const G2_YDEN_K_1_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1a0111ea397fe69au64, 0x4b1ba7b6434bacd7u64, 0x64774b84f38512bfu64,
        0x6730d2a0f6b0f624u64, 0x1eabfffeb153ffffu64, 0xb9feffffffffa9d3u64
    ]
));
#[rustfmt::skip]
const G2_YDEN_K_2_I: ArrFp = ArrFp(secret_array!(
    U64,
    [
        0x1a0111ea397fe69au64, 0x4b1ba7b6434bacd7u64, 0x64774b84f38512bfu64,
        0x6730d2a0f6b0f624u64, 0x1eabfffeb153ffffu64, 0xb9feffffffffaa99u64
    ]
));

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.2
fn g2_simple_swu_iso(u: Fp2) -> (Fp2, Fp2) {
    let z = fp2neg((Fp::TWO(), Fp::ONE()));
    let a = (Fp::ZERO(), Fp::from_literal(240u128));
    let b = (Fp::from_literal(1012u128), Fp::from_literal(1012u128));
    let tv1 = fp2inv(fp2add(
        fp2mul(fp2mul(z, z), fp2mul(fp2mul(u, u), fp2mul(u, u))),
        fp2mul(z, fp2mul(u, u)),
    )); // inv0(z^2 * u^4 + z * u^2)
    let mut x1 = fp2mul(
        fp2mul(fp2neg(b), fp2inv(a)),
        fp2add(fp2fromfp(Fp::ONE()), tv1),
    ); // (-B / A) * (1 + tv1)
    if tv1 == fp2zero() {
        x1 = fp2mul(b, fp2inv(fp2mul(z, a))); // If tv1 == 0, set x1 = B / (Z * A)
    };
    let gx1 = fp2add(fp2add(fp2mul(fp2mul(x1, x1), x1), fp2mul(a, x1)), b); // x1^3 + A * x1 + B
    let x2 = fp2mul(fp2mul(z, fp2mul(u, u)), x1); // Z * u^2 * x1
    let gx2 = fp2add(fp2add(fp2mul(fp2mul(x2, x2), x2), fp2mul(a, x2)), b); // x2^3 + A * x2 + B
    let (x, mut y) = if fp2_is_square(gx1) {
        (x1, fp2_sqrt(gx1)) // If is_square(gx1), set x = x1 and y = sqrt(gx1)
    } else {
        (x2, fp2_sqrt(gx2)) // Else set x = x2 and y = sqrt(gx2)
    };
    if fp2_sgn0(u) != fp2_sgn0(y) {
        y = fp2neg(y); // If sgn0(u) != sgn0(y), set y = -y
    };
    (x, y)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-E.3
fn g2_isogeny_map(x: Fp2, y: Fp2) -> G2 {
    // Constants
    // xnum_k
    let mut xnum_k = Seq::<Fp2>::new(4);
    xnum_k[0usize] = (
        Fp::from_byte_seq_be(&G2_XNUM_K_0.to_be_bytes()),
        Fp::from_byte_seq_be(&G2_XNUM_K_0.to_be_bytes()),
    );
    xnum_k[1usize] = (
        Fp::ZERO(),
        Fp::from_byte_seq_be(&G2_XNUM_K_1_I.to_be_bytes()),
    );
    xnum_k[2usize] = (
        Fp::from_byte_seq_be(&G2_XNUM_K_2_R.to_be_bytes()),
        Fp::from_byte_seq_be(&G2_XNUM_K_2_I.to_be_bytes()),
    );
    xnum_k[3usize] = (
        Fp::from_byte_seq_be(&G2_XNUM_K_3_R.to_be_bytes()),
        Fp::ZERO(),
    );

    // xden_k
    let mut xden_k = Seq::<Fp2>::new(2);
    xden_k[0usize] = (
        Fp::ZERO(),
        Fp::from_byte_seq_be(&G2_XDEN_K_0_I.to_be_bytes()),
    );
    xden_k[1usize] = (
        Fp::from_literal(12u128),
        Fp::from_byte_seq_be(&G2_XDEN_K_1_I.to_be_bytes()),
    );

    // ynum_k
    let mut ynum_k = Seq::<Fp2>::new(4);
    ynum_k[0usize] = (
        Fp::from_byte_seq_be(&G2_YNUM_K_0.to_be_bytes()),
        Fp::from_byte_seq_be(&G2_YNUM_K_0.to_be_bytes()),
    );
    ynum_k[1usize] = (
        Fp::ZERO(),
        Fp::from_byte_seq_be(&G2_YNUM_K_1_I.to_be_bytes()),
    );
    ynum_k[2usize] = (
        Fp::from_byte_seq_be(&G2_YNUM_K_2_R.to_be_bytes()),
        Fp::from_byte_seq_be(&G2_YNUM_K_2_I.to_be_bytes()),
    );
    ynum_k[3usize] = (
        Fp::from_byte_seq_be(&G2_YNUM_K_3_R.to_be_bytes()),
        Fp::ZERO(),
    );

    // yden_k
    let mut yden_k = Seq::<Fp2>::new(3);
    yden_k[0usize] = (
        Fp::from_byte_seq_be(&G2_YDEN_K_0.to_be_bytes()),
        Fp::from_byte_seq_be(&G2_YDEN_K_0.to_be_bytes()),
    );
    yden_k[1usize] = (
        Fp::ZERO(),
        Fp::from_byte_seq_be(&G2_YDEN_K_1_I.to_be_bytes()),
    );
    yden_k[2usize] = (
        Fp::from_literal(18u128),
        Fp::from_byte_seq_be(&G2_YDEN_K_2_I.to_be_bytes()),
    );

    // Computation

    // x_num = k_(1,3) * x^3 + k_(1,2) * x^2 + k_(1,1) * x + k_(1,0)
    let mut xnum = fp2zero();
    let mut xx = fp2fromfp(Fp::ONE());
    for i in 0..xnum_k.len() {
        xnum = fp2add(xnum, fp2mul(xx, xnum_k[i]));
        xx = fp2mul(xx, x);
    }

    // x_den = x^2 + k_(2,1) * x + k_(2,0)
    let mut xden = fp2zero();
    let mut xx = fp2fromfp(Fp::ONE());
    for i in 0..xden_k.len() {
        xden = fp2add(xden, fp2mul(xx, xden_k[i]));
        xx = fp2mul(xx, x);
    }
    xden = fp2add(xden, xx);

    // y_num = k_(3,3) * x^3 + k_(3,2) * x^2 + k_(3,1) * x + k_(3,0)
    let mut ynum = fp2zero();
    let mut xx = fp2fromfp(Fp::ONE());
    for i in 0..ynum_k.len() {
        ynum = fp2add(ynum, fp2mul(xx, ynum_k[i]));
        xx = fp2mul(xx, x);
    }

    // y_den = x^3 + k_(4,2) * x^2 + k_(4,1) * x + k_(4,0)
    let mut yden = fp2zero();
    let mut xx = fp2fromfp(Fp::ONE());
    for i in 0..yden_k.len() {
        yden = fp2add(yden, fp2mul(xx, yden_k[i]));
        xx = fp2mul(xx, x);
    }
    yden = fp2add(yden, xx);

    // xr = x_num / x_den
    let xr = fp2mul(xnum, fp2inv(xden));

    // yr = y * y_num / y_den
    let yr = fp2mul(y, fp2mul(ynum, fp2inv(yden)));

    // if xden or yden is zero return point at infinity
    let mut inf = false;
    if xden == fp2zero() || yden == fp2zero() {
        inf = true;
    }

    (xr, yr, inf)
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-6.6.3
fn g2_map_to_curve_sswu(u: Fp2) -> G2 {
    let (xp, yp) = g2_simple_swu_iso(u);
    let p = g2_isogeny_map(xp, yp);
    p
}

// https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#section-3
pub fn g2_hash_to_curve_sswu(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 2);
    let q0 = g2_map_to_curve_sswu(u[0]);
    let q1 = g2_map_to_curve_sswu(u[1]);
    let r = g2add(q0, q1);
    let p = g2_clear_cofactor(r);
    p
}

pub fn g2_encode_to_curve_sswu(msg: &ByteSeq, dst: &ByteSeq) -> G2 {
    let u = fp2_hash_to_field(msg, dst, 1);
    let q = g2_map_to_curve_sswu(u[0]);
    let p = g2_clear_cofactor(q);
    p
}

#[cfg(test)]
extern crate quickcheck;
#[cfg(test)]
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-K.1
    fn test_expand_message() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-expander-SHA256-128");
        let len_in_bytes = 0x20;
        let msg = ByteSeq::from_public_slice(b"");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "68a985b87eb6b46952128911f2a4412bbc302a9d759667f87f7a21d803f07235";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "eff31487c770a893cfb36f912fbfcbff40d5661771ca4b2cb4eafe524333f5c1";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "b23a1d2b4d97b2ef7785562a7e8bac7eed54ed6e97e29aa51bfe3f12ddad1ff9";
        assert_eq!(expm.to_hex(), result);

        let len_in_bytes = 0x80;
        let msg = ByteSeq::from_public_slice(b"");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "af84c27ccfd45d41914fdff5df25293e221afc53d8ad2ac06d5e3e29485dadbee0d121587713a3e0dd4d5e69e93eb7cd4f5df4\
            cd103e188cf60cb02edc3edf18eda8576c412b18ffb658e3dd6ec849469b979d444cf7b26911a08e63cf31f9dcc541708d3491184472\
            c2c29bb749d4286b004ceb5ee6b9a7fa5b646c993f0ced";
        assert_eq!(expm.to_hex(), result);

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let expm = expand_message_xmd(&msg, &dst, len_in_bytes);
        let result = "ef904a29bffc4cf9ee82832451c946ac3c8f8058ae97d8d629831a74c6572bd9ebd0df635cd1f208e2038e760c4994984ce73f\
            0d55ea9f22af83ba4734569d4bc95e18350f740c07eef653cbb9f87910d833751825f0ebefa1abe5420bb52be14cf489b37fe1a72f7d\
            e2d10be453b2c9d9eb20c7e3f6edc5a60629178d9478df";
        assert_eq!(expm.to_hex(), result);
    }

    #[test]
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.9.1
    fn test_fp_hash_to_field() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_");
        let msg = ByteSeq::from_public_slice(b"");
        let count = 2;
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "0ba14bd907ad64a016293ee7c2d276b8eae71f25a4b941eece7b0d89f17f75cb3ae5438a614fb61d6835ad59f29c564f");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "019b9bd7979f12657976de2884c7cce192b82c177c80e0ec604436a7f538d231552f0d96d9f7babe5fa3b19b3ff25ac9");

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "062d1865eb80ebfa73dcfc45db1ad4266b9f3a93219976a3790ab8d52d3e5f1e62f3b01795e36834b17b70e7b76246d4");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "0cdc3e2f271f29c4ff75020857ce6c5d36008c9b48385ea2f2bf6f96f428a3deb798aa033cd482d1cdc8b30178b08e3a");

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let fps = fp_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].to_byte_seq_be().to_hex(), "010476f6a060453c0b1ad0b628f3e57c23039ee16eea5e71bb87c3b5419b1255dc0e5883322e563b84a29543823c0e86");
        assert_eq!(fps[1usize].to_byte_seq_be().to_hex(), "0b1a912064fb0554b180e07af7e787f1f883a0470759c03c1b6509eb8ce980d1670305ae7b928226bb58fdc0a419f46e");
    }

    #[test]
    fn test_fp_sgn0() {
        let a = Fp::from_hex("243171");
        assert!(fp_sgn0(a));
        let b = Fp::from_hex("2431710293859032");
        assert!(!fp_sgn0(b));
    }

    #[test]
    fn test_fp2_sgn0() {
        let a = Fp::from_hex("24e31f71");
        let b = Fp::from_hex("243d17ee10293859032");
        assert!(fp2_sgn0((a, b)));
        let z = Fp::ZERO();
        let c = Fp::from_hex("598325bc69");
        assert!(fp2_sgn0((z, c)));
        let d = Fp::from_hex("9879a032b6");
        assert!(!fp2_sgn0((z, d)));
    }

    #[test]
    fn test_fp_square() {
        let x = Fp::from_literal(4);
        assert!(fp_is_square(x));
    }

    #[test]
    fn test_fp_sqrt() {
        let x = Fp::from_literal(256);
        let k = fp_sqrt(x);
        assert_eq!(k * k, x);
    }

    #[test]
    fn test_fp2_is_square() {
        let x = (Fp::from_literal(54), Fp::from_literal(34));
        let y = fp2mul(x, x);
        assert!(fp2_is_square(y));
        assert!(!fp2_is_square(x));
    }

    #[test]
    fn test_fp2_sqrt() {
        let x = (Fp::ZERO() - Fp::from_literal(54), Fp::from_literal(34));
        let y = fp2mul(x, x);
        let k = fp2_sqrt(y);
        assert_eq!(fp2mul(k, k), y);
    }

    #[test]
    fn test_g1_correct_z() {
        let z = Fp::ZERO() - Fp::from_literal(3);
        let gz = g1_curve_func(z);
        assert!(gz != Fp::ZERO());
        let t = (Fp::ZERO() - (Fp::from_literal(3) * z * z)) / (Fp::from_literal(4) * gz);
        assert!(t != Fp::ZERO());
        assert!(fp_is_square(t));
        assert!(fp_is_square(gz) || fp_is_square(g1_curve_func((Fp::ZERO() - z) / Fp::TWO())));
    }

    #[test]
    fn test_g1_map_to_curve_svdw() {
        let u = Fp::from_literal(3082);
        let (x, y, _) = g1_map_to_curve_svdw(u);
        assert_eq!(y * y, x * x * x + Fp::from_literal(4));
    }

    #[quickcheck]
    fn test_prop_g1_map_to_curve_svdw(a: u128) -> bool {
        let u = Fp::from_literal(a);
        let (x, y, _) = g1_map_to_curve_svdw(u);
        y * y == x * x * x + Fp::from_literal(4)
    }

    #[test]
    // Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.10.1
    fn test_fp2_hash_to_field() {
        let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_");
        let msg = ByteSeq::from_public_slice(b"");
        let count = 2;
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "03dbc2cce174e91ba93cbb08f26b917f98194a2ea08d1cce75b2b9cc9f21689d80bd79b594a613d0a68eb807dfdc1cf8");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "05a2acec64114845711a54199ea339abd125ba38253b70a92c876df10598bd1986b739cad67961eb94f7076511b3b39a");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "02f99798e8a5acdeed60d7e18e9120521ba1f47ec090984662846bc825de191b5b7641148c0dbc237726a334473eee94");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "145a81e418d4010cc027a68f14391b30074e89e60ee7a22f87217b2f6eb0c4b94c9115b436e6fa4607e95a98de30a435");

        let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "0313d9325081b415bfd4e5364efaef392ecf69b087496973b229303e1816d2080971470f7da112c4eb43053130b785e1");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "062f84cb21ed89406890c051a0e8b9cf6c575cf6e8e18ecf63ba86826b0ae02548d83b483b79e48512b82a6c0686df8f");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "1739123845406baa7be5c5dc74492051b6d42504de008c635f3535bb831d478a341420e67dcc7b46b2e8cba5379cca97");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "01897665d9cb5db16a27657760bbea7951f67ad68f8d55f7113f24ba6ddd82caef240a9bfa627972279974894701d975");

        let msg = ByteSeq::from_public_slice(
            b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
            qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
        );
        let fps = fp2_hash_to_field(&msg, &dst, count);
        assert_eq!(fps[0usize].0.to_byte_seq_be().to_hex(), "025820cefc7d06fd38de7d8e370e0da8a52498be9b53cba9927b2ef5c6de1e12e12f188bbc7bc923864883c57e49e253");
        assert_eq!(fps[0usize].1.to_byte_seq_be().to_hex(), "034147b77ce337a52e5948f66db0bab47a8d038e712123bb381899b6ab5ad20f02805601e6104c29df18c254b8618c7b");
        assert_eq!(fps[1usize].0.to_byte_seq_be().to_hex(), "0930315cae1f9a6017c3f0c8f2314baa130e1cf13f6532bff0a8a1790cd70af918088c3db94bda214e896e1543629795");
        assert_eq!(fps[1usize].1.to_byte_seq_be().to_hex(), "10c4df2cacf67ea3cb3108b00d4cbd0b3968031ebc8eac4b1ebcefe84d6b715fde66bef0219951ece29d1facc8a520ef");
    }

    #[test]
    fn test_g2_correct_z() {
        let z = fp2neg(fp2fromfp(Fp::ONE()));
        let gz = g2_curve_func(z);
        assert!(gz != fp2zero());
        let t = fp2mul(
            fp2neg(fp2mul(fp2fromfp(Fp::from_literal(3)), fp2mul(z, z))),
            fp2inv(fp2mul(fp2fromfp(Fp::from_literal(4)), gz)),
        );
        assert!(t != fp2zero());
        assert!(fp2_is_square(t));
        assert!(fp2_is_square(gz));
    }

    #[test]
    fn test_g2_map_to_curve_svdw() {
        let u1 = Fp::from_literal(3082);
        let u2 = Fp::from_literal(4021);
        let (x, y, _) = g2_map_to_curve_svdw((u1, u2));
        assert_eq!(
            fp2mul(y, y),
            fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4))
            )
        );
    }

    #[quickcheck]
    fn test_prop_g2_map_to_curve_svdw(a: u128, b: u128) -> bool {
        let u1 = Fp::from_literal(a);
        let u2 = Fp::from_literal(b);
        let (x, y, _) = g2_map_to_curve_svdw((u1, u2));
        fp2mul(y, y)
            == fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4)),
            )
    }

    // Tests for sswu

    #[test]
    fn test_g1_simple_swu_iso() {
        let a = Fp::from_hex("144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d");
        let b = Fp::from_hex("12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0");
        let u = Fp::from_literal(2464);
        let (x, y) = g1_simple_swu_iso(u);
        assert_eq!(y * y, x * x * x + a * x + b);
    }

    #[quickcheck]
    fn test_prop_g1_simple_swu_iso(u: u128) -> bool {
        let a = Fp::from_hex("144698a3b8e9433d693a02c96d4982b0ea985383ee66a8d8e8981aefd881ac98936f8da0e0f97f5cf428082d584c1d");
        let b = Fp::from_hex("12e2908d11688030018b12e8753eee3b2016c1f0f24f4070a0b9c14fcef35ef55a23215a316ceaa5d1cc48e98e172be0");
        let u = Fp::from_literal(u);
        let (x, y) = g1_simple_swu_iso(u);
        y * y == x * x * x + a * x + b
    }

    #[test]
    fn test_g1_map_to_curve_sswu() {
        let u = Fp::from_literal(0);
        let (x, y, _) = g1_map_to_curve_sswu(u);
        assert_eq!(y * y, x * x * x + Fp::from_literal(4));
    }

    #[quickcheck]
    fn test_prop_g1_map_to_curve_sswu(a: u128) -> bool {
        let u = Fp::from_literal(a);
        let (x, y, _) = g1_map_to_curve_sswu(u);
        y * y == x * x * x + Fp::from_literal(4)
    }

    #[test]
    fn test_g2_simple_swu_iso() {
        let a = (Fp::ZERO(), Fp::from_literal(240u128));
        let b = (Fp::from_literal(1012u128), Fp::from_literal(1012u128));
        let u1 = Fp::from_literal(3082);
        let u2 = Fp::from_literal(4021);
        let (x, y) = g2_simple_swu_iso((u1, u2));
        assert_eq!(
            fp2mul(y, y),
            fp2add(fp2add(fp2mul(fp2mul(x, x), x), fp2mul(a, x)), b)
        );
    }

    #[quickcheck]
    fn test_prop_g2_simple_swu_iso(u1: u128, u2: u128) -> bool {
        let a = (Fp::ZERO(), Fp::from_literal(240u128));
        let b = (Fp::from_literal(1012u128), Fp::from_literal(1012u128));
        let u1 = Fp::from_literal(u1);
        let u2 = Fp::from_literal(u2);
        let (x, y) = g2_simple_swu_iso((u1, u2));
        fp2mul(y, y) == fp2add(fp2add(fp2mul(fp2mul(x, x), x), fp2mul(a, x)), b)
    }

    #[test]
    fn test_g2_map_to_curve_sswu() {
        let u1 = Fp::from_literal(3082);
        let u2 = Fp::from_literal(4021);
        let (x, y, _) = g2_map_to_curve_sswu((u1, u2));
        assert_eq!(
            fp2mul(y, y),
            fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4))
            )
        );
    }

    #[quickcheck]
    fn test_prop_g2_map_to_curve_sswu(a: u128, b: u128) -> bool {
        let u1 = Fp::from_literal(a);
        let u2 = Fp::from_literal(b);
        let (x, y, _) = g2_map_to_curve_sswu((u1, u2));
        fp2mul(y, y)
            == fp2add(
                fp2mul(fp2mul(x, x), x),
                (Fp::from_literal(4), Fp::from_literal(4)),
            )
    }
}
