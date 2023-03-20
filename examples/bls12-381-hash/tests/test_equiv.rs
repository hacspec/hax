//! Testing the hacspec implementation of hashing to the bls12-381 curve against a number of implementations.

use hacspec_bls12_381_hash::*;
use hacspec_lib::*;

use h2c_rust_ref::{GetHashToCurve, SUITES_WEIERSTRASS};
use redox_ecc::ellipticcurve::Decode;

use pairing_plus::bls12_381::{G1Uncompressed, G2Uncompressed, G1, G2};
use pairing_plus::hash_to_curve::HashToCurve;
use pairing_plus::hash_to_field::ExpandMsgXmd;
use pairing_plus::{CurveProjective, EncodedPoint};
use sha2_08::Sha256;

use amcl::bls381::bls381::utils::{
    deserialize_g1, deserialize_g2, hash_to_curve_g1, hash_to_curve_g2,
};

use bls12_381::hash_to_curve::{ExpandMsgXmd as ZKExpandMsgXmd, HashToCurve as ZKHashToCurve};
use bls12_381::{
    G1Affine as ZKG1Affine, G1Projective as ZKG1Projective, G2Affine as ZKG2Affine,
    G2Projective as ZKG2Projective,
};
use sha2_09::Sha256 as ZKSha256;

use curve_arithmetic::Curve;
use group::EncodedPoint as CEncodedPoint;
use pairing::bls12_381::{
    G1Affine as CG1Affine, G1Uncompressed as CG1Uncompressed, G2Affine as CG2Affine,
    G2Uncompressed as CG2Uncompressed,
};

extern crate quickcheck;
#[macro_use(quickcheck)]
extern crate quickcheck_macros;

// Testing against the reference implementation
// https://github.com/armfazh/h2c-rust-ref
#[quickcheck]
fn test_equiv_armfazh_g1_sswu_ro(msg: String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SSWU_RO_"].get(dst);
    let curve = suite.get_curve();
    let mut q = suite.hash(msg);
    q.normalize();
    let p = g1_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        vec![4u8],
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = curve.decode(&t).unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_armfazh_g1_sswu_nu(msg: String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SSWU_NU_"].get(dst);
    let curve = suite.get_curve();
    let mut q = suite.hash(msg);
    q.normalize();
    let p = g1_encode_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        vec![4u8],
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = curve.decode(&t).unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_armfazh_g1_svdw_ro(msg: String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SVDW_RO_";
    let msg: &[u8] = msg.as_bytes();
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SVDW_RO_"].get(dst);
    let curve = suite.get_curve();
    let mut q = suite.hash(msg);
    q.normalize();
    let p = g1_hash_to_curve_svdw(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        vec![4u8],
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = curve.decode(&t).unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_armfazh_g1_svdw_nu(msg: String) -> bool {
    let dst = b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SVDW_NU_";
    let msg: &[u8] = msg.as_bytes();
    let suite = SUITES_WEIERSTRASS["BLS12381G1_XMD:SHA-256_SVDW_NU_"].get(dst);
    let curve = suite.get_curve();
    let mut q = suite.hash(msg);
    q.normalize();
    let p = g1_encode_to_curve_svdw(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        vec![4u8],
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = curve.decode(&t).unwrap();
    q == ph
}

// Testing against pairing-plus
// https://github.com/algorand/pairing-plus
#[quickcheck]
fn test_equiv_pairing_plus_g1_sswu_ro(msg: String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G1 as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve::<&[u8], &[u8]>(msg, dst)
        .into_affine();
    let p = g1_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = G1Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..96]);
    let ph = tv.into_affine().unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_pairing_plus_g1_sswu_nu(msg: String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G1 as HashToCurve<ExpandMsgXmd<Sha256>>>::encode_to_curve::<&[u8], &[u8]>(msg, dst)
        .into_affine();
    let p = g1_encode_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = G1Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..96]);
    let ph = tv.into_affine().unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_pairing_plus_g2_sswu_ro(msg: String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G2 as HashToCurve<ExpandMsgXmd<Sha256>>>::hash_to_curve::<&[u8], &[u8]>(msg, dst)
        .into_affine();
    let p = g2_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = G2Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..192]);
    let ph = tv.into_affine().unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_pairing_plus_g2_sswu_nu(msg: String) -> bool {
    let dst = b"pairing-plus-with-BLS12381G2_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let q = <G2 as HashToCurve<ExpandMsgXmd<Sha256>>>::encode_to_curve::<&[u8], &[u8]>(msg, dst)
        .into_affine();
    let p = g2_encode_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = G2Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..192]);
    let ph = tv.into_affine().unwrap();
    q == ph
}

// Testing against amcl
// https://github.com/apache/incubator-milagro-crypto-rust
#[quickcheck]
fn test_equiv_amcl_g1_sswu_ro(msg: String) -> bool {
    let dst = b"amcl-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let tv = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = deserialize_g1(&tv).unwrap();
    let q = hash_to_curve_g1(msg, dst);
    ph == q
}

#[quickcheck]
fn test_equiv_amcl_g2_sswu_ro(msg: String) -> bool {
    let dst = b"amcl-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let tv = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let ph = deserialize_g2(&tv).unwrap();
    let q = hash_to_curve_g2(msg, dst);
    ph == q
}

// Testing against zkcrypto
// https://github.com/zkcrypto/bls12_381
#[quickcheck]
fn test_equiv_zkcrypto_g1_sswu_ro(msg: String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G1_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = [0; 96];
    tv.copy_from_slice(&t[0..96]);
    let ph = ZKG1Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG1Affine::from(<ZKG1Projective as ZKHashToCurve<
        ZKExpandMsgXmd<ZKSha256>,
    >>::hash_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g1_sswu_nu(msg: String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G1_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let p = g1_encode_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = [0; 96];
    tv.copy_from_slice(&t[0..96]);
    let ph = ZKG1Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG1Affine::from(<ZKG1Projective as ZKHashToCurve<
        ZKExpandMsgXmd<ZKSha256>,
    >>::encode_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g2_sswu_ro(msg: String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G2_XMD:SHA-256_SSWU_RO_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = [0; 192];
    tv.copy_from_slice(&t[0..192]);
    let ph = ZKG2Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG2Affine::from(<ZKG2Projective as ZKHashToCurve<
        ZKExpandMsgXmd<ZKSha256>,
    >>::hash_to_curve(msg, dst));
    ph == q
}

#[quickcheck]
fn test_equiv_zkcrypto_g2_sswu_nu(msg: String) -> bool {
    let dst = b"zkcrypto-with-BLS12381G2_XMD:SHA-256_SSWU_NU_";
    let msg: &[u8] = msg.as_bytes();
    let p = g2_encode_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = [0; 192];
    tv.copy_from_slice(&t[0..192]);
    let ph = ZKG2Affine::from_uncompressed(&tv).unwrap();
    let q = ZKG2Affine::from(<ZKG2Projective as ZKHashToCurve<
        ZKExpandMsgXmd<ZKSha256>,
    >>::encode_to_curve(msg, dst));
    ph == q
}

// Testing against concordium
// https://github.com/Concordium/concordium-base/tree/main/rust-src/curve_arithmetic
#[quickcheck]
fn test_equiv_concordium_g1_sswu_ro(msg: String) -> bool {
    let dst = b"CONCORDIUM-hashtoG1-with-BLS12381G1_XMD:SHA-256_SSWU_RO";
    let msg: &[u8] = msg.as_bytes();
    let q = CG1Affine::hash_to_group(msg);
    let p = g1_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0.to_byte_seq_be().to_native(),
        p.1.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = CG1Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..96]);
    let ph = tv.into_affine().unwrap();
    q == ph
}

#[quickcheck]
fn test_equiv_concordium_g2_sswu_ro(msg: String) -> bool {
    let dst = b"CONCORDIUM-hashtoG2-with-BLS12381G2_XMD:SHA-256_SSWU_RO";
    let msg: &[u8] = msg.as_bytes();
    let q = CG2Affine::hash_to_group(msg);
    let p = g2_hash_to_curve_sswu(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
    );
    let t = [
        p.0 .1.to_byte_seq_be().to_native(),
        p.0 .0.to_byte_seq_be().to_native(),
        p.1 .1.to_byte_seq_be().to_native(),
        p.1 .0.to_byte_seq_be().to_native(),
    ]
    .concat();
    let mut tv = CG2Uncompressed::empty();
    tv.as_mut().copy_from_slice(&t[0..192]);
    let ph = tv.into_affine().unwrap();
    q == ph
}
