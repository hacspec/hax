#![allow(non_snake_case)]
extern crate quickcheck;

use curve25519_dalek_ng::ristretto::RistrettoPoint as DalekRistrettoPoint;
use curve25519_dalek_ng::scalar::Scalar as DalekScalar;
use hacspec_lib::*;
use hacspec_ristretto::*;
use quickcheck::*;

// === Helper Functions === //

fn quickcheck(tests: u64, helper: impl Testable) {
    QuickCheck::new()
        .tests(tests)
        .min_tests_passed(tests)
        .max_tests(10000000000)
        .quickcheck(helper);
}

// Compare Hacspec Ristretto point with a Dalek Ristretto point
fn cmp_points(p: RistrettoPoint, q: DalekRistrettoPoint) -> bool {
    let p_enc = encode(p);
    let p_bytes = p_enc.to_le_bytes();
    let p_native = p_bytes.to_native();
    let p_slice = p_native.as_slice();

    let q_enc = q.compress();
    let q_slice = q_enc.to_bytes();

    q_slice == p_slice
}

// Creates ristretto points for both implementations
fn create_points(mut vec: Vec<u8>) -> (RistrettoPoint, DalekRistrettoPoint) {
    vec.truncate(64);

    let hac_pnt = vec_to_pnt_hac(&vec);
    let dal_pnt = vec_to_pnt_dal(&vec);

    (hac_pnt, dal_pnt)
}

fn vec_to_pnt_hac(vec: &Vec<u8>) -> RistrettoPoint {
    let bytestring = ByteString::from_public_slice(vec.as_slice());
    one_way_map(bytestring)
}

fn vec_to_pnt_dal(vec: &Vec<u8>) -> DalekRistrettoPoint {
    let mut arr: [u8; 64] = [0; 64];

    for i in 0..vec.len() {
        arr[i] = vec[i];
    }
    DalekRistrettoPoint::from_uniform_bytes(&arr)
}

fn vec_to_scalar_hac(xs: &Vec<u8>) -> Scalar {
    let mut seq = Seq::<U8>::new(xs.len());

    for i in 0..xs.len() {
        seq[i] = U8::classify(xs[i]);
    }

    Scalar::from_byte_seq_le(seq)
}

fn vec_to_scalar_dal(vec: &Vec<u8>) -> DalekScalar {
    let mut arr: [u8; 32] = [0; 32];

    for i in 0..arr.len() {
        arr[i] = vec[i];
    }

    DalekScalar::from_bytes_mod_order(arr)
}

// === Tests === //

#[test]
fn test_dalek_one_way_map() {
    fn helper(v: Vec<u8>) -> TestResult {
        if v.len() < 64 {
            return TestResult::discard();
        }

        let (hac_map, dal_map) = create_points(v);

        TestResult::from_bool(cmp_points(hac_map, dal_map))
    }
    quickcheck(100, helper as fn(Vec<u8>) -> TestResult)
}

#[test]
fn test_prop_encode_decode() {
    fn helper(v: Vec<u8>) -> TestResult {
        if v.len() < 64 {
            return TestResult::discard();
        }

        let (hac_pnt, _) = create_points(v);

        let hac_enc = encode(hac_pnt);

        let hac_dec = decode(hac_enc).unwrap();

        let hac_renc = encode(hac_dec);

        let is_same_dec = equals(hac_pnt, hac_dec);
        let is_same_enc = hac_enc.to_le_bytes() == hac_renc.to_le_bytes();

        TestResult::from_bool(is_same_enc && is_same_dec)
    }
    quickcheck(100, helper as fn(Vec<u8>) -> TestResult)
}

#[test]
fn test_dalek_decode_encode() {
    fn helper(v: Vec<u8>) -> TestResult {
        if v.len() < 64 {
            return TestResult::discard();
        }

        let (hac_pnt, dal_pnt) = create_points(v);

        let hac_enc = encode(hac_pnt);
        let dal_enc = dal_pnt.compress();

        let hac_dec = decode(hac_enc).unwrap();
        let dal_dec = dal_enc.decompress().unwrap();

        TestResult::from_bool(cmp_points(hac_dec, dal_dec))
    }
    quickcheck(100, helper as fn(Vec<u8>) -> TestResult)
}

#[test]
fn test_dalek_point_addition_subtraction() {
    fn helper(v: Vec<u8>, u: Vec<u8>) -> TestResult {
        if v.len() < 64 || u.len() < 64 {
            return TestResult::discard();
        }

        let (hac_v, dal_v) = create_points(v);
        let (hac_u, dal_u) = create_points(u);

        let hac_add = add(hac_v, hac_u);
        let hac_sub = sub(hac_v, hac_u);

        let dal_add = dal_v + dal_u;
        let dal_sub = dal_v - dal_u;

        TestResult::from_bool(cmp_points(hac_add, dal_add) && cmp_points(hac_sub, dal_sub))
    }
    quickcheck(100, helper as fn(Vec<u8>, Vec<u8>) -> TestResult)
}

#[test]
fn test_dalek_scalar_multiplication() {
    fn helper(v: Vec<u8>, mut x: Vec<u8>) -> TestResult {
        if (v.len() < 64) || (x.len() < 32) {
            return TestResult::discard();
        }
        x.truncate(32);

        let (hac_pnt, dal_pnt) = create_points(v);

        let hac_scal = mul(vec_to_scalar_hac(&x), hac_pnt);
        let dal_scal = vec_to_scalar_dal(&x) * dal_pnt;

        TestResult::from_bool(cmp_points(hac_scal, dal_scal))
    }
    quickcheck(20, helper as fn(Vec<u8>, Vec<u8>) -> TestResult)
}

#[test]
fn test_dalek_point_negation() {
    fn helper(v: Vec<u8>) -> TestResult {
        if v.len() < 64 {
            return TestResult::discard();
        }

        let (hac_pnt, dal_pnt) = create_points(v);

        let hac_neg = neg(hac_pnt);
        let dal_neg = dal_pnt.neg();

        TestResult::from_bool(cmp_points(hac_neg, dal_neg))
    }
    quickcheck(100, helper as fn(Vec<u8>) -> TestResult)
}
