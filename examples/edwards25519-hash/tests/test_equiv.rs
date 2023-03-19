use hacspec_lib::*;
use hacspec_edwards25519_hash::*;
use hacspec_edwards25519::*;

use h2c_rust_ref::{GetHashToCurve, SUITES_EDWARDS};
use redox_ecc::ellipticcurve::Encode;

use quickcheck_macros::quickcheck;

// Checks that the three specifications of map_to_curve in ../src/edwards25519-hash.rs
// agree in value together with armfazh's specification of edwards25519_XMD:SHA-512_ELL2_NU_
// armfazh's specification can be seen here: https://github.com/armfazh/h2c-rust-ref
#[quickcheck]
fn test_equiv_armfazh(msg: String) -> bool {
    let dst = b"QUUX-V01-CS02-with-edwards25519_XMD:SHA-512_ELL2_NU_";
    let msg: &[u8] = msg.as_bytes();
    let suite = SUITES_EDWARDS["edwards25519_XMD:SHA-512_ELL2_NU_"].get(dst);
    let mut q = suite.hash(msg);
    q.normalize(); // make q into p

    // convert to hacspec ed point
    let parmfazh = q.encode(true);
    let parmfazh = ByteSeq::from_public_slice(&parmfazh);
    let parmfazh = decode(parmfazh).unwrap();

    let u = ed_hash_to_field(
        &ByteSeq::from_public_slice(msg),
        &ByteSeq::from_public_slice(dst),
        1
    ).unwrap();

    // compute normal
    let st = map_to_curve_elligator2(u[0]);
    let q = curve25519_to_edwards25519(st);
    let pnormal = ed_clear_cofactor(q);
    let pnormal = point_normalize(pnormal);

    // compute straight
    let st = map_to_curve_elligator2_straight(u[0]);
    let q = curve25519_to_edwards25519(st);
    let pstraight = ed_clear_cofactor(q);
    let pstraight = point_normalize(pstraight);

    // compute optimized
    let q = map_to_curve_elligator2_edwards25519(u[0]);
    let poptim = ed_clear_cofactor(q);
    let poptim = point_normalize(poptim);

    (parmfazh == poptim) & 
    (parmfazh == pstraight) & 
    (parmfazh == pnormal) &
    (pstraight == pnormal) &
    (pstraight == poptim) &
    (pnormal == poptim)
}
