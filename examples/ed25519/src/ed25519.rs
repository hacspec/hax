//! This crate gives a specification for the EdDSA signature scheme ed25519.
//! As there is no proper consensus for the verification algorithm, it has been implemented
//! in multiple ways.
//! - zcash_verify implements the ZIP-0215 standard (<https://zips.z.cash/zip-0215>)
//! - ietf_cofactored_verify and ietf_cofactorless_verify both implement the ietf standard.
//! (<https://datatracker.ietf.org/doc/rfc8032>). However as the standard writes:
//!
//!     > Check the group equation \[8\]\[S\]B = \[8\]R + \[8\]\[k\]A'.  It's sufficient, but not,
//!     > required to instead check \[S\]B = R + \[k\]A'.
//!
//!     they differ in which of the verification equations they use.
//! - alg2_verify implements algorithm 2 from the paper <https://eprint.iacr.org/2020/1244.pdf>.
//!
//! The different implementations and specifications differ in three ways:
//! - Cofactored/cofactorless verification -- (Using \[8\]\[S\]B = \[8\]R + \[8\]\[H(R, A, msg)\]A
//! or \[S\]B = R + \[H(R, A, msg)\]A as the verification check).
//! - Accepting/rejecting non-canonical encodings of points.
//! - Accepting/rejecting small-order points.
//!
//! For each of the single signature verification algorithms, their corresponding batch
//! verification algorithm has also been implemented. However one should not use cofactorless
//! batch verification as on some inputs it is flaky (ie. it can both accept and reject the signature
//! non-deterministically). The reason this is included is for completeness sake, to show that it
//! is indeed flaky, and because multiple libraries implement this batch verification (eg. the dalek
//! library). Cofactored batch verification does not have this problem.
//!
//! The paper <https://eprint.iacr.org/2020/1244.pdf> shows why cofactorless batch verification
//! does not work. It also provides test vectors for edge cases and compares various implementations
//! on these.
//!
//! # Examples
//! ```
//! use hacspec_lib::*;
//! use hacspec_ed25519::*;
//! use hacspec_edwards25519::*;
//!
//! let sk = SecretKey::from_hex("9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60");
//! // or alternatively SecretKey::from_public_slice(...);
//! let msg = ByteSeq::from_public_slice(b"hello world");
//! let sig = sign(sk, &msg);
//! let pk = secret_to_public(sk);
//! assert!(zcash_verify(pk, sig, &msg).is_ok());
//! ```
use hacspec_lib::*;
use hacspec_sha512::*;
use hacspec_edwards25519::*;

fn scalar_from_hash(h: Sha512Digest) -> Scalar {
    let s = BigScalar::from_byte_seq_le(h);
    Scalar::from_byte_seq_le(s.to_byte_seq_le().slice(0, 32))
}

/// Sign a message under a secret key.
pub fn sign(sk: SecretKey, msg: &ByteSeq) -> Signature {
    let (a, prefix) = secret_expand(sk);
    let a = Scalar::from_byte_seq_le(a);
    let b = decompress(BASE).unwrap();
    let a_p = compress(point_mul(a, b));
    let r = scalar_from_hash(sha512(&prefix.concat(msg)));
    let r_p = point_mul(r, b);
    let r_s = compress(r_p);
    let h = scalar_from_hash(sha512(&r_s.concat(&a_p).concat(msg)));
    let s = r + h * a;
    let s_bytes = s.to_byte_seq_le().slice(0, 32);
    Signature::new().update(0, &r_s).update(32, &s_bytes)
}

/// Cofactored verification.
/// Allows non-canonical encoding of points.
/// Allows small-order points.
pub fn zcash_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress_non_canonical(BASE).unwrap();
    let a = decompress_non_canonical(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress_non_canonical(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
pub fn ietf_cofactored_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Cofactorless verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
pub fn ietf_cofactorless_verify(
    pk: PublicKey,
    signature: Signature,
    msg: &ByteSeq,
) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul(s, b);
    let ka = point_mul(k, a);

    if point_eq(sb, point_add(r, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

fn is_identity(p: EdPoint) -> bool {
    point_eq(p, point_identity())
}

/// Algorithm 2 from <https://eprint.iacr.org/2020/1244.pdf>.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Rejects small-order points for the public key.
pub fn alg2_verify(pk: PublicKey, signature: Signature, msg: &ByteSeq) -> VerifyResult {
    let b = decompress(BASE).unwrap();
    let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
    if is_identity(point_mul_by_cofactor(a)) {
        VerifyResult::Err(Error::SmallOrderPoint)?;
    }
    let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
    let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
    if !check_canonical_scalar(s_bytes) {
        VerifyResult::Err(Error::InvalidS)?;
    }
    let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
    let s = Scalar::from_byte_seq_le(s_bytes);
    let k = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(msg)));

    let sb = point_mul_by_cofactor(point_mul(s, b));
    let rc = point_mul_by_cofactor(r);
    let ka = point_mul_by_cofactor(point_mul(k, a));

    if point_eq(sb, point_add(rc, ka)) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

#[derive(Default, Clone)]
pub struct BatchEntry(pub PublicKey, pub ByteSeq, pub Signature);

/// Batch verification.
/// Cofactored verification.
/// Allows non-canonical encoding of points.
/// Allows small-order points.
pub fn zcash_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress_non_canonical(pk).ok_or(Error::InvalidPublickey)?;
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress_non_canonical(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;
        r_sum = point_add(r_sum, point_mul(z, r));
        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_mul_by_cofactor(point_add(point_neg(sb), point_add(r_sum, a_sum)));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Batch verification.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
pub fn ietf_cofactored_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;
        r_sum = point_add(r_sum, point_mul(z, r));
        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_mul_by_cofactor(point_add(point_neg(sb), point_add(r_sum, a_sum)));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Batch verification.
/// Cofactorless verification.
/// Rejects non-canonical encoding of points.
/// Allows small-order points.
/// One should not use this as it can be flaky.
pub fn ietf_cofactorless_batch_verify(
    entries: &Seq<BatchEntry>,
    entropy: &ByteSeq,
) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;
        r_sum = point_add(r_sum, point_mul(z, r));
        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_add(point_neg(sb), point_add(r_sum, a_sum));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

/// Batch verification.
/// Algorithm 3 from <https://eprint.iacr.org/2020/1244.pdf>.
/// Cofactored verification.
/// Rejects non-canonical encoding of points.
/// Rejects small-order points for the public key.
pub fn alg3_batch_verify(entries: &Seq<BatchEntry>, entropy: &ByteSeq) -> VerifyResult {
    if entropy.len() < 16 * entries.len() {
        VerifyResult::Err(Error::NotEnoughRandomness)?;
    }
    let mut s_sum = Scalar::ZERO();
    let mut r_sum = point_identity();
    let mut a_sum = point_identity();
    for i in 0..entries.len() {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        let a = decompress(pk).ok_or(Error::InvalidPublickey)?;
        if is_identity(point_mul_by_cofactor(a)) {
            VerifyResult::Err(Error::SmallOrderPoint)?;
        }
        let r_bytes = CompressedEdPoint::from_slice(&signature, 0, 32);
        let s_bytes = SerializedScalar::from_slice(&signature, 32, 32);
        if !check_canonical_scalar(s_bytes) {
            VerifyResult::Err(Error::InvalidS)?;
        }
        let r = decompress(r_bytes).ok_or(Error::InvalidR)?;
        let s = Scalar::from_byte_seq_le(s_bytes);
        let c = scalar_from_hash(sha512(&r_bytes.concat(&pk).concat(&msg)));

        let z = entropy.slice(16 * i, 16);
        let z = Scalar::from_byte_seq_le(z.concat(&ByteSeq::new(16)));

        s_sum = s_sum + s * z;
        r_sum = point_add(r_sum, point_mul(z, r));
        a_sum = point_add(a_sum, point_mul(z * c, a))
    }

    let b = decompress(BASE).unwrap();
    let sb = point_mul(s_sum, b);
    let check = point_mul_by_cofactor(point_add(point_neg(sb), point_add(r_sum, a_sum)));
    if is_identity(check) {
        VerifyResult::Ok(())
    } else {
        VerifyResult::Err(Error::InvalidSignature)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use hacspec_dev::prelude::*;

    #[test]
    fn test_compress_decompress() {
        let sk = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));
        let b = decompress(BASE).unwrap();
        let a = point_mul(sk, b);
        let r = compress(a);
        assert!(point_eq(a, decompress(r).unwrap()));
    }

    // Test that shows that cofactorless batch verification can be flaky.
    // ie. on the same input it can both accept and reject.
    #[test]
    fn test_cofactorless_flaky() {
        let b = decompress(BASE).unwrap();
        let small_order_point = decompress(CompressedEdPoint::from_hex(
            "C7176A703D4DD84FBA3C0B760D10670F2A2053FA2C39CCC64EC7FD7792AC037A",
        ))
        .unwrap();
        let msg = ByteSeq::from_public_slice(b"hello test");

        let s = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));

        let r = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        ));

        let ap = point_add(point_mul(s, b), small_order_point);
        let rp = point_mul(r, b);
        let ap_bytes = compress(ap);
        let rp_bytes = compress(rp);
        let c = scalar_from_hash(sha512(&rp_bytes.concat(&ap_bytes).concat(&msg)));

        let sp = r + c * s;
        let sig = Signature::new()
            .update(0, &rp_bytes)
            .update(32, &sp.to_byte_seq_le());
        assert!(ietf_cofactorless_verify(ap_bytes, sig, &msg).is_err());

        let mut entry = Seq::<BatchEntry>::new(1);
        entry[0] = BatchEntry(ap_bytes, msg, sig);
        let mut no_f = 0;
        let mut no_t = 0;
        for _ in 0..64 {
            let entropy = rand::random_byte_vec(16);
            let entropy = ByteSeq::from_public_slice(&entropy);
            if ietf_cofactorless_batch_verify(&entry, &entropy).is_ok() {
                no_t += 1;
            } else {
                no_f += 1;
            }
        }
        println!("no_t: {}\nno_f: {}", no_t, no_f);
        assert!(0 < no_t);
        assert!(0 < no_f);
    }

    #[test]
    fn test_cofactored_not_flaky() {
        let b = decompress(BASE).unwrap();
        let small_order_point = decompress(CompressedEdPoint::from_hex(
            "C7176A703D4DD84FBA3C0B760D10670F2A2053FA2C39CCC64EC7FD7792AC037A",
        ))
        .unwrap();
        let msg = ByteSeq::from_public_slice(b"hello test");

        let s = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "9d61b19deffd5a60ba844af492ec2cc44449c5697b326919703bac031cae7f60",
        ));

        let r = Scalar::from_byte_seq_le(SerializedScalar::from_hex(
            "4ccd089b28ff96da9db6c346ec114e0f5b8a319f35aba624da8cf6ed4fb8a6fb",
        ));

        let ap = point_add(point_mul(s, b), small_order_point);
        let rp = point_mul(r, b);
        let ap_bytes = compress(ap);
        let rp_bytes = compress(rp);
        let c = scalar_from_hash(sha512(&rp_bytes.concat(&ap_bytes).concat(&msg)));

        let sp = r + c * s;
        let sig = Signature::new()
            .update(0, &rp_bytes)
            .update(32, &sp.to_byte_seq_le());
        assert!(zcash_verify(ap_bytes, sig, &msg).is_ok());

        let mut entry = Seq::<BatchEntry>::new(1);
        entry[0] = BatchEntry(ap_bytes, msg, sig);
        let mut no_f = 0;
        let mut no_t = 0;
        for _ in 0..32 {
            let entropy = rand::random_byte_vec(16);
            let entropy = ByteSeq::from_public_slice(&entropy);
            if ietf_cofactored_batch_verify(&entry, &entropy).is_ok() {
                no_t += 1;
            } else {
                no_f += 1;
            }
        }
        println!("no_t: {}\nno_f: {}", no_t, no_f);
        assert!(0 < no_t);
        assert!(0 == no_f);
    }
}
