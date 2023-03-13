use hacspec_lib::*;
use hacspec_p256::*;
use hacspec_sha256::*;

#[derive(Debug)]
pub enum Error {
    InvalidScalar,
    InvalidSignature,
}

pub type P256PublicKey = Affine;
pub type P256SecretKey = P256Scalar;
pub type P256Signature = (P256Scalar, P256Scalar); // (r, s)
pub type P256SignatureResult = Result<P256Signature, Error>;
pub type P256VerifyResult = Result<(), Error>;
type CheckResult = Result<(), Error>;
type ArithmeticResult = Result<Affine, Error>;

fn check_scalar_zero(r: P256Scalar) -> CheckResult {
    if r.equal(P256Scalar::ZERO()) {
        CheckResult::Err(Error::InvalidScalar)
    } else {
        CheckResult::Ok(())
    }
}

fn ecdsa_point_mul_base(x: P256Scalar) -> ArithmeticResult {
    match p256_point_mul_base(x) {
        AffineResult::Ok(s) => ArithmeticResult::Ok(s),
        AffineResult::Err(_) => ArithmeticResult::Err(Error::InvalidScalar),
    }
}

fn ecdsa_point_mul(k: P256Scalar, p: Affine) -> ArithmeticResult {
    match p256_point_mul(k, p) {
        AffineResult::Ok(s) => ArithmeticResult::Ok(s),
        AffineResult::Err(_) => ArithmeticResult::Err(Error::InvalidScalar),
    }
}

fn ecdsa_point_add(p: Affine, q: Affine) -> ArithmeticResult {
    match point_add(p, q) {
        AffineResult::Ok(s) => ArithmeticResult::Ok(s),
        AffineResult::Err(_) => ArithmeticResult::Err(Error::InvalidScalar),
    }
}

fn sign(payload: &ByteSeq, sk: P256SecretKey, nonce: P256Scalar) -> P256SignatureResult {
    check_scalar_zero(nonce)?;
    let (k_x, _k_y) = ecdsa_point_mul_base(nonce)?;
    let r = P256Scalar::from_byte_seq_be(&k_x.to_byte_seq_be());
    check_scalar_zero(r)?;
    let payload_hash = hash(payload);
    let payload_hash = P256Scalar::from_byte_seq_be(&payload_hash);
    let rsk = r * sk;
    let hash_rsk = payload_hash + rsk;
    let nonce_inv = nonce.inv();
    let s = nonce_inv * hash_rsk;

    P256SignatureResult::Ok((r, s))
}

pub fn ecdsa_p256_sha256_sign(
    payload: &ByteSeq,
    sk: P256SecretKey,
    nonce: P256Scalar,
) -> P256SignatureResult {
    sign(payload, sk, nonce)
}

fn verify(payload: &ByteSeq, pk: P256PublicKey, signature: P256Signature) -> P256VerifyResult {
    // signature = (r, s) must be in [1, n-1] because they are Scalars
    let (r, s) = signature;
    let payload_hash = hash(payload);
    let payload_hash = P256Scalar::from_byte_seq_be(&payload_hash);
    let s_inv = s.inv();

    // R' = (h * s1) * G + (r * s1) * pubKey
    let u1 = payload_hash * s_inv;
    let u1 = ecdsa_point_mul_base(u1)?;

    let u2 = r * s_inv;
    let u2 = ecdsa_point_mul(u2, pk)?;
    let (x, _y) = ecdsa_point_add(u1, u2)?;
    let x = P256Scalar::from_byte_seq_be(&x.to_byte_seq_be());

    if x == r {
        P256VerifyResult::Ok(())
    } else {
        P256VerifyResult::Err(Error::InvalidSignature)
    }
}

pub fn ecdsa_p256_sha256_verify(
    payload: &ByteSeq,
    pk: P256PublicKey,
    signature: P256Signature,
) -> P256VerifyResult {
    verify(payload, pk, signature)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn self_test() {
        let sk = P256Scalar::from_hex(
            "ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550",
        );
        let pk = (
            P256FieldElement::from_hex(
                "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
            ),
            P256FieldElement::from_hex(
                "B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A",
            ),
        );
        let msg = ByteSeq::from_public_slice(b"hacspec ecdsa p256 sha256 self test");
        let nonce = P256Scalar::from_be_bytes(&[1, 2, 3, 4, 5, 6, 7, 8, 9, 0]);

        let signature = match sign(&msg, sk, nonce) {
            Ok(s) => s,
            Err(_) => panic!("Error signing"),
        };
        assert!(verify(&msg, pk, signature).is_ok());
    }

    #[test]
    fn kat_sign() {
        let pk = (
            P256FieldElement::from_hex(
                "2927b10512bae3eddcfe467828128bad2903269919f7086069c8c4df6c732838",
            ),
            P256FieldElement::from_hex(
                "c7787964eaac00e5921fb1498a60f4606766b3d9685001558d1a974e7341513e",
            ),
        );
        let msg = ByteSeq::from_hex("313233343030");
        let sig = (
            P256Scalar::from_hex(
                "2ba3a8be6b94d5ec80a6d9d1190a436effe50d85a1eee859b8cc6af9bd5c2e18",
            ),
            P256Scalar::from_hex(
                "b329f479a2bbd0a5c384ee1493b1f5186a87139cac5df4087c134b49156847db",
            ),
        );
        assert!(verify(&msg, pk, sig).is_ok());
    }
}
