/// A module that wraps all the generic crypto needed by TLS 1.3
/// Each function below should be supported by a standard crypto library
///
/// This module uses hacspec crypto implementations.
use hacspec_lib::*;

use hacspec_aes::*;
use hacspec_aes128_gcm::*;
use hacspec_chacha20::*;
use hacspec_chacha20poly1305::*;
use hacspec_curve25519::*;
use hacspec_ecdsa_p256_sha256::*;
use hacspec_gf128::*;
use hacspec_hkdf::*;
use hacspec_hmac::*;
use hacspec_p256::*;
use hacspec_poly1305::*;
use hacspec_sha256::*;

// Error types
#[derive(Debug)]
pub enum CryptoError {
    CryptoError,
    HkdfError,
    InsufficientEntropy,
    InvalidCert,
    MacFailed,
    UnsupportedAlgorithm,
    VerifyFailed,
}

// === An alias for bytes and some helper functions. === //
pub fn empty() -> ByteSeq {
    ByteSeq::new(0)
}

pub fn zeros(u: usize) -> ByteSeq {
    ByteSeq::new(u)
}

pub type Entropy = ByteSeq;
bytes!(Random, 32);

// === A number of type aliases for different byte types. === //
pub type DhSk = ByteSeq;
pub type DhPk = ByteSeq;
pub type SignatureKey = ByteSeq;
pub type VerificationKey = ByteSeq;
pub type MacKey = ByteSeq;
pub type AeadKey = ByteSeq;
pub type Key = ByteSeq;
pub type PSK = Key;
pub type Digest = ByteSeq;
pub type HMAC = ByteSeq;
pub type Signature = ByteSeq;
pub type AeadIv = ByteSeq;

pub type AeadKeyIV = (AeadKey, AeadIv);

// === Enums for configuring TLS. === //

#[derive(Clone, Copy, PartialEq)]
pub enum NamedGroup {
    X25519,
    Secp256r1,
}

#[derive(Clone, Copy, PartialEq)]
pub enum HashAlgorithm {
    SHA256,
    SHA384,
}

#[derive(Clone, Copy, PartialEq)]
pub enum AeadAlgorithm {
    Chacha20Poly1305,
    Aes128Gcm,
    Aes256Gcm,
}

#[derive(Clone, Copy, PartialEq, Debug)]
pub enum SignatureScheme {
    ED25519,
    EcdsaSecp256r1Sha256,
    RsaPssRsaSha256,
}

// === Helper functions to get the length of different configurations. === //

pub fn hash_len(ha: &HashAlgorithm) -> usize {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48,
    }
}

pub fn hmac_key_len(ha: &HashAlgorithm) -> usize {
    match ha {
        HashAlgorithm::SHA256 => 32,
        HashAlgorithm::SHA384 => 48,
    }
}
pub fn ae_key_len(ae: &AeadAlgorithm) -> usize {
    match ae {
        AeadAlgorithm::Chacha20Poly1305 => 32,
        AeadAlgorithm::Aes128Gcm => 16,
        AeadAlgorithm::Aes256Gcm => 16,
    }
}

pub fn ae_iv_len(ae: &AeadAlgorithm) -> usize {
    match ae {
        AeadAlgorithm::Chacha20Poly1305 => 12,
        AeadAlgorithm::Aes128Gcm => 12,
        AeadAlgorithm::Aes256Gcm => 12,
    }
}

pub fn dh_priv_len(gn: &NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::Secp256r1 => 32,
    }
}

pub fn dh_pub_len(gn: &NamedGroup) -> usize {
    match gn {
        NamedGroup::X25519 => 32,
        NamedGroup::Secp256r1 => 64,
    }
}

pub fn zero_key(ha: &HashAlgorithm) -> Key {
    Key::new(hash_len(ha) as usize)
}

// === ECDH === //

// Convert a DH secret key to the corresponding public key in the given group
pub fn secret_to_public(group_name: &NamedGroup, x: &DhSk) -> Result<DhPk, CryptoError> {
    match group_name {
        NamedGroup::Secp256r1 => match p256_point_mul_base(P256Scalar::from_byte_seq_be(x)) {
            AffineResult::Ok((x, y)) => {
                Result::<DhPk, CryptoError>::Ok(x.to_byte_seq_be().concat(&y.to_byte_seq_be()))
            }
            AffineResult::Err(_) => Result::<DhPk, CryptoError>::Err(CryptoError::CryptoError),
        },
        NamedGroup::X25519 => Result::<DhPk, CryptoError>::Ok(DhPk::from_seq(
            &x25519_secret_to_public(X25519SerializedScalar::from_seq(x)),
        )),
    }
}

fn p256_check_point_len(p: &DhPk) -> Result<(), CryptoError> {
    if p.len() != 64 {
        Result::<(), CryptoError>::Err(CryptoError::CryptoError)
    } else {
        Result::<(), CryptoError>::Ok(())
    }
}

fn p256_ecdh(x: &DhSk, y: &DhPk) -> Result<Key, CryptoError> {
    p256_check_point_len(y)?;
    let pk = (
        P256FieldElement::from_byte_seq_be(&y.slice_range(0..32)),
        P256FieldElement::from_byte_seq_be(&y.slice_range(32..64)),
    );
    match p256_point_mul(P256Scalar::from_byte_seq_be(x), pk) {
        AffineResult::Ok((x, y)) => {
            Result::<Key, CryptoError>::Ok(x.to_byte_seq_be().concat(&y.to_byte_seq_be()))
        }
        AffineResult::Err(_) => Result::<Key, CryptoError>::Err(CryptoError::CryptoError),
    }
}

pub fn ecdh(group_name: &NamedGroup, x: &DhSk, y: &DhPk) -> Result<Key, CryptoError> {
    match group_name {
        NamedGroup::Secp256r1 => p256_ecdh(x, y),
        NamedGroup::X25519 => Result::<Key, CryptoError>::Ok(DhPk::from_seq(&x25519_scalarmult(
            X25519SerializedScalar::from_seq(x),
            X25519SerializedPoint::from_seq(y),
        ))),
    }
}

// === Key Encapsulation === //

pub type KemScheme = NamedGroup;
pub type KemSk = ByteSeq;
pub type KemPk = ByteSeq;

pub fn kem_priv_len(ks: &KemScheme) -> usize {
    dh_priv_len(ks)
}

pub fn kem_pub_len(ks: &KemScheme) -> usize {
    dh_pub_len(ks)
}

pub fn kem_priv_to_pub(ks: &KemScheme, sk: &KemSk) -> Result<KemPk, CryptoError> {
    secret_to_public(ks, sk)
}

fn kem_keygen_inner(ks: &KemScheme, ent: Entropy) -> Result<(KemSk, KemPk), CryptoError> {
    let sk = KemSk::from_seq(&ent.slice_range(0..dh_priv_len(ks)));
    let pk = kem_priv_to_pub(ks, &sk)?;
    Result::<(KemSk, KemPk), CryptoError>::Ok((sk, pk))
}

pub fn kem_keygen(ks: &KemScheme, ent: Entropy) -> Result<(KemSk, KemPk), CryptoError> {
    if ent.len() < dh_priv_len(ks) {
        Result::<(KemSk, KemPk), CryptoError>::Err(CryptoError::InsufficientEntropy)
    } else {
        kem_keygen_inner(ks, ent)
    }
}

pub fn kem_encap(ks: &KemScheme, pk: &KemPk, ent: Entropy) -> Result<(Key, ByteSeq), CryptoError> {
    let (x, gx) = kem_keygen(ks, ent)?;
    let gxy = ecdh(ks, &x, pk)?;
    Result::<(Key, ByteSeq), CryptoError>::Ok((gxy, gx))
}

pub fn kem_decap(ks: &KemScheme, ct: &ByteSeq, sk: KemSk) -> Result<Key, CryptoError> {
    let gxy = ecdh(ks, &sk, ct)?;
    Result::<Key, CryptoError>::Ok(gxy)
}

// === Hashing === //

pub fn hash(ha: &HashAlgorithm, payload: &ByteSeq) -> Result<Digest, CryptoError> {
    match ha {
        HashAlgorithm::SHA256 => {
            Result::<Digest, CryptoError>::Ok(Digest::from_seq(&sha256(payload)))
        }
        HashAlgorithm::SHA384 => {
            Result::<Digest, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
    }
}

// === HMAC === //

pub fn hmac_tag(ha: &HashAlgorithm, mk: &MacKey, payload: &ByteSeq) -> Result<HMAC, CryptoError> {
    match ha {
        HashAlgorithm::SHA256 => {
            Result::<HMAC, CryptoError>::Ok(HMAC::from_seq(&hmac(mk, payload)))
        }
        HashAlgorithm::SHA384 => {
            Result::<HMAC, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
    }
}

fn check_tag_len(a: &HMAC, b: &HMAC) -> Result<(), CryptoError> {
    if a.len() == b.len() {
        Result::<(), CryptoError>::Ok(())
    } else {
        Result::<(), CryptoError>::Err(CryptoError::MacFailed)
    }
}

fn check_bytes(a: U8, b: U8) -> Result<(), CryptoError> {
    if !a.equal(b) {
        Result::<(), CryptoError>::Err(CryptoError::MacFailed)
    } else {
        Result::<(), CryptoError>::Ok(())
    }
}

pub fn hmac_verify(
    ha: &HashAlgorithm,
    mk: &MacKey,
    payload: &ByteSeq,
    m: &HMAC,
) -> Result<(), CryptoError> {
    let my_hmac = hmac_tag(ha, mk, payload)?;
    check_tag_len(m, &my_hmac)?;
    for i in 0..m.len() {
        check_bytes(my_hmac[i], m[i])?;
    }
    Result::<(), CryptoError>::Ok(())
}

// === Signatures === //

bytes!(EcOidTag, 9);

// Some ASN.1 helper functions
fn get_length_length(b: &ByteSeq) -> usize {
    if U8::declassify(b[0]) >> 7 == 1u8 {
        declassify_usize_from_U8(b[0] & U8(0x7fu8))
    } else {
        0
    }
}
fn get_length(b: &ByteSeq, len: usize) -> usize {
    declassify_u32_from_U32(U32_from_be_bytes(U32Word::from_slice(b, 0, len))) as usize
        >> ((4 - len) * 8)
}
fn get_short_length(b: &ByteSeq) -> usize {
    declassify_usize_from_U8(b[0] & U8(0x7fu8))
}

// Very basic ASN.1 parser to read the ECDSA public key from an X.509 certificate.
pub fn verification_key_from_cert(cert: &ByteSeq) -> Result<VerificationKey, CryptoError> {
    // cert is an ASN.1 sequence. Take the first sequence inside the outer.
    // Skip 1 + length bytes
    let skip = 2 + get_length_length(&cert.slice_range(1..cert.len())) + 1;
    let seq1_len_len = get_length_length(&cert.slice_range(skip..cert.len()));
    let skip = skip + 1;
    let seq1_len = get_length(&cert.slice(skip, cert.len() - skip), seq1_len_len);
    let mut seq1 = cert.slice_range(skip + seq1_len_len..skip + seq1_len_len + seq1_len);

    // Read sequences until we find the ecPublicKey (we don't support anything else right now)
    let mut pk = VerificationKey::new(0);
    // XXX: the typechecker should allow _ here. We don't need the counter.  #135
    for _i in 0..seq1.len() {
        // FIXME: we really need a break statement.
        if seq1.len() > 0 {
            let element_type = U8::declassify(seq1[0]);
            seq1 = seq1.slice(1, seq1.len() - 1);
            let len_len = get_length_length(&seq1);
            let mut len = get_short_length(&seq1);
            seq1 = seq1.slice(1, seq1.len() - 1);
            if len_len != 0 {
                len = get_length(&seq1, len_len) + len_len;
            }
            // XXX: Unfortunately we can't break so we don't go in here if we have
            //      the pk already.
            if element_type == 0x30u8 && pk.len() == 0 {
                // peek into this sequence to see if sequence again with an ecPublicKey
                // as first element
                let seq2 = seq1.slice(len_len, len);
                let element_type = U8::declassify(seq2[0]);
                let seq2 = seq2.slice(1, seq2.len() - 1);
                if element_type == 0x30u8 {
                    let len_len = get_length_length(&seq2);
                    if len_len == 0 {
                        let oid_len = get_short_length(&seq2);
                        if oid_len >= 9 {
                            // ecPublicKey oid incl tag: 06 07 2A 86 48 CE 3D 02 01
                            // FIXME: This shouldn't be necessary. Instead public_byte_seq!
                            //        should be added to the typechecker. #136
                            let expected = ByteSeq::from_seq(&EcOidTag(secret_bytes!([
                                0x06u8, 0x07u8, 0x2Au8, 0x86u8, 0x48u8, 0xCEu8, 0x3Du8, 0x02u8,
                                0x01u8
                            ])));
                            let oid = seq2.slice(1, 9);
                            let mut ec_pk_oid = true;
                            for i in 0..9 {
                                let oid_byte_equal =
                                    U8::declassify(oid[i]) == U8::declassify(expected[i]);
                                ec_pk_oid = ec_pk_oid && oid_byte_equal;
                            }
                            if ec_pk_oid {
                                // We have an ecPublicKey, skip the inner sequences
                                // and read the public key from the bit string
                                let bit_string = seq2.slice(oid_len + 1, seq2.len() - oid_len - 1);
                                // We only support uncompressed points
                                if U8::declassify(bit_string[0]) == 0x03u8 {
                                    let pk_len = declassify_usize_from_U8(bit_string[1]); // 42
                                    let _zeroes = declassify_usize_from_U8(bit_string[2]); // 00
                                    let _uncompressed = declassify_usize_from_U8(bit_string[3]); // 04
                                    pk = bit_string.slice(4, pk_len - 2);
                                }
                            }
                        }
                    }
                }
            }
            seq1 = seq1.slice(len, seq1.len() - len);
        }
    }
    if pk.len() == 0 {
        Result::<VerificationKey, CryptoError>::Err(CryptoError::InvalidCert)
    } else {
        Result::<VerificationKey, CryptoError>::Ok(pk)
    }
}

fn concat_signature(r: P256Scalar, s: P256Scalar) -> Result<Signature, CryptoError> {
    let signature = Signature::new(0)
        .concat(&r.to_byte_seq_be())
        .concat(&s.to_byte_seq_be());
    Result::<Signature, CryptoError>::Ok(signature)
}

fn p256_sign(ps: &SignatureKey, payload: &ByteSeq, ent: Entropy) -> Result<Signature, CryptoError> {
    let random = Random::from_seq(&ent.slice_range(0..32));
    // FIXME: #138 return an error when nonce is not a valid scalar value.
    let nonce = P256Scalar::from_byte_seq_be(&random);
    match ecdsa_p256_sha256_sign(payload, P256Scalar::from_byte_seq_be(ps), nonce) {
        // The ASN.1 encoding happens later on the outside.
        P256SignatureResult::Ok((r, s)) => concat_signature(r, s),
        P256SignatureResult::Err(_) => Result::<Signature, CryptoError>::Err(CryptoError::CryptoError),
    }
}

pub fn sign(
    sa: &SignatureScheme,
    ps: &SignatureKey,
    payload: &ByteSeq,
    ent: Entropy,
) -> Result<Signature, CryptoError> {
    match sa {
        SignatureScheme::EcdsaSecp256r1Sha256 => p256_sign(ps, payload, ent),
        SignatureScheme::ED25519 => {
            Result::<Signature, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
        SignatureScheme::RsaPssRsaSha256 => {
            Result::<Signature, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
    }
}

fn p256_verify(pk: &VerificationKey, payload: &ByteSeq, sig: &ByteSeq) -> Result<(), CryptoError> {
    let (pk_x, pk_y) = (
        P256FieldElement::from_byte_seq_be(&pk.slice(0, 32)),
        P256FieldElement::from_byte_seq_be(&pk.slice(32, 32)),
    );
    let (r, s) = (
        P256Scalar::from_byte_seq_be(&sig.slice(0, 32)),
        P256Scalar::from_byte_seq_be(&sig.slice(32, 32)),
    );
    match ecdsa_p256_sha256_verify(payload, (pk_x, pk_y), (r, s)) {
        P256VerifyResult::Ok(()) => Result::<(), CryptoError>::Ok(()),
        P256VerifyResult::Err(_) => Result::<(), CryptoError>::Err(CryptoError::VerifyFailed),
    }
}

pub fn verify(
    sa: &SignatureScheme,
    pk: &VerificationKey,
    payload: &ByteSeq,
    sig: &ByteSeq,
) -> Result<(), CryptoError> {
    match sa {
        SignatureScheme::EcdsaSecp256r1Sha256 => p256_verify(pk, payload, sig),
        SignatureScheme::ED25519 => {
            Result::<(), CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
        SignatureScheme::RsaPssRsaSha256 => {
            Result::<(), CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
    }
}

// === HKDF === //

pub fn hkdf_extract(ha: &HashAlgorithm, k: &Key, salt: &Key) -> Result<Key, CryptoError> {
    match ha {
        HashAlgorithm::SHA256 => Result::<Key, CryptoError>::Ok(Key::from_seq(&extract(salt, k))),
        HashAlgorithm::SHA384 => Result::<Key, CryptoError>::Err(CryptoError::UnsupportedAlgorithm),
    }
}

pub fn hkdf_expand(
    ha: &HashAlgorithm,
    k: &Key,
    info: &ByteSeq,
    len: usize,
) -> Result<Key, CryptoError> {
    match ha {
        HashAlgorithm::SHA256 => match expand(k, info, len) {
            HkdfByteSeqResult::Ok(b) => Result::<Key, CryptoError>::Ok(Key::from_seq(&b)),
            HkdfByteSeqResult::Err(_) => Result::<Key, CryptoError>::Err(CryptoError::HkdfError),
        },
        HashAlgorithm::SHA384 => Result::<Key, CryptoError>::Err(CryptoError::UnsupportedAlgorithm),
    }
}

// === AEAD === //

fn aes128_encrypt(
    k: &AeadKey,
    iv: &AeadIv,
    payload: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    let (ctxt, tag) = encrypt_aes128(Key128::from_seq(k), AesNonce::from_seq(iv), ad, payload);
    Result::<ByteSeq, CryptoError>::Ok(ctxt.concat(&ByteSeq::from_seq(&tag)))
}

fn chacha_encrypt(
    k: &AeadKey,
    iv: &AeadIv,
    payload: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    let (ctxt, tag) =
        chacha20_poly1305_encrypt(ChaChaKey::from_seq(k), ChaChaIV::from_seq(iv), ad, payload);
    Result::<ByteSeq, CryptoError>::Ok(ctxt.concat(&tag))
}

pub fn aead_encrypt(
    a: &AeadAlgorithm,
    k: &AeadKey,
    iv: &AeadIv,
    payload: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    match a {
        AeadAlgorithm::Aes128Gcm => aes128_encrypt(k, iv, payload, ad),
        AeadAlgorithm::Aes256Gcm => {
            Result::<ByteSeq, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
        AeadAlgorithm::Chacha20Poly1305 => chacha_encrypt(k, iv, payload, ad),
    }
}

fn aes128_decrypt(
    k: &AeadKey,
    iv: &AeadIv,
    ciphertext: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    match decrypt_aes128(
        Key128::from_seq(k),
        AesNonce::from_seq(iv),
        ad,
        &ciphertext.slice_range(0..ciphertext.len() - 16),
        Gf128Tag::from_seq(&ciphertext.slice_range(ciphertext.len() - 16..ciphertext.len())),
    ) {
        AesGcmByteSeqResult::Ok(m) => Result::<ByteSeq, CryptoError>::Ok(m),
        AesGcmByteSeqResult::Err(_) => Result::<ByteSeq, CryptoError>::Err(CryptoError::MacFailed),
    }
}

fn chacha_decrypt(
    k: &AeadKey,
    iv: &AeadIv,
    ciphertext: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    match chacha20_poly1305_decrypt(
        ChaChaKey::from_seq(k),
        ChaChaIV::from_seq(iv),
        ad,
        &ciphertext.slice_range(0..ciphertext.len() - 16),
        Poly1305Tag::from_seq(
            &ciphertext.slice_range(ciphertext.len() - 16..ciphertext.len()), // .declassify(),
        ),
    ) {
        ByteSeqResult::Ok(ptxt) => Result::<ByteSeq, CryptoError>::Ok(ptxt),
        ByteSeqResult::Err(_) => Result::<ByteSeq, CryptoError>::Err(CryptoError::MacFailed),
    }
}

pub fn aead_decrypt(
    a: &AeadAlgorithm,
    k: &AeadKey,
    iv: &AeadIv,
    ciphertext: &ByteSeq,
    ad: &ByteSeq,
) -> Result<ByteSeq, CryptoError> {
    match a {
        AeadAlgorithm::Aes128Gcm => aes128_decrypt(k, iv, ciphertext, ad),
        AeadAlgorithm::Aes256Gcm => {
            Result::<ByteSeq, CryptoError>::Err(CryptoError::UnsupportedAlgorithm)
        }
        AeadAlgorithm::Chacha20Poly1305 => chacha_decrypt(k, iv, ciphertext, ad),
    }
}
