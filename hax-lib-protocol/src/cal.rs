//! This module defines a cryptographic abstraction layer for use in
//! hax protocol specifications.

use crate::ProtocolError;

use libcrux::ecdh::Algorithm;

#[derive(Clone)]
pub struct DHScalar(Vec<u8>);

impl DHScalar {
    pub fn from_bytes(_bytes: &[u8]) -> Self {
        todo!()
    }
}

pub struct DHElement(Vec<u8>);

impl DHElement {
    pub fn from_bytes(_bytes: &[u8]) -> Self {
        todo!()
    }
}

/// Scalar multiplication of [scalar] and [element].
pub fn dh_scalar_multiply(scalar: DHScalar, element: DHElement) -> Vec<u8> {
    libcrux::ecdh::derive(Algorithm::X25519, element.0, scalar.0).unwrap()
}

/// Scalar multiplication of a fixed generator and [scalar].
pub fn dh_scalar_multiply_base(scalar: DHScalar) -> Vec<u8> {
    libcrux::ecdh::secret_to_public(Algorithm::X25519, scalar.0).unwrap()
}

pub struct AEADKey(libcrux::aead::Key);

impl AEADKey {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        AEADKey(
            libcrux::aead::Key::from_bytes(
                libcrux::aead::Algorithm::Chacha20Poly1305,
                bytes.to_vec(),
            )
            .unwrap(),
        )
    }
}

pub struct AEADIV(libcrux::aead::Iv);

impl AEADIV {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        AEADIV(libcrux::aead::Iv::new(bytes).unwrap())
    }
}

pub struct AEADTag(libcrux::aead::Tag);
impl AEADTag {
    pub fn from_bytes(bytes: &[u8]) -> Self {
        let bytes: [u8; 16] = bytes.try_into().unwrap();
        AEADTag(libcrux::aead::Tag::from(bytes))
    }
}

pub fn aead_encrypt(key: AEADKey, iv: AEADIV, aad: &[u8], plain: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let (tag, cip) = libcrux::aead::encrypt_detached(&key.0, plain, iv.0, aad).unwrap();
    (cip, tag.as_ref().to_vec())
}

pub fn aead_decrypt(
    key: AEADKey,
    iv: AEADIV,
    aad: &[u8],
    cip: &[u8],
    tag: AEADTag,
) -> Result<Vec<u8>, ProtocolError> {
    libcrux::aead::decrypt_detached(&key.0, cip, iv.0, aad, &tag.0)
        .map_err(|_| ProtocolError::CryptoError)
}

pub fn hash(input: &[u8]) -> Vec<u8> {
    libcrux::digest::hash(libcrux::digest::Algorithm::Sha256, input)
}

pub fn hmac(key: &[u8], input: &[u8]) -> Vec<u8> {
    libcrux::hmac::hmac(libcrux::hmac::Algorithm::Sha256, key, input, None)
}
