// Import hacspec and all needed definitions.
use hax_lib_protocol::crypto::{DHGroup, *};

/// This file formalizes the Crypto Functions from the Noise Specification
/// Section 4: Crypto Functions
/// https://noiseprotocol.org/noise.html#crypto-functions

pub enum Error {
    CryptoError,
}

/// Section 4.1 and 12.1: Diffie-Hellman Functions for Curve25519
pub struct KeyPair {
    private_key: DHScalar,
    pub public_key: Vec<u8>,
}

pub const DHLEN: usize = 32;

pub fn generate_keypair(sk: &[u8]) -> KeyPair {
    let sk = DHScalar::from_bytes(sk);
    let pk = dh_scalar_multiply_base(DHGroup::X25519, sk.clone());
    KeyPair {
        private_key: sk,
        public_key: pk,
    }
}

pub fn dh(sk: &KeyPair, pk: &[u8]) -> Vec<u8> {
    let pk = DHElement::from_bytes(pk);

    dh_scalar_multiply(DHGroup::X25519, sk.private_key.clone(), pk)
}

/// Section 4.2 and 12.3: Cipher functions for ChaCha20-Poly1305

pub fn encrypt(key: &[u8], counter: u64, aad: &[u8], plain: &[u8]) -> Vec<u8> {
    let mut chacha_iv = vec![0u8; 4];
    chacha_iv.extend_from_slice(&counter.to_le_bytes());
    let (mut cipher, tag) = aead_encrypt(
        AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, key),
        AEADIV::from_bytes(&chacha_iv),
        aad,
        plain,
    );
    cipher.extend_from_slice(&tag);
    cipher
}

pub fn decrypt(key: &[u8], counter: u64, aad: &[u8], cipher: &[u8]) -> Result<Vec<u8>, Error> {
    let mut chacha_iv = vec![0u8; 4];
    chacha_iv.extend_from_slice(&counter.to_le_bytes());
    let cipher_len = cipher.len() - 16;
    let cip = &cipher[0..cipher_len];
    let tag = &cipher[cipher_len..cipher.len()];
    aead_decrypt(
        AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, key),
        AEADIV::from_bytes(&chacha_iv),
        aad,
        cip,
        AEADTag::from_bytes(tag),
    )
    .map_err(|_| Error::CryptoError)
}

pub fn rekey(key: &[u8]) -> Vec<u8> {
    encrypt(key, 0xffffffffffffffffu64, &Vec::new(), &[0u8; 32])
}

/// Section 4.3 and 12.5: Hash functions for SHA-256

pub const HASHLEN: usize = 32;
pub const BLOCKLEN: usize = 64;

pub fn hash(input: &[u8]) -> Vec<u8> {
    hax_lib_protocol::crypto::hash(HashAlgorithm::Sha256, input)
}

pub fn hmac_hash(key: &[u8], input: &[u8]) -> Vec<u8> {
    hmac(HMACAlgorithm::Sha256, key, input)
}

/// HKDF spec as per Noise
/// Alternative would be to directly use HKDF

pub fn kdf_next(secret: &[u8], prev: &[u8], counter: u8) -> Vec<u8> {
    hmac_hash(secret, &[prev, &[counter]].concat())
}

pub fn hkdf1(key: &[u8], ikm: &[u8]) -> Vec<u8> {
    let secret = hmac_hash(key, ikm);
    kdf_next(&secret, &Vec::new(), 1)
}

pub fn hkdf2(key: &[u8], ikm: &[u8]) -> (Vec<u8>, Vec<u8>) {
    let secret = hmac_hash(key, ikm);
    let k1 = kdf_next(&secret, &Vec::new(), 1);
    let k2 = kdf_next(&secret, &k1, 2);
    (k1, k2)
}

pub fn hkdf3(key: &[u8], ikm: &[u8]) -> (Vec<u8>, Vec<u8>, Vec<u8>) {
    let secret = hmac_hash(key, ikm);
    let k1 = kdf_next(&secret, &Vec::new(), 1);
    let k2 = kdf_next(&secret, &k1, 2);
    let k3 = kdf_next(&secret, &k1, 3);
    (k1, k2, k3)
}
