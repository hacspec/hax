// Import hacspec and all needed definitions.
use hacspec_lib::*;

use hacspec_chacha20::*;
use hacspec_poly1305::*;
use hacspec_chacha20poly1305::*;
use hacspec_sha256::*;
use hacspec_hmac::*;
use hacspec_curve25519::*;
//use hacspec_hkdf::*;

/// This file formalizes the Crypto Functions from the Noise Specification 
/// Section 4: Crypto Functions
/// https://noiseprotocol.org/noise.html#crypto-functions

pub enum Error {
    CryptoError
}

/// Section 4.1 and 12.1: Diffie-Hellman Functions for Curve25519
pub struct KeyPair {
    private_key: X25519SerializedScalar,
    pub public_key: Seq<U8>
}

pub const DHLEN:usize=32;

pub fn generate_keypair(sk:&Seq<U8>) -> KeyPair {
    let sk = X25519SerializedScalar::from_seq(sk);
    let pk = Seq::from_seq(&x25519_secret_to_public(sk));
    KeyPair {private_key:sk, public_key:pk}
}

pub fn dh(sk:&KeyPair,pk:&Seq<U8>) -> Seq<U8> {
    let pk = X25519SerializedPoint::from_seq(pk);
    let secret = x25519_scalarmult(sk.private_key,pk);
    Seq::from_seq(&secret)
}

/// Section 4.2 and 12.3: Cipher functions for ChaCha20-Poly1305

pub fn encrypt(key:&Seq<U8>,counter:u64,aad:&Seq<U8>,plain:&Seq<U8>) -> Seq<U8> {
    let chacha_iv = Seq::<U8>::new(4).concat(&U64_to_le_bytes(U64(counter)));
    let (cipher,tag) = chacha20_poly1305_encrypt(
	ChaChaKey::from_seq(key),
	ChaChaIV::from_seq(&chacha_iv),
	aad,
	plain);
    cipher.concat(&tag)
}

pub fn decrypt(key:&Seq<U8>,counter:u64,aad:&Seq<U8>,cipher:&Seq<U8>) -> Result<Seq<U8>,Error> {
    let chacha_iv = Seq::<U8>::new(4).concat(&U64_to_le_bytes(U64(counter)));
    let cipher_len = cipher.len() - 16;
    let cip = cipher.slice(0,cipher_len);
    let tag = cipher.slice(cipher_len,16);
    chacha20_poly1305_decrypt(
	ChaChaKey::from_seq(key),
	ChaChaIV::from_seq(&chacha_iv),
	aad,
	&cip,
    Poly1305Tag::from_seq(&tag)).
        map_err(|_| Error::CryptoError)
}

pub fn rekey(key:&Seq<U8>) -> Seq<U8> {
    encrypt(key,0xffffffffffffffffu64,&Seq::new(0),&Seq::new(32))
}

/// Section 4.3 and 12.5: Hash functions for SHA-256

pub const HASHLEN:usize = 32;
pub const BLOCKLEN:usize = 64;

pub fn hash(input:&Seq<U8>) -> Seq<U8> {
    Seq::from_seq(&sha256(input))
}

pub fn hmac_hash(key:&Seq<U8>,input:&Seq<U8>) -> Seq<U8> {
    Seq::from_seq(&hmac(key,input))
}

/// HKDF spec as per Noise
/// Alternative would be to directly use HKDF

pub fn kdf_next(secret:&Seq<U8>,prev:&Seq<U8>,counter:u8) -> Seq<U8> {
    let mut ctr = Seq::new(1);
    ctr[0] = U8(counter);
    hmac_hash(secret,&prev.concat(&ctr))
}

pub fn hkdf1(key:&Seq<U8>,ikm:&Seq<U8>) -> Seq<U8> {
    let secret = hmac_hash(key,ikm);
    kdf_next(&secret,&Seq::new(0),1)
}

pub fn hkdf2(key:&Seq<U8>,ikm:&Seq<U8>) -> (Seq<U8>,Seq<U8>) {
    let secret = hmac_hash(key,ikm);
    let k1 = kdf_next(&secret,&Seq::new(0),1);
    let k2 = kdf_next(&secret,&k1,2);
    (k1,k2)
}

pub fn hkdf3(key:&Seq<U8>,ikm:&Seq<U8>) -> (Seq<U8>,Seq<U8>,Seq<U8>) {
    let secret = hmac_hash(key,ikm);
    let k1 = kdf_next(&secret,&Seq::new(0),1);
    let k2 = kdf_next(&secret,&k1,2);
    let k3 = kdf_next(&secret,&k1,3);
    (k1,k2,k3)
}



