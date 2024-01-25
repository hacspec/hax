// Import hacspec and all needed definitions.

use crate::*;
use noise_crypto::*;

/// This module defines the generic Noise processing rules
/// Section 5: https://noiseprotocol.org/noise.html#processing-rules

pub struct CipherState {
    k: Option<Vec<u8>>,
    n: u64,
}

pub struct SymmetricState {
    cs: CipherState,
    ck: Vec<u8>,
    h: Vec<u8>,
}

/// 5.1: The CipherState Object

pub fn initialize_key(key: Option<Vec<u8>>) -> CipherState {
    CipherState { k: key, n: 0u64 }
}

pub fn has_key(cs: &CipherState) -> bool {
    cs.k != None
}

pub fn set_nonce(cs: CipherState, n: u64) -> CipherState {
    let CipherState { k, n: _ } = cs;
    CipherState { k, n }
}

pub fn encrypt_with_ad(
    cs: CipherState,
    ad: &[u8],
    plaintext: &[u8],
) -> Result<(CipherState, Vec<u8>), Error> {
    let CipherState { k, n } = cs;
    if n == 0xffffffffffffffffu64 {
        Err(Error::CryptoError)
    } else {
        match k {
            Some(k) => {
                let cip = encrypt(&k, n, ad, plaintext);
                Ok((
                    CipherState {
                        k: Some(k),
                        n: n + 1,
                    },
                    cip,
                ))
            }
            None => Ok((CipherState { k, n }, plaintext.to_vec())),
        }
    }
}

pub fn decrypt_with_ad(
    cs: CipherState,
    ad: &[u8],
    ciphertext: &[u8],
) -> Result<(CipherState, Vec<u8>), Error> {
    let CipherState { k, n } = cs;
    if n == 0xffffffffffffffffu64 {
        Err(Error::CryptoError)
    } else {
        match k {
            Some(k) => {
                let plain = decrypt(&k, n, ad, ciphertext)?;
                Ok((
                    CipherState {
                        k: Some(k),
                        n: n + 1,
                    },
                    plain,
                ))
            }
            None => Ok((CipherState { k, n }, ciphertext.to_vec())),
        }
    }
}

pub fn rekey(cs: CipherState) -> Result<CipherState, Error> {
    let CipherState { k, n } = cs;
    match k {
        Some(k) => {
            let new_k = noise_crypto::rekey(&k);
            Ok(CipherState { k: Some(new_k), n })
        }
        None => Err(Error::CryptoError),
    }
}

/// 5.2: The SymmetricState Object

pub fn initialize_symmetric(protocol_name: &[u8]) -> SymmetricState {
    let pnlen = protocol_name.len();
    let hv: Vec<u8>;
    if pnlen < HASHLEN {
        hv = [protocol_name, &vec![0u8; 32 - pnlen]].concat();
    } else {
        hv = hash(protocol_name);
    }
    let ck = hv.clone();
    SymmetricState {
        cs: initialize_key(None),
        ck,
        h: hv,
    }
}

pub fn mix_key(st: SymmetricState, input_key_material: &[u8]) -> SymmetricState {
    let SymmetricState { cs: _, ck, h } = st;
    let (ck, mut temp_k) = hkdf2(&ck, input_key_material);
    if HASHLEN == 64 {
        temp_k.truncate(32);
    }
    SymmetricState {
        cs: initialize_key(Some(temp_k)),
        ck,
        h,
    }
}

pub fn mix_hash(st: SymmetricState, data: &[u8]) -> SymmetricState {
    let SymmetricState { cs, ck, h } = st;
    SymmetricState {
        cs,
        ck,
        h: hash(&[&h, data].concat()),
    }
}

pub fn mix_key_and_hash(st: SymmetricState, input_key_material: &[u8]) -> SymmetricState {
    let SymmetricState { cs: _, ck, h } = st;
    let (ck, temp_h, mut temp_k) = hkdf3(&ck, input_key_material);
    let mut new_h = h.clone();
    new_h.extend_from_slice(&temp_h);
    let new_h = hash(&new_h);
    if HASHLEN == 64 {
        temp_k.truncate(32);
    }
    SymmetricState {
        cs: initialize_key(Some(temp_k)),
        ck,
        h: new_h,
    }
}

/// Unclear if we need a special function for psk or we can reuse mix_key_and_hash above
//pub fn mix_psk(st:SymmetricState,psk:&[u8]) -> (Vec<u8>,Vec<u8>,Vec<u8>) {
//    let (ck,temp_hash,cs_k) = kdf3(key,psk);
//    let next_hash = mix_hash(prev_hash,&temp_hash);
//    (ck,cs_k,next_hash)
//}

pub fn encrypt_and_hash(
    st: SymmetricState,
    plaintext: &[u8],
) -> Result<(SymmetricState, Vec<u8>), Error> {
    let (new_cs, ciphertext) = encrypt_with_ad(st.cs, &st.h, plaintext)?;
    let mut new_h = st.h.clone();
    new_h.extend_from_slice(&ciphertext);
    let new_h = hash(&new_h);
    Ok((
        SymmetricState {
            cs: new_cs,
            ck: st.ck,
            h: new_h,
        },
        ciphertext,
    ))
}

pub fn decrypt_and_hash(
    st: SymmetricState,
    ciphertext: &[u8],
) -> Result<(SymmetricState, Vec<u8>), Error> {
    let (new_cs, plaintext) = decrypt_with_ad(st.cs, &st.h, ciphertext)?;
    let mut new_h = st.h.clone();
    new_h.extend_from_slice(&ciphertext);
    let new_h = hash(&new_h);
    Ok((
        SymmetricState {
            cs: new_cs,
            ck: st.ck,
            h: new_h,
        },
        plaintext,
    ))
}

pub fn split(st: SymmetricState) -> (CipherState, CipherState, Vec<u8>) {
    let (mut temp_k1, mut temp_k2) = hkdf2(&st.ck, &Vec::new());
    if HASHLEN == 64 {
        temp_k1.truncate(32);
        temp_k2.truncate(32);
    }
    (
        initialize_key(Some(temp_k1)),
        initialize_key(Some(temp_k2)),
        st.h,
    )
}
