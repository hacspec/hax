// Import hacspec and all needed definitions.
use hacspec_lib::*;

use crate::*;
use noise_crypto::*;

/// This module defines the generic Noise processing rules
/// Section 5: https://noiseprotocol.org/noise.html#processing-rules

pub struct CipherState {
    k: Option<Seq<U8>>,
    n: u64,
}

pub struct SymmetricState {
    cs: CipherState,
    ck: Seq<U8>,
    h: Seq<U8>,
}

/// 5.1: The CipherState Object

pub fn initialize_key(key: Option<Seq<U8>>) -> CipherState {
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
    ad: &Seq<U8>,
    plaintext: &Seq<U8>,
) -> Result<(CipherState, Seq<U8>), Error> {
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
            None => Ok((CipherState { k, n }, plaintext.clone())),
        }
    }
}

pub fn decrypt_with_ad(
    cs: CipherState,
    ad: &Seq<U8>,
    ciphertext: &Seq<U8>,
) -> Result<(CipherState, Seq<U8>), Error> {
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
            None => Ok((CipherState { k, n }, ciphertext.clone())),
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

pub fn initialize_symmetric(protocol_name: &Seq<U8>) -> SymmetricState {
    let pnlen = protocol_name.len();
    let mut hv: Seq<U8> = Seq::new(0);
    if pnlen < HASHLEN {
        hv = protocol_name.concat(&Seq::new(32 - pnlen));
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

pub fn mix_key(st: SymmetricState, input_key_material: &Seq<U8>) -> SymmetricState {
    let SymmetricState { cs: _, ck, h } = st;
    let (ck, mut temp_k) = hkdf2(&ck, input_key_material);
    if HASHLEN == 64 {
        temp_k = temp_k.slice(0, 32);
    }
    SymmetricState {
        cs: initialize_key(Some(temp_k)),
        ck,
        h,
    }
}

pub fn mix_hash(st: SymmetricState, data: &Seq<U8>) -> SymmetricState {
    let SymmetricState { cs, ck, h } = st;
    SymmetricState {
        cs,
        ck,
        h: hash(&h.concat(data)),
    }
}

pub fn mix_key_and_hash(st: SymmetricState, input_key_material: &Seq<U8>) -> SymmetricState {
    let SymmetricState { cs: _, ck, h } = st;
    let (ck, temp_h, mut temp_k) = hkdf3(&ck, input_key_material);
    let new_h = hash(&h.concat(&temp_h));
    if HASHLEN == 64 {
        temp_k = temp_k.slice(0, 32);
    }
    SymmetricState {
        cs: initialize_key(Some(temp_k)),
        ck,
        h: new_h,
    }
}

/// Unclear if we need a special function for psk or we can reuse mix_key_and_hash above
//pub fn mix_psk(st:SymmetricState,psk:&Seq<U8>) -> (Seq<U8>,Seq<U8>,Seq<U8>) {
//    let (ck,temp_hash,cs_k) = kdf3(key,psk);
//    let next_hash = mix_hash(prev_hash,&temp_hash);
//    (ck,cs_k,next_hash)
//}

pub fn encrypt_and_hash(
    st: SymmetricState,
    plaintext: &Seq<U8>,
) -> Result<(SymmetricState, Seq<U8>), Error> {
    let (new_cs, ciphertext) = encrypt_with_ad(st.cs, &st.h, plaintext)?;
    let new_h = hash(&st.h.concat(&ciphertext));
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
    ciphertext: &Seq<U8>,
) -> Result<(SymmetricState, Seq<U8>), Error> {
    let (new_cs, plaintext) = decrypt_with_ad(st.cs, &st.h, ciphertext)?;
    let new_h = hash(&st.h.concat(ciphertext));
    Ok((
        SymmetricState {
            cs: new_cs,
            ck: st.ck,
            h: new_h,
        },
        plaintext,
    ))
}

pub fn split(st: SymmetricState) -> (CipherState, CipherState, Seq<U8>) {
    let (mut temp_k1, mut temp_k2) = hkdf2(&st.ck, &Seq::new(0));
    if HASHLEN == 64 {
        temp_k1 = temp_k1.slice(0, 32);
        temp_k2 = temp_k2.slice(0, 32);
    }
    (
        initialize_key(Some(temp_k1)),
        initialize_key(Some(temp_k2)),
        st.h,
    )
}
