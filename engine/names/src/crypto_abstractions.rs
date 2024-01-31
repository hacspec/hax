use hax_lib_protocol::crypto::*;

fn crypto_abstractions() {
    let bytes = vec![0u8; 32];
    let iv = AEADIV::from_bytes(&bytes);
    let key = AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, &bytes);

    let (cipher_text, _tag) = aead_encrypt(key, iv, &bytes, &bytes);
    let iv = AEADIV::from_bytes(&bytes);
    let key = AEADKey::from_bytes(AEADAlgorithm::Chacha20Poly1305, &bytes);
    let _ = aead_decrypt(key, iv, &bytes, &cipher_text, AEADTag::from_bytes(&bytes));

    let p = DHElement::from_bytes(&bytes);
    let s = DHScalar::from_bytes(&bytes);
    dh_scalar_multiply(DHGroup::X25519, s.clone(), p);
    dh_scalar_multiply_base(DHGroup::X25519, s);

    let _ = hmac(HMACAlgorithm::Sha256, &bytes, &bytes);

    let _ = 1u64.to_le_bytes();
    let slice = &bytes[0..1];
    let _ = slice.len();
    let _ = slice.to_vec();
    let _ = [slice, slice].concat();
    let mut v = vec![0];
    v.extend_from_slice(slice);
    v.truncate(1);

    let _ = hash(HashAlgorithm::Sha256, &bytes);
    let _ = cipher_text.clone();
}
