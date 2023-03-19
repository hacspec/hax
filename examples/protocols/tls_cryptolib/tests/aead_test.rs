use hacspec_lib::*;
use tls_cryptolib::*;

#[test]
fn aead() {
    let k = ByteSeq::from_hex("0123456789abcdef0123456789abcdef");
    let iv = ByteSeq::from_hex("151515151515151515151515");
    let payload = ByteSeq::from_public_slice("This is the plaintext message".as_bytes());
    let ad = ByteSeq::from_public_slice("Some additional data".as_bytes());
    let ctxt =
        aead_encrypt(&AeadAlgorithm::Aes128Gcm, &k, &iv, &payload, &ad).expect("Error encrypting");
    let ptxt =
        aead_decrypt(&AeadAlgorithm::Aes128Gcm, &k, &iv, &ctxt, &ad).expect("Error decrypting");
    assert_secret_seq_eq!(payload, ptxt, U8);

    let k = ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    let iv = ByteSeq::from_hex("151515151515151515151515");
    let payload = ByteSeq::from_public_slice("This is the plaintext message".as_bytes());
    let ad = ByteSeq::from_public_slice("Some additional data".as_bytes());
    let ctxt = aead_encrypt(&AeadAlgorithm::Chacha20Poly1305, &k, &iv, &payload, &ad)
        .expect("Error encrypting");
    let ptxt = aead_decrypt(&AeadAlgorithm::Chacha20Poly1305, &k, &iv, &ctxt, &ad)
        .expect("Error decrypting");
    assert_secret_seq_eq!(payload, ptxt, U8);
}
