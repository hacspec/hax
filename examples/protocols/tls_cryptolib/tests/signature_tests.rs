use hacspec_lib::*;
use tls_cryptolib::*;

#[test]
fn sign_verify() {
    let payload = ByteSeq::from_public_slice("This is the message to be signed".as_bytes());
    let entropy =
        ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    let (sk, pk) = kem_keygen(&NamedGroup::Secp256r1, entropy).expect("Error generating keys");

    let entropy =
        ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    let signature = sign(
        &SignatureScheme::EcdsaSecp256r1Sha256,
        &sk,
        &payload,
        entropy,
    )
    .expect("Error signing");
    assert!(verify(
        &SignatureScheme::EcdsaSecp256r1Sha256,
        &pk,
        &payload,
        &signature
    )
    .is_ok());
}
