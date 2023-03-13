use hacspec_lib::*;
use tls_cryptolib::*;

#[test]
fn constants() {
    assert_eq!(32, kem_priv_len(&NamedGroup::X25519));
    assert_eq!(32, kem_priv_len(&NamedGroup::Secp256r1));
    assert_eq!(32, kem_pub_len(&KemScheme::X25519));
    assert_eq!(64, kem_pub_len(&KemScheme::Secp256r1));
}

#[test]
fn priv_to_pub() {
    let sk = ByteSeq::from_hex("14");
    let p = kem_priv_to_pub(&NamedGroup::Secp256r1, &sk).expect("Error in ECDH");
    let expected_p = ByteSeq::from_hex("83A01A9378395BAB9BCD6A0AD03CC56D56E6B19250465A94A234DC4C6B28DA9A76E49B6DE2F73234AE6A5EB9D612B75C9F2202BB6923F54FF8240AAA86F640B8");
    assert_secret_seq_eq!(p, expected_p, U8);
}

#[test]
fn keygen() {
    let entropy =
        ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    let _k = kem_keygen(&NamedGroup::X25519, entropy).expect("Error generating key");
}

// Returns ((k, enc), (pk, sk))
fn encap() -> ((ByteSeq, ByteSeq), (ByteSeq, ByteSeq)) {
    let entropy =
        ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    let (sk, pk) = kem_keygen(&NamedGroup::Secp256r1, entropy).expect("Error generating key");
    let entropy =
        ByteSeq::from_hex("0123456789abcdef0123456789abcdef0123456789abcdef0123456789abcdef");
    (
        kem_encap(&NamedGroup::Secp256r1, &pk, entropy).expect("Error encapsulating"),
        (pk, sk),
    )
}

#[test]
fn encaps() {
    let _ = encap();
}

#[test]
fn decaps() {
    let ((k, enc), (_pk, sk)) = encap();
    let k_dec = kem_decap(&NamedGroup::Secp256r1, &enc, sk).expect("Error in decaps");
    assert_secret_seq_eq!(k, k_dec, U8);
}
