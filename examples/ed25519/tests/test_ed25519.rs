use hacspec_dev::prelude::*;
use hacspec_ed25519::*;
use hacspec_edwards25519::*;
use hacspec_lib::*;
use quickcheck::QuickCheck;

// Test vectors from https://datatracker.ietf.org/doc/rfc8032
create_test_vectors!(
    IetfTestVector,
    secret_key: String,
    public_key: String,
    message: String,
    signature: String
);

// Test vectors from https://eprint.iacr.org/2020/1244.pdf
// https://github.com/novifinancial/ed25519-speccheck
create_test_vectors!(
    CasesTestVector,
    message: String,
    pub_key: String,
    signature: String
);

#[test]
fn test_secret_to_public() {
    let v: Vec<IetfTestVector> = IetfTestVector::from_file("tests/ietf_test_vectors.json");
    for t in v {
        let sk = SecretKey::from_hex(&t.secret_key);
        let pk = PublicKey::from_hex(&t.public_key);
        let pk_r = secret_to_public(sk);
        assert_bytes_eq!(pk, pk_r);
    }
}

#[test]
fn test_sign() {
    let v: Vec<IetfTestVector> = IetfTestVector::from_file("tests/ietf_test_vectors.json");
    for t in v {
        let sk = SecretKey::from_hex(&t.secret_key);
        let msg = ByteSeq::from_hex(&t.message);
        let sig = Signature::from_hex(&t.signature);
        let sig_r = sign(sk, &msg);
        assert_bytes_eq!(sig, sig_r);
    }
}

#[test]
fn test_verify() {
    let v: Vec<IetfTestVector> = IetfTestVector::from_file("tests/ietf_test_vectors.json");
    for t in v {
        let pk = PublicKey::from_hex(&t.public_key);
        let msg = ByteSeq::from_hex(&t.message);
        let sig = Signature::from_hex(&t.signature);
        assert!(zcash_verify(pk, sig, &msg).is_ok());
        assert!(ietf_cofactored_verify(pk, sig, &msg).is_ok());
        assert!(ietf_cofactorless_verify(pk, sig, &msg).is_ok());
        assert!(alg2_verify(pk, sig, &msg).is_ok());
    }
}

#[test]
fn test_sign_verify() {
    fn test_q(sk: (u128, u128), msg: String) -> bool {
        let (sk1, sk2) = sk;
        let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
        let sk = SecretKey::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = &ByteSeq::from_public_slice(msg.as_bytes());
        let sig = sign(sk, &msg);
        zcash_verify(pk, sig, &msg).is_ok()
            && ietf_cofactored_verify(pk, sig, &msg).is_ok()
            && ietf_cofactorless_verify(pk, sig, &msg).is_ok()
            && alg2_verify(pk, sig, &msg).is_ok()
    }
    QuickCheck::new()
        .tests(30)
        .quickcheck(test_q as fn((u128, u128), String) -> bool);
}

#[test]
fn test_batch() {
    let entropy = rand::random_byte_vec(512);
    let entropy = ByteSeq::from_public_slice(&entropy);
    let mut entries = Seq::<BatchEntry>::new(32);
    for i in 0..32usize {
        let sk = rand::random_byte_vec(32);
        let sk = SecretKey::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
        let sig = sign(sk, &msg);
        entries[i] = BatchEntry(pk, msg, sig);
    }
    assert!(zcash_batch_verify(&entries, &entropy).is_ok());
    assert!(ietf_cofactored_batch_verify(&entries, &entropy).is_ok());
    assert!(ietf_cofactorless_batch_verify(&entries, &entropy).is_ok());
    assert!(alg3_batch_verify(&entries, &entropy).is_ok());
}

#[test]
fn test_batch_bad() {
    let entropy = rand::random_byte_vec(512);
    let entropy = ByteSeq::from_public_slice(&entropy);
    let mut entries = Seq::<BatchEntry>::new(32);
    let bad_index = 10;
    for i in 0..32usize {
        let sk = rand::random_byte_vec(32);
        let sk = SecretKey::from_public_slice(&sk);
        let pk = secret_to_public(sk);
        let msg = ByteSeq::from_public_slice(b"BatchVerifyTest");
        let sig = if i != bad_index {
            sign(sk, &msg)
        } else {
            sign(sk, &ByteSeq::from_public_slice(b"badmsg"))
        };
        entries[i] = BatchEntry(pk, msg, sig);
    }
    assert!(zcash_batch_verify(&entries, &entropy).is_err());
    assert!(ietf_cofactored_batch_verify(&entries, &entropy).is_err());
    assert!(ietf_cofactorless_batch_verify(&entries, &entropy).is_err());
    assert!(alg3_batch_verify(&entries, &entropy).is_err());
    for i in 0..32usize {
        let BatchEntry(pk, msg, signature) = entries[i].clone();
        if i != bad_index {
            assert!(zcash_verify(pk, signature, &msg).is_ok());
            assert!(ietf_cofactored_verify(pk, signature, &msg).is_ok());
            assert!(ietf_cofactorless_verify(pk, signature, &msg).is_ok());
            assert!(alg2_verify(pk, signature, &msg).is_ok());
        } else {
            assert!(zcash_verify(pk, signature, &msg).is_err());
            assert!(ietf_cofactored_verify(pk, signature, &msg).is_err());
            assert!(ietf_cofactorless_verify(pk, signature, &msg).is_err());
            assert!(alg2_verify(pk, signature, &msg).is_err());
        }
    }
}

// Testing test vectors from https://eprint.iacr.org/2020/1244.pdf
// https://github.com/novifinancial/ed25519-speccheck
#[test]
fn test_vectors_zcash() {
    let v: Vec<CasesTestVector> = CasesTestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3, 4, 5, 9, 10, 11];
    println!("Zcash spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = zcash_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_ieft_cofactored() {
    let v: Vec<CasesTestVector> = CasesTestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3, 4, 5];
    println!("ietf cofactored spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = ietf_cofactored_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_ieft_cofactorless() {
    let v: Vec<CasesTestVector> = CasesTestVector::from_file("tests/cases.json");
    let expected_success = [0, 1, 2, 3];
    println!("ietf cofactorless spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = ietf_cofactorless_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}

#[test]
fn test_vectors_alg2() {
    let v: Vec<CasesTestVector> = CasesTestVector::from_file("tests/cases.json");
    let expected_success = [2, 3, 4, 5];
    println!("ietf cofactored spec");
    for i in 0..v.len() {
        let msg = ByteSeq::from_hex(&v[i].message);
        let pub_key = CompressedEdPoint::from_hex(&v[i].pub_key);
        let signature = Signature::from_hex(&v[i].signature);
        let result = alg2_verify(pub_key, signature, &msg);
        println!("Test {}: {:?}", i, result);
        if expected_success.contains(&i) {
            assert!(result.is_ok());
        } else {
            assert!(result.is_err());
        }
    }
}
