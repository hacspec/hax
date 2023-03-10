use hacspec_dev::prelude::*;
use hacspec_bip_340::*;
use hacspec_lib::*;
use quickcheck::QuickCheck;

/* The cases.json was produced from the test vectors with the following command:

     curl -s https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv \
       | python -c 'import csv, json, sys; print(json.dumps([dict(r) for r in csv.DictReader(sys.stdin)]))' \
       | jq \
       | sed -e 's/secret key/secret_key/' -e 's/public key/public_key/' -e 's/verification result/verification_result/'

   The SHA256 digest of the test vectors produced with

     curl -s https://raw.githubusercontent.com/bitcoin/bips/master/bip-0340/test-vectors.csv \
     | sha256sum

   was a17adbd2c19032ddc12e63b5f35d5224a9295e9f82397d2632a301696b3cac9f.
*/
create_test_vectors!(
    CasesTestVector,
    index: String,
    secret_key: String,
    public_key: String,
    aux_rand: String,
    message: String,
    signature: String,
    verification_result: String
);

#[test]
fn test_invalid_secret() {
    let sk = SecretKey::from_hex("0000000000000000000000000000000000000000000000000000000000000000");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364140");
    assert!(pubkey_gen(sk).is_ok());
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
    let sk = SecretKey::from_hex("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF");
    assert_eq!(pubkey_gen(sk).unwrap_err(), Error::InvalidSecretKey);
}

#[test]
fn test_vectors() {
    let v: Vec<CasesTestVector> = CasesTestVector::from_file("tests/cases.json");
    for t in v {
        let pk = PublicKey::from_hex(&t.public_key);
        let sig = Signature::from_hex(&t.signature);
        let msg = Message::from_hex(&t.message);
        if t.secret_key != "" {
            let sk = SecretKey::from_hex(&t.secret_key);
            let pk2 = pubkey_gen(sk).unwrap();
            assert_bytes_eq!(pk, pk2);
            let aux_rand = AuxRand::from_hex(&t.aux_rand);
            let sig2 = sign(msg, sk, aux_rand).unwrap();
            assert_bytes_eq!(sig, sig2);
        }
        let result = t.verification_result == "TRUE";
        assert_eq!(verify(msg, pk, sig).is_ok(), result);
    }
}

#[test]
fn test_sign_verify() {
    fn test_q(msg: (u128, u128), sk: (u128, u128), aux_rand: (u128, u128)) -> bool {
        let (msg1, msg2) = msg;
        let msg = [msg2.to_le_bytes(), msg1.to_le_bytes()].concat();
        let msg = Message::from_public_slice(&msg);
        let (sk1, sk2) = sk;
        let sk = [sk2.to_le_bytes(), sk1.to_le_bytes()].concat();
        let sk = SecretKey::from_public_slice(&sk);
        let pk_res = pubkey_gen(sk);
        if pk_res.is_err() {
            // if there's an error, the secret key is invalid and we don't need
            // to try signing
            return true;
        }
        let (aux_rand1, aux_rand2) = aux_rand;
        let aux_rand = [aux_rand2.to_le_bytes(), aux_rand1.to_le_bytes()].concat();
        let aux_rand = AuxRand::from_public_slice(&aux_rand);
        // sign also verifies the resulting signature
        sign(msg, sk, aux_rand).unwrap();
        true
    }
    QuickCheck::new()
        .tests(12)
        .quickcheck(test_q as fn((u128, u128), (u128, u128), (u128, u128)) -> bool);
}
