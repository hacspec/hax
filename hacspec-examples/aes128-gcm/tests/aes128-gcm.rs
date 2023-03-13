use hacspec_dev::prelude::*;
use hacspec_lib::prelude::*;

use hacspec_aes::*;
use hacspec_aes128_gcm::*;
use hacspec_gf128::*;

struct AeadTestVector<'a> {
    key: &'a str,
    nonce: &'a str,
    msg: &'a str,
    aad: &'a str,
    exp_cipher: &'a str,
    exp_mac: &'a str,
}

const KAT: [AeadTestVector; 4] = [
    AeadTestVector {
        key: "00000000000000000000000000000000",
        nonce: "000000000000000000000000",
        msg: "",
        aad: "",
        exp_cipher: "",
        exp_mac: "58e2fccefa7e3061367f1d57a4e7455a"
    },
    AeadTestVector {
        key	: "00000000000000000000000000000000",
        nonce	: "000000000000000000000000",
        aad	: "",
        msg	: "00000000000000000000000000000000",
        exp_cipher : "0388dace60b6a392f328c2b971b2fe78",
        exp_mac	: "ab6e47d42cec13bdf53a67b21257bddf",
    },
    AeadTestVector {
        key	: "feffe9928665731c6d6a8f9467308308",
        nonce	: "cafebabefacedbaddecaf888",
        msg	: "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b391aafd255",
        aad	: "",
        exp_cipher : "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091473f5985",
        exp_mac	: "4d5c2af327cd64a62cf35abd2ba6fab4",
    },
    AeadTestVector {
        key	: "feffe9928665731c6d6a8f9467308308",
        nonce	: "cafebabefacedbaddecaf888",
        msg	: "d9313225f88406e5a55909c5aff5269a86a7a9531534f7da2e4c303d8a318a721c3c0c95956809532fcf0e2449a6b525b16aedf5aa0de657ba637b39",
        aad	: "feedfacedeadbeeffeedfacedeadbeefabaddad2",
        exp_cipher: "42831ec2217774244b7221b784d0d49ce3aa212f2c02a4e035c17e2329aca12e21d514b25466931c7d8f6a5aac84aa051ba30b396a0aac973d58e091",
        exp_mac	: "5bc94fbc3221a5db94fae95ae7121a47",
    }
];

macro_rules! to_public_vec {
    ($x:expr) => {
        $x.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    };
}

#[test]
fn kat_test() {
    for kat in KAT.iter() {
        let k = Key128::from_hex(kat.key);
        let nonce = AesNonce::from_hex(kat.nonce);
        let exp_mac = Gf128Tag::from_hex(kat.exp_mac);
        let msg = ByteSeq::from_hex(kat.msg);
        let aad = ByteSeq::from_hex(kat.aad);
        let exp_cipher = ByteSeq::from_hex(kat.exp_cipher);

        let (cipher, mac) = encrypt_aes128(k, nonce, &aad, &msg);
        assert_eq!(
            exp_cipher
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>(),
            cipher
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            exp_mac
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>(),
            mac.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
        );

        let decrypted_msg = decrypt_aes128(k, nonce, &aad, &cipher, mac).unwrap();
        assert_eq!(
            msg.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
            decrypted_msg
                .iter()
                .map(|x| U8::declassify(*x))
                .collect::<Vec<_>>()
        );
    }
}

create_test_vectors!(
    AesGcmTestVector,
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    header: Vec<Value>,   // not used
    testGroups: Vec<TestGroup>
);

create_test_vectors!(
    TestGroup,
    ivSize: usize,
    keySize: usize,
    tagSize: usize,
    r#type: String,
    tests: Vec<Test>
);

create_test_vectors!(
    Test,
    tcId: usize,
    comment: String,
    key: String,
    iv: String,
    aad: String,
    msg: String,
    ct: String,
    tag: String,
    result: String,
    flags: Vec<String>
);

#[allow(non_snake_case)]
#[test]
fn test_wycheproof() {
    let tests: AesGcmTestVector = AesGcmTestVector::from_file("tests/aes_gcm_test_wycheproof.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "AES-GCM" => (),
        _ => panic!("This is not an AES-GCM test vector."),
    };
    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "AeadTest");
        if testGroup.keySize != 128 {
            // not implemented
            println!("Only AES 128 is implemented.");
            skipped_tests += testGroup.tests.len();
            continue;
        };
        if testGroup.ivSize != 96 {
            // not implemented
            println!("Nonce sizes != 96 are not supported for AES GCM.");
            skipped_tests += testGroup.tests.len();
            continue;
        }
        for test in testGroup.tests.iter() {
            let valid = test.result.eq("valid");
            if test.comment == "invalid nonce size" {
                // not implemented
                println!("Invalid nonce sizes are not supported.");
                skipped_tests += 1;
                break;
            }
            println!("Test {:?}: {:?}", test.tcId, test.comment);
            let nonce = AesNonce::from_hex(&test.iv);
            let msg = ByteSeq::from_hex(&test.msg);
            let aad = ByteSeq::from_hex(&test.aad);
            let exp_cipher = ByteSeq::from_hex(&test.ct);
            let exp_tag = Gf128Tag::from_hex(&test.tag);
            let k = Key128::from_hex(&test.key);
            let (cipher, tag) = encrypt_aes128(k, nonce, &aad, &msg);
            if valid {
                assert_eq!(to_public_vec!(tag), to_public_vec!(exp_tag));
            } else {
                assert_ne!(to_public_vec!(tag), to_public_vec!(exp_tag));
            }
            assert_eq!(to_public_vec!(cipher), to_public_vec!(exp_cipher));
            tests_run += 1;
        }
    }
    // Check that we ran all tests.
    println!(
        "Ran {} out of {} tests and skipped {}.",
        tests_run, num_tests, skipped_tests
    );
    assert_eq!(num_tests - skipped_tests, tests_run);
}
