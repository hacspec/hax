use hacspec_lib::{ByteSeq, ModNumeric};
use hacspec_p256::*;

use hacspec_dev::prelude::*;

#[test]
fn test_p256_base() {
    let sk = P256Scalar::from_hex("14");
    let point_expected = (
        P256FieldElement::from_hex(
            "83A01A9378395BAB9BCD6A0AD03CC56D56E6B19250465A94A234DC4C6B28DA9A",
        ),
        P256FieldElement::from_hex(
            "76E49B6DE2F73234AE6A5EB9D612B75C9F2202BB6923F54FF8240AAA86F640B8",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk = P256Scalar::from_hex("018ebbb95eed0e13");
    let point_expected = (
        P256FieldElement::from_hex(
            "339150844EC15234807FE862A86BE77977DBFB3AE3D96F4C22795513AEAAB82F",
        ),
        P256FieldElement::from_hex(
            "B1C14DDFDC8EC1B2583F51E85A5EB3A155840F2034730E9B5ADA38B674336A21",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);

    let sk =
        P256Scalar::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    let point_expected = (
        P256FieldElement::from_hex(
            "6B17D1F2E12C4247F8BCE6E563A440F277037D812DEB33A0F4A13945D898C296",
        ),
        P256FieldElement::from_hex(
            "B01CBD1C01E58065711814B583F061E9D431CCA994CEA1313449BF97C840AE0A",
        ),
    );

    let point_computed = match p256_point_mul_base(sk) {
        Ok(p) => p,
        Err(_) => panic!("Error p256_point_mul_base"),
    };
    assert_eq!(point_computed.0, point_expected.0);
    assert_eq!(point_computed.1, point_expected.1);
}

create_test_vectors!(
    P256TestVector,
    algorithm: String,
    generatorVersion: String,
    numberOfTests: usize,
    header: Vec<Value>,   // not used
    notes: Option<Value>, // text notes (might not be present), keys correspond to flags
    schema: String,       // not used
    testGroups: Vec<TestGroup>
);

create_test_vectors!(
    TestGroup,
    curve: String,
    encoding: String,
    r#type: String,
    tests: Vec<Test>
);

create_test_vectors!(
    Test,
    tcId: usize,
    comment: String,
    public: String,
    private: String,
    shared: String,
    result: String,
    flags: Vec<String>
);

#[allow(non_snake_case)]
#[test]
fn test_wycheproof_plain() {
    let tests: P256TestVector = P256TestVector::from_file("tests/ecdh_secp256r1_ecpoint_test.json");

    let num_tests = tests.numberOfTests;
    let mut skipped_tests = 0;
    let mut tests_run = 0;
    match tests.algorithm.as_ref() {
        "ECDH" => (),
        _ => panic!("This is not an ECDH test vector."),
    };
    for testGroup in tests.testGroups.iter() {
        assert_eq!(testGroup.r#type, "EcdhEcpointTest");
        assert_eq!(testGroup.curve, "secp256r1");
        assert_eq!(testGroup.encoding, "ecpoint");
        for test in testGroup.tests.iter() {
            println!("Test {:?}: {:?}", test.tcId, test.comment);
            if !test.result.eq("valid")
                && !(test.result.eq("invalid") && test.comment.eq("point is not on curve"))
            {
                println!("We're only doing valid tests for now.");
                skipped_tests += 1;
                continue;
            }
            let not_on_curve =
                test.result.eq("invalid") && test.comment.eq("point is not on curve");
            if test.comment == "compressed public key" {
                // not implemented
                println!("Compressed public keys are not supported.");
                skipped_tests += 1;
                continue;
            }
            assert_eq!(&test.public[0..2], "04");
            let k = P256Scalar::from_hex(&test.private);
            let p = (
                P256FieldElement::from_hex(&test.public[2..66]),
                P256FieldElement::from_hex(&test.public[66..]),
            );
            if not_on_curve {
                assert!(!p256_validate_public_key(p));
                tests_run += 1;
                continue;
            }
            assert!(p256_validate_public_key(p));
            let expected = P256FieldElement::from_hex(&test.shared);
            let shared = match p256_point_mul(k, p) {
                Ok(s) => s,
                Err(_) => panic!("Unexpected error in point_mul"),
            };
            assert_eq!(shared.0, expected);

            // Check w
            let my_p = (p.0, p256_calculate_w(p.0));
            let shared = match p256_point_mul(k, my_p) {
                Ok(s) => s,
                Err(_) => panic!("Unexpected error in point_mul"),
            };
            assert_eq!(shared.0, expected, "Error in ECDH using calculate w");
            // The Y coordinate of the computed point (my_p) is either
            // equal to y, or -y % p.
            let other_y = my_p.1.neg();
            assert!(
                p.1 == my_p.1 || p.1 == other_y,
                "The computed w is wrong.\nGot {:x}\n or {:x} but expected\n    {}",
                my_p.1,
                other_y,
                &test.public[66..]
            );

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

#[test]
fn invalid_scalars() {
    let zero = ByteSeq::from_hex("00");
    assert!(!p256_validate_private_key(&zero));

    let too_large =
        ByteSeq::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551");
    assert!(!p256_validate_private_key(&too_large));

    let largest_valid =
        ByteSeq::from_hex("ffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632550");
    assert!(p256_validate_private_key(&largest_valid));
}

#[test]
fn point_validation() {
    let not_on_curve = (
        P256FieldElement::from_hex(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        ),
        P256FieldElement::from_hex(
            "ffffffff00000001000000000000000000000000ffffffffffffffffffffffff",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));

    let valid_point = (
        P256FieldElement::from_hex(
            "31028f3377fc8f2b1967edaab90213acad0da9f50897f08f57537f78f1167447",
        ),
        P256FieldElement::from_hex(
            "43a1930189363bbde2ac4cbd1649cdc6f451add71dd2f16a8a867f2b17caa16b",
        ),
    );
    assert!(p256_validate_public_key(valid_point));

    let not_on_curve = (
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));

    let not_on_curve = (
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000000",
        ),
        P256FieldElement::from_hex(
            "0000000000000000000000000000000000000000000000000000000000000001",
        ),
    );
    assert!(!p256_validate_public_key(not_on_curve));
}

#[test]
fn test_p256_calculate_w() {
    fn test_ecdh(x: &str, gy_x: &str, gy_y: &str, gxy_x: &str) {
        let private = P256Scalar::from_hex(x);
        let public_x = P256FieldElement::from_hex(gy_x);
        let expected_secret_x = P256FieldElement::from_hex(gxy_x);

        let public = (public_x, p256_calculate_w(public_x));

        // Check the Y coordinate.
        let other_y = public.1.neg();
        assert!(gy_y == format!("{:x}", public.1) || gy_y == format!("{:x}", other_y));

        // calculate the ECDH secret
        let my_secret_x = match p256_point_mul(private, public) {
            Ok(p) => p.0,
            Err(_) => panic!("Error test_ecdh"),
        };

        assert_eq!(expected_secret_x, my_secret_x);
    }

    // taken from ecdh_secp256r1_ecpoint_test.json tcId=2
    // negative y
    test_ecdh(
        "0612465c89a023ab17855b0a6bcebfd3febb53aef84138647b5352e02c10c346",
        "62d5bd3372af75fe85a040715d0f502428e07046868b0bfdfa61d731afe44f26",
        "ac333a93a9e70a81cd5a95b5bf8d13990eb741c8c38872b4a07d275a014e30cf",
        "53020d908b0219328b658b525f26780e3ae12bcd952bb25a93bc0895e1714285",
    );

    // taken from ecdh_secp256r1_ecpoint_test.json tcId=4
    test_ecdh(
        "0a0d622a47e48f6bc1038ace438c6f528aa00ad2bd1da5f13ee46bf5f633d71a",
        "00c7defeb1a16236738e9a1123ba621bc8e9a3f2485b3f8ffde7f9ce98f5a8a1",
        "cb338c3912b1792f60c2b06ec5231e2d84b0e596e9b76d419ce105ece3791dbc",
        "0000000000000000ffffffffffffffff00000000000000010000000000000001",
    );

    // taken from ecdh_secp256r1_ecpoint_test.json tcId=7
    test_ecdh(
        "0a0d622a47e48f6bc1038ace438c6f528aa00ad2bd1da5f13ee46bf5f633d71a",
        "e9484e58f3331b66ffed6d90cb1c78065fa28cfba5c7dd4352013d3252ee4277",
        "bd7503b045a38b4b247b32c59593580f39e6abfa376c3dca20cf7f9cfb659e13",
        "000003ffffff0000003ffffff0000003ffffff0000003ffffff0000003ffffff",
    );

    // test vector from edhoc
    // positive y
    test_ecdh(
        "368ec1f69aeb659ba37d5a8d45b21bdc0299dceaa8ef235f3ca42ce3530f9525",
        "419701d7f00a26c2dc587a36dd752549f33763c893422c8ea0f955a13a4ff5d5",
        "5e4f0dd8a3da0baa16b9d3ad56a0c1860a940af85914915e25019b402417e99d",
        "2f0cb7e860ba538fbf5c8bded009f6259b4b628fe1eb7dbe9378e5ecf7a824ba",
    );
}
