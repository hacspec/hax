use hacspec_bls12_381::*;
use hacspec_bls12_381_hash::*;
use hacspec_lib::*;

#[test]
fn test_g1_hash_to_curve_svdw() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SVDW_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_hash_to_curve_svdw(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_hash_to_curve_svdw(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_hash_to_curve_svdw(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g1_encode_to_curve_svdw() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SVDW_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_encode_to_curve_svdw(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_encode_to_curve_svdw(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_encode_to_curve_svdw(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_hash_to_curve_svdw() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SVDW_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_hash_to_curve_svdw(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_hash_to_curve_svdw(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_hash_to_curve_svdw(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_encode_to_curve_svdw() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SVDW_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_encode_to_curve_svdw(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_encode_to_curve_svdw(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_encode_to_curve_svdw(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g1_hash_to_curve_sswu() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SSWU_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_hash_to_curve_sswu(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_hash_to_curve_sswu(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_hash_to_curve_sswu(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g1_encode_to_curve_sswu() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G1_XMD:SHA-256_SSWU_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g1_encode_to_curve_sswu(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g1mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g1_encode_to_curve_sswu(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g1_encode_to_curve_sswu(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_hash_to_curve_sswu() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SSWU_RO_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_hash_to_curve_sswu(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_hash_to_curve_sswu(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_hash_to_curve_sswu(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
fn test_g2_encode_to_curve_sswu() {
    let dst = ByteSeq::from_public_slice(b"hacspec_v0.1.0_BLS12381G2_XMD:SHA-256_SSWU_NU_");
    let msg1 = ByteSeq::from_public_slice(b"hello world");
    let p1 = g2_encode_to_curve_sswu(&msg1, &dst);
    let r = Scalar::from_hex("73eda753299d7d483339d80809a1d80553bda402fffe5bfeffffffff00000001"); // Order of the group
    let h = g2mul(r, p1);
    assert!(h.2); // in the correct sub-group
    let msg2 = ByteSeq::from_public_slice(b"hello world");
    let p2 = g2_encode_to_curve_sswu(&msg2, &dst);
    assert_eq!(p1, p2); // deterministic
    let msg3 = ByteSeq::from_public_slice(b"hello world2");
    let p3 = g2_encode_to_curve_sswu(&msg3, &dst);
    assert!(p1 != p3); // not trivial
}

#[test]
// Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.9.1
fn test_g1_hash_test_vectors() {
    let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_RO_");
    let msg = ByteSeq::from_public_slice(b"");
    let p = g1_hash_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("052926add2207b76ca4fa57a8734416c8dc95e24501772c814278700eed6d1e4e8cf62d9c09db0fac349612b759e79a1"), 
        Fp::from_hex("08ba738453bfed09cb546dbb0783dbb3a5f1f566ed67bb6be0e8c67e2e81a4cc68ee29813bb7994998f3eae0c9c6a265"), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
    let p = g1_hash_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("11e0b079dea29a68f0383ee94fed1b940995272407e3bb916bbf268c263ddd57a6a27200a784cbc248e84f357ce82d98"), 
        Fp::from_hex("03a87ae2caf14e8ee52e51fa2ed8eefe80f02457004ba4d486d6aa1f517c0889501dc7413753f9599b099ebcbbd2d709"), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(
        b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
        qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
    );
    let p = g1_hash_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("15f68eaa693b95ccb85215dc65fa81038d69629f70aeee0d0f677cf22285e7bf58d7cb86eefe8f2e9bc3f8cb84fac488"), 
        Fp::from_hex("1807a1d50c29f430b8cafc4f8638dfeeadf51211e1602a5f184443076715f91bb90a48ba1e370edce6ae1062f5e6dd38"), false);
    assert_eq!(p, result);
}

#[test]
// Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.9.2
fn test_g1_encode_test_vectors() {
    let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G1_XMD:SHA-256_SSWU_NU_");
    let msg = ByteSeq::from_public_slice(b"");
    let p = g1_encode_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("184bb665c37ff561a89ec2122dd343f20e0f4cbcaec84e3c3052ea81d1834e192c426074b02ed3dca4e7676ce4ce48ba"), 
        Fp::from_hex("04407b8d35af4dacc809927071fc0405218f1401a6d15af775810e4e460064bcc9468beeba82fdc751be70476c888bf3"), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
    let p = g1_encode_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("1974dbb8e6b5d20b84df7e625e2fbfecb2cdb5f77d5eae5fb2955e5ce7313cae8364bc2fff520a6c25619739c6bdcb6a"), 
        Fp::from_hex("15f9897e11c6441eaa676de141c8d83c37aab8667173cbe1dfd6de74d11861b961dccebcd9d289ac633455dfcc7013a3"), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(
        b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
        qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
    );
    let p = g1_encode_to_curve_sswu(&msg, &dst);
    let result = (Fp::from_hex("0a7a047c4a8397b3446450642c2ac64d7239b61872c9ae7a59707a8f4f950f101e766afe58223b3bff3a19a7f754027c"), 
        Fp::from_hex("1383aebba1e4327ccff7cf9912bda0dbc77de048b71ef8c8a81111d71dc33c5e3aa6edee9cf6f5fe525d50cc50b77cc9"), false);
    assert_eq!(p, result);
}

#[test]
// Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.10.1
fn test_g2_hash_test_vectors() {
    let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_RO_");
    let msg = ByteSeq::from_public_slice(b"");
    let p = g2_hash_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("0141ebfbdca40eb85b87142e130ab689c673cf60f1a3e98d69335266f30d9b8d4ac44c1038e9dcdd5393faf5c41fb78a"), 
    Fp::from_hex("05cb8437535e20ecffaef7752baddf98034139c38452458baeefab379ba13dff5bf5dd71b72418717047f5b0f37da03d")),
    (Fp::from_hex("0503921d7f6a12805e72940b963c0cf3471c7b2a524950ca195d11062ee75ec076daf2d4bc358c4b190c0c98064fdd92"), 
        Fp::from_hex("12424ac32561493f3fe3c260708a12b7c620e7be00099a974e259ddc7d1f6395c3c811cdd19f1e8dbf3e9ecfdcbab8d6")), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
    let p = g2_hash_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("121982811d2491fde9ba7ed31ef9ca474f0e1501297f68c298e9f4c0028add35aea8bb83d53c08cfc007c1e005723cd0"), 
    Fp::from_hex("190d119345b94fbd15497bcba94ecf7db2cbfd1e1fe7da034d26cbba169fb3968288b3fafb265f9ebd380512a71c3f2c")),
    (Fp::from_hex("05571a0f8d3c08d094576981f4a3b8eda0a8e771fcdcc8ecceaf1356a6acf17574518acb506e435b639353c2e14827c8"), 
        Fp::from_hex("0bb5e7572275c567462d91807de765611490205a941a5a6af3b1691bfe596c31225d3aabdf15faff860cb4ef17c7c3be")), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(
        b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
        qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
    );
    let p = g2_hash_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("19a84dd7248a1066f737cc34502ee5555bd3c19f2ecdb3c7d9e24dc65d4e25e50d83f0f77105e955d78f4762d33c17da"), 
    Fp::from_hex("0934aba516a52d8ae479939a91998299c76d39cc0c035cd18813bec433f587e2d7a4fef038260eef0cef4d02aae3eb91")),
    (Fp::from_hex("14f81cd421617428bc3b9fe25afbb751d934a00493524bc4e065635b0555084dd54679df1536101b2c979c0152d09192"), 
        Fp::from_hex("09bcccfa036b4847c9950780733633f13619994394c23ff0b32fa6b795844f4a0673e20282d07bc69641cee04f5e5662")), false);
    assert_eq!(p, result);
}

#[test]
// Test vectors from https://www.ietf.org/archive/id/draft-irtf-cfrg-hash-to-curve-13.html#appendix-J.10.2
fn test_g2_encode_test_vectors() {
    let dst = ByteSeq::from_public_slice(b"QUUX-V01-CS02-with-BLS12381G2_XMD:SHA-256_SSWU_NU_");
    let msg = ByteSeq::from_public_slice(b"");
    let p = g2_encode_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("00e7f4568a82b4b7dc1f14c6aaa055edf51502319c723c4dc2688c7fe5944c213f510328082396515734b6612c4e7bb7"), 
    Fp::from_hex("126b855e9e69b1f691f816e48ac6977664d24d99f8724868a184186469ddfd4617367e94527d4b74fc86413483afb35b")),
    (Fp::from_hex("0caead0fd7b6176c01436833c79d305c78be307da5f6af6c133c47311def6ff1e0babf57a0fb5539fce7ee12407b0a42"), 
        Fp::from_hex("1498aadcf7ae2b345243e281ae076df6de84455d766ab6fcdaad71fab60abb2e8b980a440043cd305db09d283c895e3d")), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(b"abcdef0123456789");
    let p = g2_encode_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("038af300ef34c7759a6caaa4e69363cafeed218a1f207e93b2c70d91a1263d375d6730bd6b6509dcac3ba5b567e85bf3"), 
    Fp::from_hex("0da75be60fb6aa0e9e3143e40c42796edf15685cafe0279afd2a67c3dff1c82341f17effd402e4f1af240ea90f4b659b")),
    (Fp::from_hex("19b148cbdf163cf0894f29660d2e7bfb2b68e37d54cc83fd4e6e62c020eaa48709302ef8e746736c0e19342cc1ce3df4"), 
        Fp::from_hex("0492f4fed741b073e5a82580f7c663f9b79e036b70ab3e51162359cec4e77c78086fe879b65ca7a47d34374c8315ac5e")), false);
    assert_eq!(p, result);

    let msg = ByteSeq::from_public_slice(
        b"q128_qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq\
        qqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqqq",
    );
    let p = g2_encode_to_curve_sswu(&msg, &dst);
    let result = ((Fp::from_hex("0c5ae723be00e6c3f0efe184fdc0702b64588fe77dda152ab13099a3bacd3876767fa7bbad6d6fd90b3642e902b208f9"), 
    Fp::from_hex("12c8c05c1d5fc7bfa847f4d7d81e294e66b9a78bc9953990c358945e1f042eedafce608b67fdd3ab0cb2e6e263b9b1ad")),
    (Fp::from_hex("04e77ddb3ede41b5ec4396b7421dd916efc68a358a0d7425bddd253547f2fb4830522358491827265dfc5bcc1928a569"), 
        Fp::from_hex("11c624c56dbe154d759d021eec60fab3d8b852395a89de497e48504366feedd4662d023af447d66926a28076813dd646")), false);
    assert_eq!(p, result);
}
