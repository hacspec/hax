use hacspec_lib::prelude::*;

use hacspec_curve25519::*;

fn ecdh(s: X25519SerializedScalar, u: X25519SerializedPoint, expected: X25519SerializedPoint) {
    let r = x25519_scalarmult(s, u);
    assert_bytes_eq!(expected, r);
}

#[test]
fn test_kat1() {
    let s = X25519SerializedScalar::from_public_slice(&[
        0xa5, 0x46, 0xe3, 0x6b, 0xf0, 0x52, 0x7c, 0x9d, 0x3b, 0x16, 0x15, 0x4b, 0x82, 0x46, 0x5e,
        0xdd, 0x62, 0x14, 0x4c, 0x0a, 0xc1, 0xfc, 0x5a, 0x18, 0x50, 0x6a, 0x22, 0x44, 0xba, 0x44,
        0x9a, 0xc4,
    ]);
    let u = X25519SerializedPoint::from_public_slice(&[
        0xe6, 0xdb, 0x68, 0x67, 0x58, 0x30, 0x30, 0xdb, 0x35, 0x94, 0xc1, 0xa4, 0x24, 0xb1, 0x5f,
        0x7c, 0x72, 0x66, 0x24, 0xec, 0x26, 0xb3, 0x35, 0x3b, 0x10, 0xa9, 0x03, 0xa6, 0xd0, 0xab,
        0x1c, 0x4c,
    ]);
    let expected = X25519SerializedPoint::from_public_slice(&[
        0xc3, 0xda, 0x55, 0x37, 0x9d, 0xe9, 0xc6, 0x90, 0x8e, 0x94, 0xea, 0x4d, 0xf2, 0x8d, 0x08,
        0x4f, 0x32, 0xec, 0xcf, 0x03, 0x49, 0x1c, 0x71, 0xf7, 0x54, 0xb4, 0x07, 0x55, 0x77, 0xa2,
        0x85, 0x52,
    ]);

    ecdh(s, u, expected);
}

const KAT: [(&str, &str, &str); 5] = [
    (
        "77076d0a7318a57d3c16c17251b26645df4c2f87ebc0992ab177fba51db92c2a",
        "de9edb7d7b7dc1b4d35b61c2ece435373f8343c85b78674dadfc7e146f882b4f",
        "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742",
    ),
    (
        "5dab087e624a8a4b79e17f8b83800ee66f3bb1292618b6fd1c2f8b27ff88e0eb",
        "8520f0098930a754748b7ddcb43ef75a0dbf3a0d26381af4eba4a98eaa9b4e6a",
        "4a5d9d5ba4ce2de1728e3bf480350f25e07e21c947d19e3376f09b3c1e161742",
    ),
    (
        "0100000000000000000000000000000000000000000000000000000000000000",
        "2500000000000000000000000000000000000000000000000000000000000000",
        "3c7777caf997b264416077665b4e229d0b9548dc0cd81998ddcdc5c8533c797f",
    ),
    (
        "0100000000000000000000000000000000000000000000000000000000000000",
        "ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff",
        "b32d1362c248d62fe62619cff04dd43db73ffc1b6308ede30b78d87380f1e834",
    ),
    (
        "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4",
        "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c",
        "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552",
    ),
];

#[test]
fn test_kat3() {
    for kat in KAT.iter() {
        let s = X25519SerializedScalar::from_hex(kat.0);
        let u = X25519SerializedPoint::from_hex(kat.1);
        let expected = X25519SerializedPoint::from_hex(kat.2);

        ecdh(s, u, expected);
    }
}
