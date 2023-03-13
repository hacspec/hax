use hacspec_hkdf::*;
use hacspec_lib::prelude::*;

struct HKDFTestVectors<'a> {
    ikm: &'a str,
    salt: &'a str,
    info: &'a str,
    l: usize,
    prk: &'a str,
    okm: &'a str,
}

// https://tools.ietf.org/html/rfc5869
const HKDF_KAT: [HKDFTestVectors; 3] = [
    HKDFTestVectors {
        ikm: "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
        salt: "000102030405060708090a0b0c",
        info: "f0f1f2f3f4f5f6f7f8f9",
        l: 42,
        prk: "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5",
        okm: "3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf34007208d5b887185865"
    },
    HKDFTestVectors {
        ikm: "000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f202122232425262728292a2b2c2d2e2f303132333435363738393a3b3c3d3e3f404142434445464748494a4b4c4d4e4f",
        salt: "606162636465666768696a6b6c6d6e6f707172737475767778797a7b7c7d7e7f808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9fa0a1a2a3a4a5a6a7a8a9aaabacadaeaf",
        info: "b0b1b2b3b4b5b6b7b8b9babbbcbdbebfc0c1c2c3c4c5c6c7c8c9cacbcccdcecfd0d1d2d3d4d5d6d7d8d9dadbdcdddedfe0e1e2e3e4e5e6e7e8e9eaebecedeeeff0f1f2f3f4f5f6f7f8f9fafbfcfdfeff",
        l: 82,
        prk: "06a6b88c5853361a06104c9ceb35b45cef760014904671014a193f40c15fc244",
        okm: "b11e398dc80327a1c8e7f78c596a49344f012eda2d4efad8a050cc4c19afa97c59045a99cac7827271cb41c65e590e09da3275600c2f09b8367793a9aca3db71cc30c58179ec3e87c14c01d5c1f3434f1d87"
    },
    HKDFTestVectors {
        ikm: "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
        salt: "",
        info: "",
        l: 42,
        prk: "19ef24a32c717b167f33a91d6f648bdf96596776afdb6377ac434c1c293ccb04",
        okm: "8da4e775a563c18f715f802a063c5a31b8a11f5c5ee1879ec3454e5f3c738d2d9d201395faa4b61a96c8"
    }
];

#[test]
fn test_kat() {
    for kat in HKDF_KAT.iter() {
        let prk = extract(&ByteSeq::from_hex(kat.salt), &ByteSeq::from_hex(kat.ikm));
        assert_eq!(kat.prk, prk.to_hex());

        let okm = match expand(
            &ByteSeq::from_seq(&prk),
            &ByteSeq::from_hex(kat.info),
            kat.l,
        ) {
            Ok(okm) => okm,
            Err(_) => panic!("Invalid HKDF output length"),
        };
        assert_eq!(kat.okm, okm.to_hex());
    }
}

#[test]
fn test_invalid_output_len() {
    expand(
        &ByteSeq::from_hex("deadbeef"),
        &ByteSeq::from_hex("deadbeef"),
        10000,
    )
    .expect_err("The output should have been too long");
}
