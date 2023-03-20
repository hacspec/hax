use hacspec_hmac::*;
use hacspec_lib::prelude::*;

struct HMACTestVectors<'a> {
    key: &'a str,
    txt: &'a str,
    expected: &'a str,
}

// https://tools.ietf.org/html/rfc4231
const HMAC_KAT: [HMACTestVectors; 5] = [
    HMACTestVectors {
        key: "0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b0b",
        txt: "4869205468657265",
        expected: "b0344c61d8db38535ca8afceaf0bf12b881dc200c9833da726e9376c2e32cff7",
    },
    HMACTestVectors {
        key: "4a656665",
        txt: "7768617420646f2079612077616e7420666f72206e6f7468696e673f",
        expected: "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843",
    },
    HMACTestVectors {
        key: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        txt: "dddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddddd",
        expected: "773ea91e36800e46854db8ebd09181a72959098b3ef8c122d9635514ced565fe",
    },
    HMACTestVectors {
        key: "0102030405060708090a0b0c0d0e0f10111213141516171819",
        txt: "cdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcdcd",
        expected: "82558a389a443c0ea4cc819899f2083a85f0faa3e578f8077a2e3ff46729665b",
    },
    HMACTestVectors {
        key: "aaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa",
        txt: "54657374205573696e67204c6172676572205468616e20426c6f636b2d53697a65204b6579202d2048617368204b6579204669727374",
        expected: "60e431591ee0b67f0d8a26aacbf5b77f8e0bc6213728c5140546040f0ee37f54",
    }
];

#[test]
fn test_hmac_kat() {
    for kat in HMAC_KAT.iter() {
        let hmac = hmac(&ByteSeq::from_hex(kat.key), &ByteSeq::from_hex(kat.txt));
        assert_eq!(kat.expected, hmac.to_hex());
    }
}
