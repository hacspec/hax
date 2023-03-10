use hacspec_lib::prelude::*;

use hacspec_sha256::{hash, Sha256Digest};

#[test]
fn test_sha256_kat() {
    let msg = ByteSeq::from_hex("686163737065632072756c6573");
    let expected_256 = "b37db5ed72c97da3b2579537afbc3261ed3d5a56f57b3d8e5c1019ae35929964";
    let digest = hash(&msg);
    println!("{:?}", expected_256);
    println!("{:x?}", digest);
    assert_eq!(expected_256, digest.to_hex());

    let msg = ByteSeq::from_hex("6861637370656320697320612070726f706f73616c20666f722061206e65772073706563696669636174696f6e206c616e677561676520666f722063727970746f207072696d69746976657320746861742069732073756363696e63742c2074686174206973206561737920746f207265616420616e6420696d706c656d656e742c20616e642074686174206c656e647320697473656c6620746f20666f726d616c20766572696669636174696f6e2e");
    let expected_256 = "348ef044446d56e05210361af5a258588ad31765f446bf4cb3b67125a187a64a";
    let digest = hash(&msg);
    println!("{:?}", expected_256);
    println!("{:x?}", digest);
    assert_eq!(expected_256, digest.to_hex());
}

#[test]
fn empty_input() {
    const SHA256_EMPTY: Sha256Digest = Sha256Digest(secret_bytes!([
        0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8, 0x99, 0x6f, 0xb9,
        0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c, 0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52,
        0xb8, 0x55
    ]));
    assert_eq!(hash(&ByteSeq::from_hex("")).to_hex(), SHA256_EMPTY.to_hex());
}
