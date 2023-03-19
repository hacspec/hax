use hacspec_lib::*;
use hacspec_sha512::*;

#[test]
fn test_sha512() {
    let msg = ByteSeq::from_public_slice(b"hello world");
    let expected = "309ecc489c12d6eb4cc40f50c902f2b4d0ed77ee511a7c7a9bcd3ca86d4cd86f\
        989dd35bc5ff499670da34255b45b0cfd830e81f605dcf7dc5542e93ae9cd76f";
    let result = sha512(&msg);
    assert_eq!(expected, result.to_hex());
}

#[test]
fn test_empty() {
    let msg = ByteSeq::from_public_slice(b"");
    let expected = "cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce\
        47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e";
    let result = sha512(&msg);
    assert_eq!(expected, result.to_hex());
}
