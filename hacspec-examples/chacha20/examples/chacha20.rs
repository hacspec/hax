use std::fs::File;
use std::io::Read;

use hacspec_lib::prelude::*;

use hacspec_chacha20::*;

fn read_file() -> Vec<u8> {
    let mut file = File::open("input.data").unwrap();
    let mut data = Vec::new();
    let _read = file.read_to_end(&mut data);
    data
}

fn enc_dec_test(m: ByteSeq, key: ChaChaKey, iv: ChaChaIV) {
    let c = chacha20(key, iv, 0, &m);
    let m_dec = chacha20(key, iv, 0, &c);
    assert_eq!(
        m.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>(),
        m_dec.iter().map(|x| U8::declassify(*x)).collect::<Vec<_>>()
    );
}

fn main() {
    let data = ByteSeq::from_public_slice(&read_file());
    let key = ChaChaKey::from_public_slice(&[
        0x80, 0x81, 0x82, 0x83, 0x84, 0x85, 0x86, 0x87, 0x88, 0x89, 0x8a, 0x8b, 0x8c, 0x8d, 0x8e,
        0x8f, 0x90, 0x91, 0x92, 0x93, 0x94, 0x95, 0x96, 0x97, 0x98, 0x99, 0x9a, 0x9b, 0x9c, 0x9d,
        0x9e, 0x9f,
    ]);
    let nonce = ChaChaIV::from_public_slice(&[
        0xf0, 0xf1, 0xf2, 0xf3, 0xf4, 0xf5, 0xf6, 0xf7, 0xf8, 0xf9, 0xfa, 0xfb,
    ]);
    enc_dec_test(data, key, nonce);
}
