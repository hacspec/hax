// Import hacspec and all needed definitions.
use hacspec_lib::*;

// Import chacha20 and poly1305
use hacspec_chacha20::*;
use hacspec_poly1305::*;

#[derive(Debug)]
pub enum Error {
    InvalidTag,
}

pub type ChaChaPolyKey = ChaChaKey;
pub type ChaChaPolyIV = ChaChaIV;
pub type ByteSeqResult = Result<ByteSeq, Error>;

pub fn init(key: ChaChaPolyKey, iv: ChaChaPolyIV) -> PolyState {
    let key_block0 = chacha20_key_block0(key, iv);
    let poly_key = PolyKey::from_slice(&key_block0, 0, 32);
    poly1305_init(poly_key)
}

pub fn poly1305_update_padded(m: &ByteSeq, st: PolyState) -> PolyState {
    let st = poly1305_update_blocks(m, st);
    let last = m.get_remainder_chunk(16);
    poly1305_update_last(16, &last, st)
}

pub fn finish(aad_len: usize, cipher_len: usize, st: PolyState) -> Poly1305Tag {
    let mut last_block = PolyBlock::new();
    last_block = last_block.update(0, &U64_to_le_bytes(U64(aad_len as u64)));
    last_block = last_block.update(8, &U64_to_le_bytes(U64(cipher_len as u64)));
    let st = poly1305_update_block(&last_block, st);
    poly1305_finish(st)
}

pub fn chacha20_poly1305_encrypt(
    key: ChaChaPolyKey,
    iv: ChaChaPolyIV,
    aad: &ByteSeq,
    msg: &ByteSeq,
) -> (ByteSeq, Poly1305Tag) {
    let cipher_text = chacha20(key, iv, 1u32, msg);
    let mut poly_st = init(key, iv);
    poly_st = poly1305_update_padded(aad, poly_st);
    poly_st = poly1305_update_padded(&cipher_text, poly_st);
    let tag = finish(aad.len(), cipher_text.len(), poly_st);
    (cipher_text, tag)
}

pub fn chacha20_poly1305_decrypt(
    key: ChaChaPolyKey,
    iv: ChaChaPolyIV,
    aad: &ByteSeq,
    cipher_text: &ByteSeq,
    tag: Poly1305Tag,
) -> ByteSeqResult {
    let mut poly_st = init(key, iv);
    poly_st = poly1305_update_padded(aad, poly_st);
    poly_st = poly1305_update_padded(cipher_text, poly_st);
    let my_tag = finish(aad.len(), cipher_text.len(), poly_st);
    if my_tag.declassify_eq(&tag) {
        ByteSeqResult::Ok(chacha20(key, iv, 1u32, cipher_text))
    } else {
        ByteSeqResult::Err(Error::InvalidTag)
    }
}
