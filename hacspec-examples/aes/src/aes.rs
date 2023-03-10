use hacspec_lib::*;

const BLOCKSIZE: usize = 16;
const IVSIZE: usize = 12;

pub const KEY_LENGTH: usize = 4;
pub const ROUNDS: usize = 10;
pub const KEY_SCHEDULE_LENGTH: usize = 176;
pub const ITERATIONS: usize = 40;

pub const INVALID_KEY_EXPANSION_INDEX: u8 = 1u8;

bytes!(Block, BLOCKSIZE);
bytes!(Word, KEY_LENGTH);
bytes!(RoundKey, BLOCKSIZE);
bytes!(AesNonce, IVSIZE);
bytes!(SBox, 256);
bytes!(RCon, 15);
bytes!(Bytes144, 144);
bytes!(Bytes176, KEY_SCHEDULE_LENGTH);
bytes!(Key128, BLOCKSIZE);

type ByteSeqResult = Result<ByteSeq, u8>;
type BlockResult = Result<Block, u8>;
type WordResult = Result<Word, u8>;

const SBOX: SBox = SBox(secret_bytes!([
    0x63u8, 0x7Cu8, 0x77u8, 0x7Bu8, 0xF2u8, 0x6Bu8, 0x6Fu8, 0xC5u8, 0x30u8, 0x01u8, 0x67u8, 0x2Bu8,
    0xFEu8, 0xD7u8, 0xABu8, 0x76u8, 0xCAu8, 0x82u8, 0xC9u8, 0x7Du8, 0xFAu8, 0x59u8, 0x47u8, 0xF0u8,
    0xADu8, 0xD4u8, 0xA2u8, 0xAFu8, 0x9Cu8, 0xA4u8, 0x72u8, 0xC0u8, 0xB7u8, 0xFDu8, 0x93u8, 0x26u8,
    0x36u8, 0x3Fu8, 0xF7u8, 0xCCu8, 0x34u8, 0xA5u8, 0xE5u8, 0xF1u8, 0x71u8, 0xD8u8, 0x31u8, 0x15u8,
    0x04u8, 0xC7u8, 0x23u8, 0xC3u8, 0x18u8, 0x96u8, 0x05u8, 0x9Au8, 0x07u8, 0x12u8, 0x80u8, 0xE2u8,
    0xEBu8, 0x27u8, 0xB2u8, 0x75u8, 0x09u8, 0x83u8, 0x2Cu8, 0x1Au8, 0x1Bu8, 0x6Eu8, 0x5Au8, 0xA0u8,
    0x52u8, 0x3Bu8, 0xD6u8, 0xB3u8, 0x29u8, 0xE3u8, 0x2Fu8, 0x84u8, 0x53u8, 0xD1u8, 0x00u8, 0xEDu8,
    0x20u8, 0xFCu8, 0xB1u8, 0x5Bu8, 0x6Au8, 0xCBu8, 0xBEu8, 0x39u8, 0x4Au8, 0x4Cu8, 0x58u8, 0xCFu8,
    0xD0u8, 0xEFu8, 0xAAu8, 0xFBu8, 0x43u8, 0x4Du8, 0x33u8, 0x85u8, 0x45u8, 0xF9u8, 0x02u8, 0x7Fu8,
    0x50u8, 0x3Cu8, 0x9Fu8, 0xA8u8, 0x51u8, 0xA3u8, 0x40u8, 0x8Fu8, 0x92u8, 0x9Du8, 0x38u8, 0xF5u8,
    0xBCu8, 0xB6u8, 0xDAu8, 0x21u8, 0x10u8, 0xFFu8, 0xF3u8, 0xD2u8, 0xCDu8, 0x0Cu8, 0x13u8, 0xECu8,
    0x5Fu8, 0x97u8, 0x44u8, 0x17u8, 0xC4u8, 0xA7u8, 0x7Eu8, 0x3Du8, 0x64u8, 0x5Du8, 0x19u8, 0x73u8,
    0x60u8, 0x81u8, 0x4Fu8, 0xDCu8, 0x22u8, 0x2Au8, 0x90u8, 0x88u8, 0x46u8, 0xEEu8, 0xB8u8, 0x14u8,
    0xDEu8, 0x5Eu8, 0x0Bu8, 0xDBu8, 0xE0u8, 0x32u8, 0x3Au8, 0x0Au8, 0x49u8, 0x06u8, 0x24u8, 0x5Cu8,
    0xC2u8, 0xD3u8, 0xACu8, 0x62u8, 0x91u8, 0x95u8, 0xE4u8, 0x79u8, 0xE7u8, 0xC8u8, 0x37u8, 0x6Du8,
    0x8Du8, 0xD5u8, 0x4Eu8, 0xA9u8, 0x6Cu8, 0x56u8, 0xF4u8, 0xEAu8, 0x65u8, 0x7Au8, 0xAEu8, 0x08u8,
    0xBAu8, 0x78u8, 0x25u8, 0x2Eu8, 0x1Cu8, 0xA6u8, 0xB4u8, 0xC6u8, 0xE8u8, 0xDDu8, 0x74u8, 0x1Fu8,
    0x4Bu8, 0xBDu8, 0x8Bu8, 0x8Au8, 0x70u8, 0x3Eu8, 0xB5u8, 0x66u8, 0x48u8, 0x03u8, 0xF6u8, 0x0Eu8,
    0x61u8, 0x35u8, 0x57u8, 0xB9u8, 0x86u8, 0xC1u8, 0x1Du8, 0x9Eu8, 0xE1u8, 0xF8u8, 0x98u8, 0x11u8,
    0x69u8, 0xD9u8, 0x8Eu8, 0x94u8, 0x9Bu8, 0x1Eu8, 0x87u8, 0xE9u8, 0xCEu8, 0x55u8, 0x28u8, 0xDFu8,
    0x8Cu8, 0xA1u8, 0x89u8, 0x0Du8, 0xBFu8, 0xE6u8, 0x42u8, 0x68u8, 0x41u8, 0x99u8, 0x2Du8, 0x0Fu8,
    0xB0u8, 0x54u8, 0xBBu8, 0x16u8
]));

const RCON: RCon = RCon(secret_bytes!([
    0x8du8, 0x01u8, 0x02u8, 0x04u8, 0x08u8, 0x10u8, 0x20u8, 0x40u8, 0x80u8, 0x1bu8, 0x36u8, 0x6cu8,
    0xd8u8, 0xabu8, 0x4du8
]));

fn sub_bytes(state: Block) -> Block {
    let mut st = state;
    for i in 0..BLOCKSIZE {
        st[i] = SBOX[U8::declassify(state[i])];
    }
    st
}

fn shift_row(i: usize, shift: usize, state: Block) -> Block {
    let mut out = state;
    out[i] = state[i + (4 * (shift % 4))];
    out[i + 4] = state[i + (4 * ((shift + 1) % 4))];
    out[i + 8] = state[i + (4 * ((shift + 2) % 4))];
    out[i + 12] = state[i + (4 * ((shift + 3) % 4))];
    out
}

fn shift_rows(state: Block) -> Block {
    let state = shift_row(1, 1, state);
    let state = shift_row(2, 2, state);
    shift_row(3, 3, state)
}

fn xtime(x: U8) -> U8 {
    let x1 = x << 1;
    let x7 = x >> 7;
    let x71 = x7 & U8(0x01u8);
    let x711b = x71 * U8(0x1bu8);
    x1 ^ x711b
}

fn mix_column(c: usize, state: Block) -> Block {
    let i0 = 4 * c;
    let s0 = state[i0];
    let s1 = state[i0 + 1];
    let s2 = state[i0 + 2];
    let s3 = state[i0 + 3];
    let mut st = state;
    let tmp = s0 ^ s1 ^ s2 ^ s3;
    st[i0] = s0 ^ tmp ^ (xtime(s0 ^ s1));
    st[i0 + 1] = s1 ^ tmp ^ (xtime(s1 ^ s2));
    st[i0 + 2] = s2 ^ tmp ^ (xtime(s2 ^ s3));
    st[i0 + 3] = s3 ^ tmp ^ (xtime(s3 ^ s0));
    st
}

fn mix_columns(state: Block) -> Block {
    let state = mix_column(0, state);
    let state = mix_column(1, state);
    let state = mix_column(2, state);
    mix_column(3, state)
}

fn add_round_key(state: Block, key: RoundKey) -> Block {
    let mut out = state;
    for i in 0..BLOCKSIZE {
        out[i] = out[i] ^ key[i];
    }
    out
}

fn aes_enc(state: Block, round_key: RoundKey) -> Block {
    let state = sub_bytes(state);
    let state = shift_rows(state);
    let state = mix_columns(state);
    add_round_key(state, round_key)
}

fn aes_enc_last(state: Block, round_key: RoundKey) -> Block {
    let state = sub_bytes(state);
    let state = shift_rows(state);
    add_round_key(state, round_key)
}

fn rounds_aes(state: Block, key: ByteSeq) -> Block {
    let mut out = state;
    for i in 0..key.num_chunks(BLOCKSIZE) {
        let (_, key_block) = key.get_chunk(BLOCKSIZE, i);
        out = aes_enc(out, RoundKey::from_seq(&key_block));
    }
    out
}

fn block_cipher_aes(input: Block, key: ByteSeq, nr: usize) -> Block {
    let k0 = RoundKey::from_slice_range(&key, 0..16);
    let k = ByteSeq::from_slice_range(&key, 16..nr * 16);
    let kn = RoundKey::from_slice(&key, nr * 16, 16);
    let state = add_round_key(input, k0);
    let state = rounds_aes(state, k);
    aes_enc_last(state, kn)
}

fn rotate_word(w: Word) -> Word {
    Word([w[1], w[2], w[3], w[0]])
}

fn slice_word(w: Word) -> Word {
    Word([
        SBOX[declassify_usize_from_U8(w[0])],
        SBOX[declassify_usize_from_U8(w[1])],
        SBOX[declassify_usize_from_U8(w[2])],
        SBOX[declassify_usize_from_U8(w[3])],
    ])
}

fn aes_keygen_assist(w: Word, rcon: U8) -> Word {
    let mut k = rotate_word(w);
    k = slice_word(k);
    k[0] = k[0] ^ rcon;
    k
}

fn key_expansion_word(w0: Word, w1: Word, i: usize, nk: usize, nr: usize) -> WordResult {
    let mut k = w1;
    let mut result = WordResult::Err(INVALID_KEY_EXPANSION_INDEX);
    if i < (4 * (nr + 1)) {
        if i % nk == 0 {
            k = aes_keygen_assist(k, RCON[i / nk]);
        } else {
            // FIXME: #85
            if nk > 6 && i % nk == 4 {
                k = slice_word(k);
            }
        }
        for i in 0..4 {
            k[i] = k[i] ^ w0[i];
        }
        result = WordResult::Ok(k);
    }
    result
}

fn key_expansion_aes(
    key: &ByteSeq,
    nk: usize,
    nr: usize,
    key_schedule_length: usize,
    key_length: usize,
    iterations: usize,
) -> ByteSeqResult {
    let mut key_ex = ByteSeq::new(key_schedule_length);
    key_ex = key_ex.update_start(key);
    let word_size = key_length;
    for j in 0..iterations {
        let i = j + word_size;
        let word = key_expansion_word(
            Word::from_slice(&key_ex, 4 * (i - word_size), 4),
            Word::from_slice(&key_ex, 4 * i - 4, 4),
            i,
            nk,
            nr,
        )?;
        key_ex = key_ex.update(4 * i, &word);
    }
    ByteSeqResult::Ok(key_ex)
}

pub(crate) fn aes_encrypt_block(
    k: &ByteSeq,
    input: Block,
    nk: usize,
    nr: usize,
    key_schedule_length: usize,
    key_length: usize,
    iterations: usize,
) -> BlockResult {
    let key_ex = key_expansion_aes(k, nk, nr, key_schedule_length, key_length, iterations)?;
    BlockResult::Ok(block_cipher_aes(input, key_ex, nr))
}

pub fn aes128_encrypt_block(k: Key128, input: Block) -> Block {
    aes_encrypt_block(
        &ByteSeq::from_seq(&k),
        input,
        KEY_LENGTH,
        ROUNDS,
        KEY_SCHEDULE_LENGTH,
        KEY_LENGTH,
        ITERATIONS,
    )
    .unwrap()
}

pub fn aes_ctr_key_block(
    k: &ByteSeq,
    n: AesNonce,
    c: U32,
    nk: usize,
    nr: usize,
    key_schedule_length: usize,
    key_length: usize,
    iterations: usize,
) -> BlockResult {
    let mut input = Block::new();
    input = input.update(0, &n);
    input = input.update(12, &U32_to_be_bytes(c));
    aes_encrypt_block(
        k,
        input,
        nk,
        nr,
        key_schedule_length,
        key_length,
        iterations,
    )
}

pub fn xor_block(block: Block, key_block: Block) -> Block {
    let mut out = block;
    for i in 0..BLOCKSIZE {
        out[i] = out[i] ^ key_block[i];
    }
    out
}

fn aes_counter_mode(
    key: &ByteSeq,
    nonce: AesNonce,
    counter: U32,
    msg: &ByteSeq,
    nk: usize,
    nr: usize,
    key_schedule_length: usize,
    key_length: usize,
    iterations: usize,
) -> ByteSeqResult {
    let mut ctr = counter;
    let mut blocks_out = ByteSeq::new(msg.len());
    let n_blocks = msg.num_exact_chunks(BLOCKSIZE);
    for i in 0..n_blocks {
        let msg_block = msg.get_exact_chunk(BLOCKSIZE, i);
        let key_block = aes_ctr_key_block(
            key,
            nonce,
            ctr,
            nk,
            nr,
            key_schedule_length,
            key_length,
            iterations,
        )?;
        blocks_out = blocks_out.set_chunk(
            BLOCKSIZE,
            i,
            &xor_block(Block::from_seq(&msg_block), key_block),
        );
        ctr = ctr + U32(1u32);
    }
    let last_block = msg.get_remainder_chunk(BLOCKSIZE);
    let last_block_len = last_block.len();
    if last_block_len != 0 {
        // Last block that needs padding
        let last_block = Block::new().update_start(&last_block);
        let key_block = aes_ctr_key_block(
            key,
            nonce,
            ctr,
            nk,
            nr,
            key_schedule_length,
            key_length,
            iterations,
        )?;
        blocks_out = blocks_out.set_chunk(
            BLOCKSIZE,
            n_blocks,
            &xor_block(last_block, key_block).slice_range(0..last_block_len),
        );
    }
    ByteSeqResult::Ok(blocks_out)
}

pub fn aes128_encrypt(key: Key128, nonce: AesNonce, counter: U32, msg: &ByteSeq) -> ByteSeq {
    aes_counter_mode(
        &ByteSeq::from_seq(&key),
        nonce,
        counter,
        msg,
        KEY_LENGTH,
        ROUNDS,
        KEY_SCHEDULE_LENGTH,
        KEY_LENGTH,
        ITERATIONS,
    )
    .unwrap()
}

pub fn aes128_decrypt(key: Key128, nonce: AesNonce, counter: U32, ctxt: &ByteSeq) -> ByteSeq {
    aes_counter_mode(
        &ByteSeq::from_seq(&key),
        nonce,
        counter,
        ctxt,
        KEY_LENGTH,
        ROUNDS,
        KEY_SCHEDULE_LENGTH,
        KEY_LENGTH,
        ITERATIONS,
    )
    .unwrap()
}

#[test]
fn test_kat_block1() {
    let msg = Block(secret_bytes!([
        0x6bu8, 0xc1u8, 0xbeu8, 0xe2u8, 0x2eu8, 0x40u8, 0x9fu8, 0x96u8, 0xe9u8, 0x3du8, 0x7eu8,
        0x11u8, 0x73u8, 0x93u8, 0x17u8, 0x2au8
    ]));
    let key = Key128(secret_bytes!([
        0x2bu8, 0x7eu8, 0x15u8, 0x16u8, 0x28u8, 0xaeu8, 0xd2u8, 0xa6u8, 0xabu8, 0xf7u8, 0x15u8,
        0x88u8, 0x09u8, 0xcfu8, 0x4fu8, 0x3cu8
    ]));
    let ctxt = secret_bytes!([
        0x3au8, 0xd7u8, 0x7bu8, 0xb4u8, 0x0du8, 0x7au8, 0x36u8, 0x60u8, 0xa8u8, 0x9eu8, 0xcau8,
        0xf3u8, 0x24u8, 0x66u8, 0xefu8, 0x97u8
    ]);

    let c = aes128_encrypt_block(key, msg);
    assert_bytes_eq!(ctxt, c);
}

#[test]
fn test_kat_block2() {
    let msg = Block::from_public_slice(&[
        0x53u8, 0x69u8, 0x6eu8, 0x67u8, 0x6cu8, 0x65u8, 0x20u8, 0x62u8, 0x6cu8, 0x6fu8, 0x63u8,
        0x6bu8, 0x20u8, 0x6du8, 0x73u8, 0x67u8,
    ]);
    let key = Key128::from_public_slice(&[
        0xaeu8, 0x68u8, 0x52u8, 0xf8u8, 0x12u8, 0x10u8, 0x67u8, 0xccu8, 0x4bu8, 0xf7u8, 0xa5u8,
        0x76u8, 0x55u8, 0x77u8, 0xf3u8, 0x9eu8,
    ]);
    let ctxt = ByteSeq::from_public_slice(&[
        0x61u8, 0x5fu8, 0x09u8, 0xfbu8, 0x35u8, 0x3fu8, 0x61u8, 0x3bu8, 0xa2u8, 0x8fu8, 0xf3u8,
        0xa3u8, 0x0cu8, 0x64u8, 0x75u8, 0x2du8,
    ]);
    let c = aes128_encrypt_block(key, msg);
    assert_bytes_eq!(ctxt, c);
}
