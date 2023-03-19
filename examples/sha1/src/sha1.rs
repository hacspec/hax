#![allow(non_snake_case)]

// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(Schedule, 80, U32);

const BLOCK_WORDS: usize = 512 / 32;
const HASH_WORDS: usize = 160 / 32;
array!(Block, BLOCK_WORDS, U32);
array!(Hash, HASH_WORDS, U32);

const BLOCK_BYTES: usize = 512 / 8;
const HASH_BYTES: usize = 160 / 8;
bytes!(BlockBytes, BLOCK_BYTES);
bytes!(Sha1Digest, HASH_BYTES);

const BITLENGTH_BYTES: usize = 64 / 8;

pub fn ch(x: U32, y: U32, z: U32) -> U32 {
    (x & y) ^ ((!x) & z)
}

pub fn parity(x: U32, y: U32, z: U32) -> U32 {
    x ^ y ^ z
}

pub fn maj(x: U32, y: U32, z: U32) -> U32 {
    (x & y) ^ (x & z) ^ (y & z)
}

const HASH_INIT: Hash = Hash(secret_array!(
    U32,
    [
        0x67452301u32,
        0xefcdab89u32,
        0x98badcfeu32,
        0x10325476u32,
        0xc3d2e1f0u32
    ]
));

pub fn compress(M_bytes: BlockBytes, mut H: Hash) -> Hash {
    let M = M_bytes.to_be_U32s();
    // 1. Prepare message schedule
    let mut W = Schedule::new();
    for t in 0..80 {
        if t < 16 {
            W[t] = M[t];
        } else {
            W[t] = U32::rotate_left(W[t - 3] ^ W[t - 8] ^ W[t - 14] ^ W[t - 16], 1);
        };
    }
    // 2. Initialize five working variables with previous hash value
    let mut a = H[0];
    let mut b = H[1];
    let mut c = H[2];
    let mut d = H[3];
    let mut e = H[4];
    // 3. (Apply message schedule)
    for t in 0..80 {
        let mut T = U32::ZERO();
        if 0 <= t && t < 20 {
            T = U32::rotate_left(a, 5) + ch(b, c, d) + e + U32(0x5a827999u32) + W[t];
        }
        if 20 <= t && t < 40 {
            T = U32::rotate_left(a, 5) + parity(b, c, d) + e + U32(0x6ed9eba1u32) + W[t];
        }
        if 40 <= t && t < 60 {
            T = U32::rotate_left(a, 5) + maj(b, c, d) + e + U32(0x8f1bbcdcu32) + W[t];
        }
        if 60 <= t && t < 80 {
            T = U32::rotate_left(a, 5) + parity(b, c, d) + e + U32(0xca62c1d6u32) + W[t];
        }
        e = d;
        d = c;
        c = U32::rotate_left(b, 30);
        b = a;
        a = T;
    }
    // 4. Compute intermediate hash value
    H[0] = a + H[0];
    H[1] = b + H[1];
    H[2] = c + H[2];
    H[3] = d + H[3];
    H[4] = e + H[4];
    H
}

pub fn hash(msg: &ByteSeq) -> Sha1Digest {
    let mut H = HASH_INIT;
    // Compress full blocks
    for i in 0..msg.num_exact_chunks(BLOCK_BYTES) {
        let raw_bytes = msg.get_exact_chunk(BLOCK_BYTES, i);
        let block_bytes = BlockBytes::from_seq(&raw_bytes);
        H = compress(block_bytes, H);
    }
    // Compress last block(s)
    let raw_bytes = msg.get_remainder_chunk(BLOCK_BYTES);
    let mut block_bytes = BlockBytes::new().update_start(&raw_bytes);
    block_bytes[raw_bytes.len()] = U8(0b10000000u8);
    let message_bitlength = U64((msg.len() * 8) as u64);
    // Message length either fits in the last block or gets its own block
    if raw_bytes.len() < BLOCK_BYTES - BITLENGTH_BYTES {
        block_bytes = block_bytes.update(
            BLOCK_BYTES - BITLENGTH_BYTES,
            &U64_to_be_bytes(message_bitlength),
        );
        H = compress(block_bytes, H);
    } else {
        H = compress(block_bytes, H);
        let mut pad_block = BlockBytes::new();
        pad_block = pad_block.update(
            BLOCK_BYTES - BITLENGTH_BYTES,
            &U64_to_be_bytes(message_bitlength),
        );
        H = compress(pad_block, H);
    }
    Sha1Digest::from_seq(&H.to_be_bytes())
}

pub fn sha1(msg: &ByteSeq) -> Sha1Digest {
    hash(msg)
}
