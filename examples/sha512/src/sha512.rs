// Import hacspec and all needed definitions.
use hacspec_lib::*;

const BLOCK_SIZE: usize = 128;
const LEN_SIZE: usize = 16;
pub const K_SIZE: usize = 80;
pub const HASH_SIZE: usize = 512 / 8;

bytes!(Block, BLOCK_SIZE);
array!(OpTableType, 12, usize);
bytes!(Sha512Digest, HASH_SIZE);
array!(RoundConstantsTable, K_SIZE, U64);
array!(Hash, 8, U64);

fn ch(x: U64, y: U64, z: U64) -> U64 {
    (x & y) ^ ((!x) & z)
}

fn maj(x: U64, y: U64, z: U64) -> U64 {
    (x & y) ^ ((x & z) ^ (y & z))
}

const OP_TABLE: OpTableType = OpTableType([28, 34, 39, 14, 18, 41, 1, 8, 7, 19, 61, 6]);

#[rustfmt::skip]
const K_TABLE: RoundConstantsTable = RoundConstantsTable(secret_array!(
    U64,
    [
        0x428a2f98d728ae22u64, 0x7137449123ef65cdu64, 0xb5c0fbcfec4d3b2fu64, 0xe9b5dba58189dbbcu64, 
        0x3956c25bf348b538u64, 0x59f111f1b605d019u64, 0x923f82a4af194f9bu64, 0xab1c5ed5da6d8118u64, 
        0xd807aa98a3030242u64, 0x12835b0145706fbeu64, 0x243185be4ee4b28cu64, 0x550c7dc3d5ffb4e2u64, 
        0x72be5d74f27b896fu64, 0x80deb1fe3b1696b1u64, 0x9bdc06a725c71235u64, 0xc19bf174cf692694u64, 
        0xe49b69c19ef14ad2u64, 0xefbe4786384f25e3u64, 0x0fc19dc68b8cd5b5u64, 0x240ca1cc77ac9c65u64, 
        0x2de92c6f592b0275u64, 0x4a7484aa6ea6e483u64, 0x5cb0a9dcbd41fbd4u64, 0x76f988da831153b5u64, 
        0x983e5152ee66dfabu64, 0xa831c66d2db43210u64, 0xb00327c898fb213fu64, 0xbf597fc7beef0ee4u64, 
        0xc6e00bf33da88fc2u64, 0xd5a79147930aa725u64, 0x06ca6351e003826fu64, 0x142929670a0e6e70u64, 
        0x27b70a8546d22ffcu64, 0x2e1b21385c26c926u64, 0x4d2c6dfc5ac42aedu64, 0x53380d139d95b3dfu64, 
        0x650a73548baf63deu64, 0x766a0abb3c77b2a8u64, 0x81c2c92e47edaee6u64, 0x92722c851482353bu64, 
        0xa2bfe8a14cf10364u64, 0xa81a664bbc423001u64, 0xc24b8b70d0f89791u64, 0xc76c51a30654be30u64, 
        0xd192e819d6ef5218u64, 0xd69906245565a910u64, 0xf40e35855771202au64, 0x106aa07032bbd1b8u64, 
        0x19a4c116b8d2d0c8u64, 0x1e376c085141ab53u64, 0x2748774cdf8eeb99u64, 0x34b0bcb5e19b48a8u64, 
        0x391c0cb3c5c95a63u64, 0x4ed8aa4ae3418acbu64, 0x5b9cca4f7763e373u64, 0x682e6ff3d6b2b8a3u64, 
        0x748f82ee5defb2fcu64, 0x78a5636f43172f60u64, 0x84c87814a1f0ab72u64, 0x8cc702081a6439ecu64, 
        0x90befffa23631e28u64, 0xa4506cebde82bde9u64, 0xbef9a3f7b2c67915u64, 0xc67178f2e372532bu64, 
        0xca273eceea26619cu64, 0xd186b8c721c0c207u64, 0xeada7dd6cde0eb1eu64, 0xf57d4f7fee6ed178u64, 
        0x06f067aa72176fbau64, 0x0a637dc5a2c898a6u64, 0x113f9804bef90daeu64, 0x1b710b35131c471bu64, 
        0x28db77f523047d84u64, 0x32caab7b40c72493u64, 0x3c9ebe0a15c9bebcu64, 0x431d67c49c100d4cu64, 
        0x4cc5d4becb3e42b6u64, 0x597f299cfc657e2au64, 0x5fcb6fab3ad6faecu64, 0x6c44198c4a475817u64
    ]
));

const HASH_INIT: Hash = Hash(secret_array!(
    U64,
    [
        0x6a09e667f3bcc908u64,
        0xbb67ae8584caa73bu64,
        0x3c6ef372fe94f82bu64,
        0xa54ff53a5f1d36f1u64,
        0x510e527fade682d1u64,
        0x9b05688c2b3e6c1fu64,
        0x1f83d9abfb41bd6bu64,
        0x5be0cd19137e2179u64
    ]
));

fn sigma(x: U64, i: usize, op: usize) -> U64 {
    let mut tmp: U64 = x.rotate_right(OP_TABLE[3 * i + 2]);
    if op == 0 {
        tmp = x >> OP_TABLE[3 * i + 2]
    }
    x.rotate_right(OP_TABLE[3 * i]) ^ x.rotate_right(OP_TABLE[3 * i + 1]) ^ tmp
}

fn schedule(block: Block) -> RoundConstantsTable {
    let b = block.to_be_U64s();
    let mut s = RoundConstantsTable::new();
    for i in 0..K_SIZE {
        if i < 16 {
            s[i] = b[i];
        } else {
            let t16 = s[i - 16];
            let t15 = s[i - 15];
            let t7 = s[i - 7];
            let t2 = s[i - 2];
            let s1 = sigma(t2, 3, 0);
            let s0 = sigma(t15, 2, 0);
            s[i] = s1 + t7 + s0 + t16;
        }
    }
    s
}

fn shuffle(ws: RoundConstantsTable, hashi: Hash) -> Hash {
    let mut h = hashi;
    for i in 0..K_SIZE {
        let a0 = h[0];
        let b0 = h[1];
        let c0 = h[2];
        let d0 = h[3];
        let e0 = h[4];
        let f0 = h[5];
        let g0 = h[6];
        let h0: U64 = h[7];

        let t1 = h0 + sigma(e0, 1, 1) + ch(e0, f0, g0) + K_TABLE[i] + ws[i];
        let t2 = sigma(a0, 0, 1) + maj(a0, b0, c0);

        h[0] = t1 + t2;
        h[1] = a0;
        h[2] = b0;
        h[3] = c0;
        h[4] = d0 + t1;
        h[5] = e0;
        h[6] = f0;
        h[7] = g0;
    }
    h
}

fn compress(block: Block, h_in: Hash) -> Hash {
    let s = schedule(block);
    let mut h = shuffle(s, h_in);
    for i in 0..8 {
        h[i] = h[i] + h_in[i];
    }
    h
}

pub fn hash(msg: &ByteSeq) -> Sha512Digest {
    let mut h = HASH_INIT;
    // FIXME: #96 use exact_chunks
    let mut last_block = Block::new();
    let mut last_block_len = 0;
    for i in 0..msg.num_chunks(BLOCK_SIZE) {
        let (block_len, block) = msg.get_chunk(BLOCK_SIZE, i);
        if block_len < BLOCK_SIZE {
            last_block = Block::new().update_start(&block);
            last_block_len = block_len;
        } else {
            let compress_input = Block::from_seq(&block);
            h = compress(compress_input, h);
        }
    }

    last_block[last_block_len] = U8(0x80u8);
    let len_bist = U128((msg.len() * 8) as u128);
    if last_block_len < BLOCK_SIZE - LEN_SIZE {
        last_block = last_block.update(BLOCK_SIZE - LEN_SIZE, &U128_to_be_bytes(len_bist));
        h = compress(last_block, h);
    } else {
        let mut pad_block = Block::new();
        pad_block = pad_block.update(BLOCK_SIZE - LEN_SIZE, &U128_to_be_bytes(len_bist));
        h = compress(last_block, h);
        h = compress(pad_block, h);
    }

    Sha512Digest::from_seq(&h.to_be_bytes())
}

pub fn sha512(msg: &ByteSeq) -> Sha512Digest {
    hash(msg)
}
