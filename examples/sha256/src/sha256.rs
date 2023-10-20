use hax_lib_macros as hax;
use std::convert::TryInto;

const BLOCK_SIZE: usize = 64;
const LEN_SIZE: usize = 8;
pub const K_SIZE: usize = 64;
pub const HASH_SIZE: usize = 256 / 8;

pub type Block = [u8; BLOCK_SIZE];
pub type OpTableType = [u8; 12];
pub type Sha256Digest = [u8; HASH_SIZE];
pub type RoundConstantsTable = [u32; K_SIZE];
pub type Hash = [u32; LEN_SIZE];

pub fn ch(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((!x) & z)
}

pub fn maj(x: u32, y: u32, z: u32) -> u32 {
    (x & y) ^ ((x & z) ^ (y & z))
}

const OP_TABLE: OpTableType = [2, 13, 22, 6, 11, 25, 7, 18, 3, 17, 19, 10];

#[rustfmt::skip]
const K_TABLE: RoundConstantsTable = [
        0x428a_2f98u32, 0x7137_4491u32, 0xb5c0_fbcfu32, 0xe9b5_dba5u32, 0x3956_c25bu32,
        0x59f1_11f1u32, 0x923f_82a4u32, 0xab1c_5ed5u32, 0xd807_aa98u32, 0x1283_5b01u32,
        0x2431_85beu32, 0x550c_7dc3u32, 0x72be_5d74u32, 0x80de_b1feu32, 0x9bdc_06a7u32,
        0xc19b_f174u32, 0xe49b_69c1u32, 0xefbe_4786u32, 0x0fc1_9dc6u32, 0x240c_a1ccu32,
        0x2de9_2c6fu32, 0x4a74_84aau32, 0x5cb0_a9dcu32, 0x76f9_88dau32, 0x983e_5152u32,
        0xa831_c66du32, 0xb003_27c8u32, 0xbf59_7fc7u32, 0xc6e0_0bf3u32, 0xd5a7_9147u32,
        0x06ca_6351u32, 0x1429_2967u32, 0x27b7_0a85u32, 0x2e1b_2138u32, 0x4d2c_6dfcu32,
        0x5338_0d13u32, 0x650a_7354u32, 0x766a_0abbu32, 0x81c2_c92eu32, 0x9272_2c85u32,
        0xa2bf_e8a1u32, 0xa81a_664bu32, 0xc24b_8b70u32, 0xc76c_51a3u32, 0xd192_e819u32,
        0xd699_0624u32, 0xf40e_3585u32, 0x106a_a070u32, 0x19a4_c116u32, 0x1e37_6c08u32,
        0x2748_774cu32, 0x34b0_bcb5u32, 0x391c_0cb3u32, 0x4ed8_aa4au32, 0x5b9c_ca4fu32,
        0x682e_6ff3u32, 0x748f_82eeu32, 0x78a5_636fu32, 0x84c8_7814u32, 0x8cc7_0208u32,
        0x90be_fffau32, 0xa450_6cebu32, 0xbef9_a3f7u32, 0xc671_78f2u32
    ];

const HASH_INIT: Hash = [
    0x6a09e667u32,
    0xbb67ae85u32,
    0x3c6ef372u32,
    0xa54ff53au32,
    0x510e527fu32,
    0x9b05688cu32,
    0x1f83d9abu32,
    0x5be0cd19u32,
];

#[hax::requires(i < 4)]
pub fn sigma(x: u32, i: usize, op: usize) -> u32 {
    let mut tmp: u32 = x.rotate_right(OP_TABLE[3 * i + 2].into());
    if op == 0 {
        tmp = x >> OP_TABLE[3 * i + 2]
    }
    let rot_val_1 = OP_TABLE[3 * i].into();
    let rot_val_2 = OP_TABLE[3 * i + 1].into();
    x.rotate_right(rot_val_1) ^ x.rotate_right(rot_val_2) ^ tmp
}

fn to_be_u32s(block: Block) -> Vec<u32> {
    let mut out = Vec::with_capacity(BLOCK_SIZE / 4);
    for block_chunk in block.chunks_exact(4) {
        let block_chunk_array = u32::from_be_bytes(block_chunk.try_into().unwrap());
        out.push(block_chunk_array);
    }

    out
}

pub fn schedule(block: Block) -> RoundConstantsTable {
    let b = to_be_u32s(block);
    let mut s = [0; K_SIZE];
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
            s[i] = s1.wrapping_add(t7).wrapping_add(s0).wrapping_add(t16);
        }
    }
    s
}

pub fn shuffle(ws: RoundConstantsTable, hashi: Hash) -> Hash {
    let mut h = hashi;
    for i in 0..K_SIZE {
        let a0 = h[0];
        let b0 = h[1];
        let c0 = h[2];
        let d0 = h[3];
        let e0 = h[4];
        let f0 = h[5];
        let g0 = h[6];
        let h0: u32 = h[7];

        let t1 = h0
            .wrapping_add(sigma(e0, 1, 1))
            .wrapping_add(ch(e0, f0, g0))
            .wrapping_add(K_TABLE[i])
            .wrapping_add(ws[i]);
        let t2 = sigma(a0, 0, 1).wrapping_add(maj(a0, b0, c0));

        h[0] = t1.wrapping_add(t2);
        h[1] = a0;
        h[2] = b0;
        h[3] = c0;
        h[4] = d0.wrapping_add(t1);
        h[5] = e0;
        h[6] = f0;
        h[7] = g0;
    }
    h
}

pub fn compress(block: Block, h_in: Hash) -> Hash {
    let s = schedule(block);
    let mut h = shuffle(s, h_in);
    for i in 0..8 {
        h[i] = h[i].wrapping_add(h_in[i]);
    }
    h
}

fn u32s_to_be_bytes(state: Hash) -> Sha256Digest {
    let mut out: Sha256Digest = [0u8; HASH_SIZE];
    for i in 0..LEN_SIZE {
        let tmp = state[i];
        let tmp = tmp.to_be_bytes();
        for j in 0..4 {
            out[i * 4 + j] = tmp[j];
        }
    }
    out
}

pub fn hash(msg: &[u8]) -> Sha256Digest {
    let mut h = HASH_INIT;
    let mut last_block: Block = [0; BLOCK_SIZE];
    let mut last_block_len = 0;
    for block in msg.chunks(BLOCK_SIZE) {
        if block.len() < BLOCK_SIZE {
            for i in 0..block.len() {
                last_block[i] = block[i];
            }
            last_block_len = block.len();
        } else {
            h = compress(block.try_into().unwrap(), h);
        }
    }

    last_block[last_block_len] = 0x80;
    let len_bist = (msg.len() * 8) as u64;
    let len_bist_bytes = len_bist.to_be_bytes();
    if last_block_len < BLOCK_SIZE - LEN_SIZE {
        for i in 0..LEN_SIZE {
            last_block[BLOCK_SIZE - LEN_SIZE + i] = len_bist_bytes[i];
        }
        h = compress(last_block, h);
    } else {
        let mut pad_block: Block = [0; BLOCK_SIZE];
        for i in 0..LEN_SIZE {
            pad_block[BLOCK_SIZE - LEN_SIZE + i] = len_bist_bytes[i];
        }
        h = compress(last_block, h);
        h = compress(pad_block, h);
    }

    u32s_to_be_bytes(h)
}

pub fn sha256(msg: &[u8]) -> Sha256Digest {
    hash(msg)
}
