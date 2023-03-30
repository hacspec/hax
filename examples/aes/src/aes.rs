use hacspec_lib::*;

struct x {
    temp : usize
}

fn x_test() -> x {
    x { temp: 3 }
}

public_bytes!(Name, 3);

fn name_test() -> Name {
    Name ([3u8, 4u8, 5u8])
}

enum p {
    CASE1 (usize),
    CASE2 (u8),
}

fn enum_test() -> p {
    p::CASE1(32)
}

fn private() -> U64 {
    U64(5)
}

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
bytes!(SBox, 2);
bytes!(RCon, 15);
bytes!(Bytes144, 144);
bytes!(Bytes176, KEY_SCHEDULE_LENGTH);
bytes!(Key128, BLOCKSIZE);

type ByteSeqResult = Result<ByteSeq, u8>;
type BlockResult = Result<Block, u8>;
type WordResult = Result<Word, u8>;

const SBOX: SBox = SBox(secret_bytes!([0x8d,0x10])); // 0x8d,0x8d

// const RCON: RCon = RCon(secret_bytes!([
//     0x8du8, 0x01u8, 0x02u8, 0x04u8, 0x08u8, 0x10u8, 0x20u8, 0x40u8, 0x80u8, 0x1bu8, 0x36u8, 0x6cu8,
//     0xd8u8, 0xabu8, 0x4du8
// ]));
