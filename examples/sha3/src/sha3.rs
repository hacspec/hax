// Import hacspec and all needed definitions.
use hacspec_lib::*;

const ROUNDS: usize = 24;
pub const SHA3224_RATE: usize = 144;
pub const SHA3256_RATE: usize = 136;
pub const SHA3384_RATE: usize = 104;
pub const SHA3512_RATE: usize = 72;
pub const SHAKE128_RATE: usize = 168;
pub const SHAKE256_RATE: usize = 136;

array!(State, 25, U64);
array!(Row, 5, U64);
bytes!(Digest224, 28);
bytes!(Digest256, 32);
bytes!(Digest384, 48);
bytes!(Digest512, 64);
array!(RoundConstants, ROUNDS, u64);
array!(RotationConstants, 25, usize);

#[rustfmt::skip]
const ROUNDCONSTANTS: RoundConstants = RoundConstants([
    0x0000_0000_0000_0001u64,  0x0000_0000_0000_8082u64,  0x8000_0000_0000_808au64,
    0x8000_0000_8000_8000u64,  0x0000_0000_0000_808bu64,  0x0000_0000_8000_0001u64,
    0x8000_0000_8000_8081u64,  0x8000_0000_0000_8009u64,  0x0000_0000_0000_008au64,
    0x0000_0000_0000_0088u64,  0x0000_0000_8000_8009u64,  0x0000_0000_8000_000au64,
    0x0000_0000_8000_808bu64,  0x8000_0000_0000_008bu64,  0x8000_0000_0000_8089u64,
    0x8000_0000_0000_8003u64,  0x8000_0000_0000_8002u64,  0x8000_0000_0000_0080u64,
    0x0000_0000_0000_800au64,  0x8000_0000_8000_000au64,  0x8000_0000_8000_8081u64,
    0x8000_0000_0000_8080u64,  0x0000_0000_8000_0001u64,  0x8000_0000_8000_8008u64,
]);

const ROTC: RotationConstants = RotationConstants([
    0, 1, 62, 28, 27, 36, 44, 6, 55, 20, 3, 10, 43, 25, 39, 41, 45, 15, 21, 8, 18, 2, 61, 56, 14,
]);

const PI: RotationConstants = RotationConstants([
    0, 6, 12, 18, 24, 3, 9, 10, 16, 22, 1, 7, 13, 19, 20, 4, 5, 11, 17, 23, 2, 8, 14, 15, 21,
]);

fn theta(mut s: State) -> State {
    let mut b = Row::new();
    for i in 0..5 {
        b[i] = s[i] ^ s[i + 5] ^ s[i + 10] ^ s[i + 15] ^ s[i + 20];
    }
    for i in 0..5 {
        let u: U64 = b[(i + 1) % 5];
        let t = b[(i + 4) % 5] ^ u.rotate_left(1);
        for j in 0..5 {
            s[5 * j + i] = s[5 * j + i] ^ t;
        }
    }
    s
}

fn rho(mut s: State) -> State {
    for i in 0..25 {
        let u: U64 = s[i];
        s[i] = u.rotate_left(ROTC[i]);
    }
    s
}

fn pi(s: State) -> State {
    let mut v = State::new();
    for i in 0..25 {
        v[i] = s[PI[i]];
    }
    v
}

fn chi(mut s: State) -> State {
    let mut b = Row::new();
    for i in 0..5 {
        for j in 0..5 {
            b[j] = s[5 * i + j];
        }
        for j in 0..5 {
            let u: U64 = b[(j + 1) % 5];
            s[5 * i + j] = s[5 * i + j] ^ (!u) & b[(j + 2) % 5];
        }
    }
    s
}

fn iota(mut s: State, rndconst: u64) -> State {
    s[0] = s[0] ^ U64::classify(rndconst);
    s
}

pub fn keccakf1600(mut s: State) -> State {
    for i in 0..ROUNDS {
        s = theta(s);
        s = rho(s);
        s = pi(s);
        s = chi(s);
        s = iota(s, ROUNDCONSTANTS[i]);
    }
    s
}

fn absorb_block(mut s: State, block: &ByteSeq) -> State {
    for i in 0..block.len() {
        let w = i >> 3u32;
        let o = 8 * (i & 7);
        s[w] = s[w] ^ U64_from_U8(block[i]) << o;
    }
    keccakf1600(s)
}

fn squeeze(mut s: State, nbytes: usize, rate: usize) -> ByteSeq {
    let mut out = ByteSeq::new(nbytes);
    for i in 0..nbytes {
        let pos = i % rate;
        let w = pos >> 3u32;
        let o = 8 * (pos & 7);
        let b = (s[w] >> o) & U64::classify(0xffu64);
        out[i] = U8_from_U64(b);
        if ((i + 1) % rate) == 0 {
            s = keccakf1600(s);
        }
    }
    out
}

fn keccak(rate: usize, data: &ByteSeq, p: u8, outbytes: usize) -> ByteSeq {
    let mut buf = ByteSeq::new(rate);
    let mut last_block_len = 0;
    let mut s = State::new();

    for i in 0..data.num_chunks(rate) {
        let (block_len, block) = data.get_chunk(rate, i);
        if block_len == rate {
            s = absorb_block(s, &block);
        } else {
            buf = buf.update_start(&block);
            last_block_len = block_len;
        }
    }
    buf[last_block_len] = U8(p);
    buf[rate - 1] = buf[rate - 1] | U8(128u8);
    s = absorb_block(s, &buf);

    squeeze(s, outbytes, rate)
}

pub fn sha3224(data: &ByteSeq) -> Digest224 {
    let t = keccak(SHA3224_RATE, data, 0x06u8, 28);
    Digest224::from_seq(&t)
}

pub fn sha3256(data: &ByteSeq) -> Digest256 {
    let t = keccak(SHA3256_RATE, data, 0x06u8, 32);
    Digest256::from_seq(&t)
}

pub fn sha3384(data: &ByteSeq) -> Digest384 {
    let t = keccak(SHA3384_RATE, data, 0x06u8, 48);
    Digest384::from_seq(&t)
}

pub fn sha3512(data: &ByteSeq) -> Digest512 {
    let t = keccak(SHA3512_RATE, data, 0x06u8, 64);
    Digest512::from_seq(&t)
}

pub fn shake128(data: &ByteSeq, outlen: usize) -> ByteSeq {
    keccak(SHAKE128_RATE, data, 0x1fu8, outlen)
}

pub fn shake256(data: &ByteSeq, outlen: usize) -> ByteSeq {
    keccak(SHAKE256_RATE, data, 0x1fu8, outlen)
}
