use hacspec_lib::*;

public_bytes!(SBox, 256);
public_bytes!(RCon, 15);

public_bytes!(PBytes256, 256);
const SBOX: SBox = SBox([
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
]);

const RCON: RCon = RCon([
    0x8du8, 0x01u8, 0x02u8, 0x04u8, 0x08u8, 0x10u8, 0x20u8, 0x40u8, 0x80u8, 0x1bu8, 0x36u8, 0x6cu8,
    0xd8u8, 0xabu8, 0x4du8
]);

fn index_u32 (s : u128, i : usize) -> u32 {
    ((s >> i * 32) % (1_u128 << 32)) as u32
}
fn index_u8 (s : u32, i : usize) -> u8 {
    ((s >> i * 8) % (1_u32 << 8)) as u8
}

fn rebuild_u32(s0 : u8, s1 : u8, s2 : u8, s3 : u8) -> u32 {
    (s0 as u32) | (((s1 as u32) << 8) | (((s2 as u32) << 16) | ((s3 as u32) << 24)))
}
fn rebuild_u128(s0 : u32, s1 : u32, s2 : u32, s3 : u32) -> u128 {
    (s0 as u128) | (((s1 as u128) << 32) | (((s2 as u128) << 64) | ((s3 as u128) << 96)))
}

fn subword(v : u32) -> u32 {
    rebuild_u32(SBOX[index_u8(v, 0)],
                SBOX[index_u8(v, 1)],
                SBOX[index_u8(v, 2)],
                SBOX[index_u8(v, 3)])
}

fn rotword(v: u32) -> u32 {
    // (v >> 8) | (v << 24)
    rebuild_u32 (
        index_u8(v, 1),
        index_u8(v, 2),
        index_u8(v, 3),
        index_u8(v, 0))
}

fn vpshufd1 (s: u128, o: u8, i : usize) -> u32 {
    index_u32(s >> 32 * ((o >> (2 * i)) % 4_u8) as usize, 0)
}

fn vpshufd (s: u128, o: u8) -> u128 {
    let d1 : u32 = vpshufd1(s, o, 0);
    let d2 : u32 = vpshufd1(s, o, 1);
    let d3 : u32 = vpshufd1(s, o, 2);
    let d4 : u32 = vpshufd1(s, o, 3);

    rebuild_u128(d1, d2, d3, d4)
}

fn vshufps(s1: u128, s2: u128, o: u8) -> u128 {
    let d1 : u32 = vpshufd1(s1, o, 0);
    let d2 : u32 = vpshufd1(s1, o, 1);
    let d3 : u32 = vpshufd1(s2, o, 2);
    let d4 : u32 = vpshufd1(s2, o, 3);

    rebuild_u128(d1, d2, d3, d4)
}

// note the constants might be off, I've interpreted arrays from `aes.jinc` as low endian, they might be big endian
fn key_combine(rkey: u128, temp1: u128, temp2: u128) -> (u128, u128) {
    let temp1 = vpshufd(temp1, 0xFF);
    let temp2 = vshufps(temp2, rkey, 16u8); // 4u8
    let rkey = rkey ^ temp2;
    let temp2 = vshufps(temp2, rkey, 140u8); // 50u8
    let rkey = rkey ^ temp2;
    let rkey = rkey ^ temp1;
    (rkey, temp2)
}

// See: https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
fn aeskeygenassist(v1: u128, v2: u8) -> u128 {
    let x1 = index_u32(v1, 1);
    let x3 = index_u32(v1, 3);
    let y0 = subword(x1);
    let y1 = rotword(y0) ^ ((v2 as u32));
    let y2 = subword(x3);
    let y3 = rotword(y2) ^ ((v2 as u32));
    rebuild_u128(y0, y1, y2, y3)
}

fn key_expand(rcon: u8, rkey: u128, temp2: u128) -> (u128, u128) {
    let temp1 = aeskeygenassist(rkey, rcon);
    let (rkey, temp2) = key_combine(rkey, temp1, temp2);
    (rkey, temp2)
}

type KeyList = Seq<u128>;

fn keys_expand(key : u128) -> KeyList {
    let mut rkeys : KeyList = KeyList::new(0);
    let mut key = key;
    rkeys = rkeys.push(&key);
    let mut temp2 : u128 = 0;
    for round in 1 .. 11 {
        let rcon = RCON[round];
        let (key_temp, temp2_temp) = key_expand(rcon, key, temp2);
        key = key_temp;
        temp2 = temp2_temp;
        rkeys = rkeys.push(&key);
    }
    rkeys
}

fn subbytes (s : u128) -> u128 {
    rebuild_u128(subword(index_u32(s, 0)),
                 subword(index_u32(s, 1)),
                 subword(index_u32(s, 2)),
                 subword(index_u32(s, 3)))
}

fn matrix_index (s : u128, i : usize, j : usize) -> u8 {
    index_u8(index_u32(s, j), i)
}

fn shiftrows (s : u128) -> u128 {
    rebuild_u128(
        rebuild_u32(matrix_index(s,0,0),matrix_index(s,1,1),matrix_index(s,2,2),matrix_index(s,3,3)),
        rebuild_u32(matrix_index(s,0,1),matrix_index(s,1,2),matrix_index(s,2,3),matrix_index(s,3,0)),
        rebuild_u32(matrix_index(s,0,2),matrix_index(s,1,3),matrix_index(s,2,0),matrix_index(s,3,1)),
        rebuild_u32(matrix_index(s,0,3),matrix_index(s,1,0),matrix_index(s,2,1),matrix_index(s,3,2)))
}

fn xtime(x: u8) -> u8 {
    let x1 = x << 1;
    let x7 = x >> 7;
    let x71 = x7 & 0x01u8;
    let x711b = x71 * 0x1bu8;
    x1 ^ x711b
}

fn mixcolumn(c: usize, state: u128) -> u32 {
    let s0 = matrix_index(state, 0, c);
    let s1 = matrix_index(state, 1, c);
    let s2 = matrix_index(state, 2, c);
    let s3 = matrix_index(state, 3, c);
    let tmp = s0 ^ s1 ^ s2 ^ s3;
    let r0 = s0 ^ tmp ^ (xtime(s0 ^ s1));
    let r1 = s1 ^ tmp ^ (xtime(s1 ^ s2));
    let r2 = s2 ^ tmp ^ (xtime(s2 ^ s3));
    let r3 = s3 ^ tmp ^ (xtime(s3 ^ s0));
    rebuild_u32(r0, r1, r2, r3)
}

fn mixcolumns(state: u128) -> u128 {
    let c0 = mixcolumn(0, state);
    let c1 = mixcolumn(1, state);
    let c2 = mixcolumn(2, state);
    let c3 = mixcolumn(3, state);
    rebuild_u128(c0, c1, c2, c3)
}

fn aesenc (state : u128, rkey : u128) -> u128 {
    let state = shiftrows(state);
    let state = subbytes(state);
    let state = mixcolumns(state);
    state ^ rkey
}

fn aesenclast (state : u128, rkey : u128) -> u128 {
    let state = shiftrows(state);
    let state = subbytes(state);
    state ^ rkey
}

fn aes_rounds (rkeys : KeyList, inp : u128) -> u128 {
    let mut state : u128 = inp ^ rkeys[0];
    // TODO:
    for round in 1 .. 10 {
        state = aesenc(state, rkeys[round])
    }
    aesenclast(state, rkeys[10])
}

fn aes(key : u128, inp : u128) -> u128 {
    let rkeys = keys_expand(key);
    aes_rounds(rkeys, inp)
}

#[test]
fn test_aeskeygenassist() {

    let key = 0x3c4fcf098815f7aba6d2ae2816157e2bu128;
    println!("{:X?} vs {:X?}", aeskeygenassist(key, RCON[1]), 0x01eb848beb848a013424b5e524b5e434u128);
    assert_eq!(aeskeygenassist(0x3c4fcf098815f7aba6d2ae2816157e2bu128, RCON[1]), 0x01eb848beb848a013424b5e524b5e434u128);
}

#[test]
fn test_key_combine() {
    let key = 0x3c4fcf098815f7aba6d2ae2816157e2bu128;
    let (lhs, _) = key_combine(key, aeskeygenassist(key, RCON[1]), 0);

    let rhs = 0x05766c2a3939a323b12c548817fefaa0u128;

    println!("{:X?} vs {:X?}", lhs, rhs);
    assert_eq!(lhs, rhs, "left: {:x} \n right: {:x}", lhs, rhs);
}

// test vector from
// https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
#[test]
fn test_mixcolumns() {
    let inp = 0x627a6f6644b109c82b18330a81c3b3e5;
    let lhs = mixcolumns(inp);
    let rhs = 0x7b5b54657374566563746f725d53475d;
    assert_eq!(lhs, rhs, "\n left: {:x}\nright: {:x}\n", lhs, rhs)
}

// test vector from
// https://www.intel.com/content/dam/doc/white-paper/advanced-encryption-standard-new-instructions-set-paper.pdf
#[test]
fn test_aesenc() {
    let rkey = 0x48692853686179295b477565726f6e5d;
    let state = 0x7b5b54657374566563746f725d53475d;
    let lhs = aesenc(state, rkey);
    let rhs = 0xa8311c2f9fdba3c58b104b58ded7e595;
    assert_eq!(lhs, rhs, "\n left: {:x}\nright: {:x}\n", lhs, rhs)
}

// NIST test vector: https://csrc.nist.gov/publications/detail/fips/197/final -- (p.33)
#[test]
fn test_aes() {
    let key = 0x3c4fcf098815f7aba6d2ae2816157e2bu128;
    let msg = 0x340737e0a29831318d305a88a8f64332u128;
    let ctx = 0x320b6a19978511dcfb09dc021d842539u128;

    let c = aes(key, msg);
    assert_eq!(ctx, c);
}
