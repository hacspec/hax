// Import hacspec and all needed definitions.
use hacspec_lib::*;

const BLOCKSIZE: usize = 16;

bytes!(Gf128Block, BLOCKSIZE);
bytes!(Gf128Key, BLOCKSIZE);
bytes!(Gf128Tag, BLOCKSIZE);

type Element = U128;
const IRRED: Element = U128(0xE100_0000_0000_0000_0000_0000_0000_0000u128);

fn fadd(x: Element, y: Element) -> Element {
    x ^ y
}

fn fmul(x: Element, y: Element) -> Element {
    let mut res: Element = U128(0u128);
    let mut sh = x;
    for i in 0..128 {
        if (y & (U128(1u128) << (127 - i))).declassify() != U128(0u128).declassify() {
            res = res ^ sh;
        }
        if (sh & U128(1u128)).declassify() != U128(0u128).declassify() {
            sh = (sh >> 1) ^ IRRED;
        } else {
            sh = sh >> 1;
        }
    }
    res
}

// GMAC

// TODO: block is actually subblock
fn encode(block: Gf128Block) -> Element {
    U128_from_be_bytes(U128Word::from_seq(&block))
}

fn decode(e: Element) -> Gf128Block {
    Gf128Block::from_seq(&U128_to_be_bytes(e))
}

// TODO: block is actually subblock
fn update(r: Element, block: Gf128Block, acc: Element) -> Element {
    fmul(fadd(encode(block), acc), r)
}

fn poly(msg: &ByteSeq, r: Element) -> Element {
    let l = msg.len();
    let n_blocks: usize = l / BLOCKSIZE;
    let rem = l % BLOCKSIZE;
    let mut acc = U128(0u128);
    for i in 0..n_blocks {
        let k = i * BLOCKSIZE;
        let mut block = Gf128Block::new();
        block = block.update_start(&msg.slice_range(k..k + BLOCKSIZE));
        acc = update(r, block, acc);
    }
    if rem != 0 {
        let k = n_blocks * BLOCKSIZE;
        let mut last_block = Gf128Block::new();
        last_block = last_block.update_slice(0, msg, k, rem);
        acc = update(r, last_block, acc);
    }
    acc
}

pub fn gmac(text: &ByteSeq, k: Gf128Key) -> Gf128Tag {
    let s = Gf128Block::new();
    let r = encode(Gf128Block::from_seq(&k));
    let a = poly(text, r);
    Gf128Tag::from_seq(&decode(fadd(a, encode(s))))
}

#[test]
fn test_gmac() {
    let msg = ByteSeq::from_hex("feedfacedeadbeeffeedfacedeadbeefabaddad20000000000000000000000005a8def2f0c9e53f1f75d7853659e2a20eeb2b22aafde6419a058ab4f6f746bf40fc0c3b780f244452da3ebf1c5d82cdea2418997200ef82e44ae7e3f");
    let key = Gf128Key::from_hex("acbef20579b4b8ebce889bac8732dad7");
    let output = Gf128Tag::from_hex("cc9ae9175729a649936e890bd971a8bf");
    let tag = gmac(&msg, key);
    assert!(output.declassify_eq(&tag));
}
