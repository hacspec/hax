mod hacspec_helper;
use hacspec_helper::*;
use secret_independence::*;

use hax_lib as hax;

type State = [U32; 16]; 
type Block = [U8; 64];
type ChaChaIV = [U8; 12];
type ChaChaKey = [U8; 32]; 

type StateIdx = hax_bounded_integers::BoundedUsize<0, 15>;

fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: u32, m: State) -> State {
    let mut state = m;
    state[a] = state[a].wrapping_add(state[b]);
    state[d] = state[d] ^ state[a];
    state[d] = state[d].rotate_left(s);
    state
}

pub fn chacha20_quarter_round(
    a: StateIdx,
    b: StateIdx,
    c: StateIdx,
    d: StateIdx,
    state: State,
) -> State {
    let state = chacha20_line(a, b, d, 16, state);
    let state = chacha20_line(c, d, b, 12, state);
    let state = chacha20_line(a, b, d, 8, state);
    chacha20_line(c, d, b, 7, state)
}

use hax_lib::*;

fn chacha20_double_round(state: State) -> State {
    let state = chacha20_quarter_round(
        0.into_checked(),
        4.into_checked(),
        8.into_checked(),
        12.into_checked(),
        state,
    );
    let state = chacha20_quarter_round(
        1.into_checked(),
        5.into_checked(),
        9.into_checked(),
        13.into_checked(),
        state,
    );
    let state = chacha20_quarter_round(
        2.into_checked(),
        6.into_checked(),
        10.into_checked(),
        14.into_checked(),
        state,
    );
    let state = chacha20_quarter_round(
        3.into_checked(),
        7.into_checked(),
        11.into_checked(),
        15.into_checked(),
        state,
    );

    let state = chacha20_quarter_round(
        0.into_checked(),
        5.into_checked(),
        10.into_checked(),
        15.into_checked(),
        state,
    );
    let state = chacha20_quarter_round(
        1.into_checked(),
        6.into_checked(),
        11.into_checked(),
        12.into_checked(),
        state,
    );
    let state = chacha20_quarter_round(
        2.into_checked(),
        7.into_checked(),
        8.into_checked(),
        13.into_checked(),
        state,
    );
    chacha20_quarter_round(
        3.into_checked(),
        4.into_checked(),
        9.into_checked(),
        14.into_checked(),
        state,
    )
}

pub fn chacha20_rounds(state: State) -> State {
    let mut st = state;
    for _i in 0..10 {
        st = chacha20_double_round(st);
    }
    st
}

pub fn chacha20_core(ctr: u32, st0: State) -> State {
    let mut state = st0;
    state[12] = state[12].wrapping_add(ctr);
    let k = chacha20_rounds(state);
    add_state(state, k)
}

pub fn chacha20_init(key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> State {
    let key_u32: [U32; 8] = <[U32;8]>::from_le_bytes(key).unwrap(); 
    let iv_u32: [U32; 3] = <[U32;3]>::from_le_bytes(iv).unwrap();
    [
        0x6170_7865.into(),
        0x3320_646e.into(),
        0x7962_2d32.into(),
        0x6b20_6574.into(),
        key_u32[0],
        key_u32[1],
        key_u32[2],
        key_u32[3],
        key_u32[4],
        key_u32[5],
        key_u32[6],
        key_u32[7],
        ctr.into(),
        iv_u32[0],
        iv_u32[1],
        iv_u32[2],
    ]
}

pub fn chacha20_key_block(state: State) -> Block {
    let state = chacha20_core(0u32, state);
    state.to_le_bytes().unwrap()
}

pub fn chacha20_key_block0(key: &ChaChaKey, iv: &ChaChaIV) -> Block {
    let state = chacha20_init(key, iv, 0u32);
    chacha20_key_block(state)
}

pub fn chacha20_encrypt_block(st0: State, ctr: u32, plain: &Block) -> Block {
    let st = chacha20_core(ctr, st0);
    let pl: State = State::from_le_bytes(plain).unwrap();
    let encrypted = xor_state(st, pl);
    encrypted.to_le_bytes().unwrap()
}

#[hax::requires(plain.len() <= 64)]
pub fn chacha20_encrypt_last(st0: State, ctr: u32, plain: &[U8]) -> Vec<U8> {
    let mut b: Block = [0.into(); 64];
    b = update_array(b, plain);
    b = chacha20_encrypt_block(st0, ctr, &b);
    b[0..plain.len()].to_vec()
}

pub fn chacha20_update(st0: State, m: &[U8]) -> Vec<U8> {
    let mut blocks_out = Vec::new();
    let num_blocks = m.len() / 64;
    let remainder_len = m.len() % 64;
    for i in 0..num_blocks {
        // Full block
        let b =
            chacha20_encrypt_block(st0, i as u32, &m[64 * i..(64 * i + 64)].try_into().unwrap());
        hax_lib::assume!(blocks_out.len() == i * 64);
        blocks_out.extend_from_slice(&b);
    }
    hax_lib::assume!(blocks_out.len() == num_blocks * 64);
    if remainder_len != 0 {
        // Last block
        let b = chacha20_encrypt_last(st0, num_blocks as u32, &m[64 * num_blocks..m.len()]);
        blocks_out.extend_from_slice(&b);
    }
    blocks_out
}

pub fn chacha20(m: &[U8], key: &ChaChaKey, iv: &ChaChaIV, ctr: u32) -> Vec<U8> {
    let state = chacha20_init(key, iv, ctr);
    chacha20_update(state, m) 
}
