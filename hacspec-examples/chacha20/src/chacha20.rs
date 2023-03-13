// Import hacspec and all needed definitions.
use hacspec_lib::*;

array!(State, 16, U32, type_for_indexes: StateIdx);
array!(Constants, 4, U32, type_for_indexes: ConstantsIdx);
bytes!(Block, 64);
bytes!(ChaChaIV, 12);
bytes!(ChaChaKey, 32);

fn chacha20_line(a: StateIdx, b: StateIdx, d: StateIdx, s: usize, m: State) -> State {
    let mut state = m;
    // TODO: we can't write += or ^= here right now :(
    state[a] = state[a] + state[b];
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

fn chacha20_double_round(state: State) -> State {
    let state = chacha20_quarter_round(0, 4, 8, 12, state);
    let state = chacha20_quarter_round(1, 5, 9, 13, state);
    let state = chacha20_quarter_round(2, 6, 10, 14, state);
    let state = chacha20_quarter_round(3, 7, 11, 15, state);

    let state = chacha20_quarter_round(0, 5, 10, 15, state);
    let state = chacha20_quarter_round(1, 6, 11, 12, state);
    let state = chacha20_quarter_round(2, 7, 8, 13, state);
    chacha20_quarter_round(3, 4, 9, 14, state)
}

pub fn chacha20_rounds(state: State) -> State {
    let mut st = state;
    for _i in 0..10 {
        st = chacha20_double_round(st);
    }
    st
}

pub fn chacha20_core(ctr: U32, st0: State) -> State {
    let mut state = st0;
    state[12] = state[12] + ctr;
    let k = chacha20_rounds(state);
    k + state
}

pub fn chacha20_constants_init() -> Constants {
    let mut constants = Constants::new();
    constants[0] = U32(0x6170_7865u32);
    constants[1] = U32(0x3320_646eu32);
    constants[2] = U32(0x7962_2d32u32);
    constants[3] = U32(0x6b20_6574u32);
    constants
}

pub fn chacha20_init(key: ChaChaKey, iv: ChaChaIV, ctr: U32) -> State {
    let mut st = State::new();
    st = st.update(0, &chacha20_constants_init());
    st = st.update(4, &key.to_le_U32s());
    st[12] = ctr;
    st = st.update(13, &iv.to_le_U32s());
    st
}

pub fn chacha20_key_block(state: State) -> Block {
    let state = chacha20_core(U32(0u32), state);
    Block::from_seq(&state.to_le_bytes())
}

pub fn chacha20_key_block0(key: ChaChaKey, iv: ChaChaIV) -> Block {
    let state = chacha20_init(key, iv, U32(0u32));
    chacha20_key_block(state)
}

pub fn chacha20_encrypt_block(st0: State, ctr: U32, plain: &Block) -> Block {
    let st = chacha20_core(ctr, st0);
    let pl = State::from_seq(&plain.to_le_U32s());
    let st = pl ^ st;
    Block::from_seq(&st.to_le_bytes())
}

pub fn chacha20_encrypt_last(st0: State, ctr: U32, plain: &ByteSeq) -> ByteSeq {
    let mut b = Block::new();
    b = b.update(0, plain);
    b = chacha20_encrypt_block(st0, ctr, &b);
    b.slice(0, plain.len())
}

pub fn chacha20_update(st0: State, m: &ByteSeq) -> ByteSeq {
    let mut blocks_out = ByteSeq::new(m.len());
    let n_blocks = m.num_exact_chunks(64);
    for i in 0..n_blocks {
        let msg_block = m.get_exact_chunk(64, i);
        let b = chacha20_encrypt_block(st0, U32(i as u32), &Block::from_seq(&msg_block));
        blocks_out = blocks_out.set_exact_chunk(64, i, &b);
    }
    let last_block = m.get_remainder_chunk(64);
    if last_block.len() != 0 {
        let b = chacha20_encrypt_last(st0, U32(n_blocks as u32), &last_block);
        blocks_out = blocks_out.set_chunk(64, n_blocks, &b);
    }
    blocks_out
}

pub fn chacha20(key: ChaChaKey, iv: ChaChaIV, ctr: u32, m: &ByteSeq) -> ByteSeq {
    let state = chacha20_init(key, iv, U32(ctr));
    chacha20_update(state, m)
}
