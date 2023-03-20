use hacspec_lib::*;

array!(State, 12, U32, type_for_indexes: StateIdx);

fn swap(mut s: State, i: StateIdx, j: StateIdx) -> State {
    let tmp = s[i];
    s[i] = s[j];
    s[j] = tmp;
    s
}

fn gimli_round(mut s: State, r: u32) -> State {
    for col in 0usize..4 {
        let x = s[col].rotate_left(24);
        let y = s[col + 4].rotate_left(9);
        let z = s[col + 8];

        s[col + 8] = x ^ (z << 1) ^ ((y & z) << 2);
        s[col + 4] = y ^ x ^ ((x | z) << 1);
        s[col] = z ^ y ^ ((x & y) << 3);
    }

    if (r & 3u32) == 0u32 {
        s = swap(s, 0, 1);
        s = swap(s, 2, 3);
    }

    if (r & 3u32) == 2u32 {
        s = swap(s, 0, 2);
        s = swap(s, 1, 3);
    }

    if (r & 3u32) == 0u32 {
        s[0] = s[0] ^ (U32(0x9e377900u32) | U32(r))
    }

    s
}

pub fn gimli(mut s: State) -> State {
    for rnd in 0..24 {
        let rnd = (24 - rnd) as u32;
        s = gimli_round(s, rnd);
    }

    s
}

// === Hash ===

bytes!(Block, 16);
bytes!(Digest, 32);

fn absorb_block(input_block: Block, mut s: State) -> State {
    let input_bytes = input_block.to_le_U32s();
    s[0] = s[0] ^ input_bytes[0];
    s[1] = s[1] ^ input_bytes[1];
    s[2] = s[2] ^ input_bytes[2];
    s[3] = s[3] ^ input_bytes[3];
    gimli(s)
}

fn squeeze_block(s: State) -> Block {
    let mut block = Block::new();
    for i in 0..4 {
        let s_i: U32 = s[i]; // XXX: Rust can't figure out the type here for some reason.
        let s_i_bytes = s_i.to_le_bytes();
        block[4 * i] = s_i_bytes[0];
        block[4 * i + 1] = s_i_bytes[1];
        block[4 * i + 2] = s_i_bytes[2];
        block[4 * i + 3] = s_i_bytes[3];
    }
    block
}

fn gimli_hash_state(input: &ByteSeq, mut s: State) -> State {
    let rate = Block::length();
    let chunks = input.num_exact_chunks(rate);

    for i in 0..chunks {
        let input_block = input.get_exact_chunk(rate, i);

        // Absorb full blocks
        let full_block = Block::from_seq(&input_block);
        s = absorb_block(full_block, s);
    }

    // Absorb last incomplete block (0 <= bytes <= 15)
    let input_block = input.get_remainder_chunk(rate);
    let input_block_padded = Block::new();
    let mut input_block_padded = input_block_padded.update_start(&input_block);
    input_block_padded[input_block.len()] = U8(1u8);

    // XOR in capacity part
    s[11] = s[11] ^ U32(0x01000000u32);
    s = absorb_block(input_block_padded, s);

    s
}

pub fn gimli_hash(input_bytes: &ByteSeq) -> Digest {
    let s = State::new();
    let s = gimli_hash_state(input_bytes, s);
    let output = Digest::new();
    let output = output.update_start(&squeeze_block(s));
    let s = gimli(s);
    output.update(Block::length(), &squeeze_block(s))
}

// === Cipher ===

bytes!(Nonce, 16);
bytes!(Key, 32);
bytes!(Tag, 16);

fn process_ad(ad: &ByteSeq, s: State) -> State {
    gimli_hash_state(ad, s)
}

fn process_msg(message: &ByteSeq, mut s: State) -> (State, ByteSeq) {
    let mut ciphertext = ByteSeq::new(message.len());

    let rate = Block::length();
    let num_chunks = message.num_exact_chunks(rate);

    for i in 0..num_chunks {
        // Handle Full Block
        let key_block = squeeze_block(s);
        let msg_block = message.get_exact_chunk(rate, i);
        let msg_block = Block::from_seq(&msg_block);
        ciphertext = ciphertext.set_exact_chunk(rate, i, &(msg_block ^ key_block));
        s = absorb_block(msg_block, s);
    }

    // Handle final non-full block
    let key_block = squeeze_block(s);
    let last_block = message.get_remainder_chunk(rate);
    let block_len = last_block.len();

    // This pads the block if necessary
    let msg_block_padded = Block::new();
    let mut msg_block_padded = msg_block_padded.update_start(&last_block);

    ciphertext = ciphertext.set_chunk(
        rate,
        num_chunks,
        // the slice_range cuts off the last block if it is padded
        &(msg_block_padded ^ key_block).slice_range(0..block_len),
    );
    msg_block_padded[block_len] = msg_block_padded[block_len] ^ U8(1u8);
    s[11] = s[11] ^ U32(0x01000000u32); // s_2,3
    s = absorb_block(msg_block_padded, s);

    (s, ciphertext)
}

fn process_ct(ciphertext: &ByteSeq, mut s: State) -> (State, ByteSeq) {
    let mut message = ByteSeq::new(ciphertext.len());

    let rate = Block::length();
    let num_chunks = ciphertext.num_exact_chunks(rate);

    for i in 0..num_chunks {
        let key_block = squeeze_block(s);
        let ct_block = ciphertext.get_exact_chunk(rate, i);
        let ct_block = Block::from_seq(&ct_block);
        let msg_block = ct_block ^ key_block;
        message = message.set_exact_chunk(rate, i, &(ct_block ^ key_block));
        s = absorb_block(msg_block, s);
    }

    // Handle final non-full ct_block
    let key_block = squeeze_block(s);
    let ct_final = ciphertext.get_remainder_chunk(rate);
    let block_len = ct_final.len();

    let ct_block_padded = Block::new();
    let ct_block_padded = ct_block_padded.update_start(&ct_final);

    let msg_block = ct_block_padded ^ key_block;
    message = message.set_chunk(rate, num_chunks, &msg_block.slice_range(0..block_len));

    let mut msg_block = Block::from_slice_range(&msg_block, 0..block_len);
    msg_block[block_len] = msg_block[block_len] ^ U8(1u8);
    s[11] = s[11] ^ U32(0x01000000u32); // s_2,3
    s = absorb_block(msg_block, s);

    (s, message)
}

// XXX: These two functions should maybe get a helper in the library.
pub fn nonce_to_u32s(nonce: Nonce) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(4);
    uints[0] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 0..4));
    uints[1] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 4..8));
    uints[2] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 8..12));
    uints[3] = U32_from_le_bytes(U32Word::from_slice_range(&nonce, 12..16));
    uints
}

pub fn key_to_u32s(key: Key) -> Seq<U32> {
    let mut uints = Seq::<U32>::new(8);
    uints[0] = U32_from_le_bytes(U32Word::from_slice_range(&key, 0..4));
    uints[1] = U32_from_le_bytes(U32Word::from_slice_range(&key, 4..8));
    uints[2] = U32_from_le_bytes(U32Word::from_slice_range(&key, 8..12));
    uints[3] = U32_from_le_bytes(U32Word::from_slice_range(&key, 12..16));
    uints[4] = U32_from_le_bytes(U32Word::from_slice_range(&key, 16..20));
    uints[5] = U32_from_le_bytes(U32Word::from_slice_range(&key, 20..24));
    uints[6] = U32_from_le_bytes(U32Word::from_slice_range(&key, 24..28));
    uints[7] = U32_from_le_bytes(U32Word::from_slice_range(&key, 28..32));
    uints
}

pub fn gimli_aead_encrypt(
    message: &ByteSeq,
    ad: &ByteSeq,
    nonce: Nonce,
    key: Key,
) -> (ByteSeq, Tag) {
    // Add nonce and key to state
    let s = State::from_seq(&nonce_to_u32s(nonce).concat(&key_to_u32s(key)));
    let s = gimli(s);

    let s = process_ad(ad, s);
    let (s, ciphertext) = process_msg(message, s);

    let tag = squeeze_block(s);
    let tag = Tag::from_seq(&tag);

    (ciphertext, tag)
}

pub fn gimli_aead_decrypt(
    ciphertext: &ByteSeq,
    ad: &ByteSeq,
    tag: Tag,
    nonce: Nonce,
    key: Key,
) -> ByteSeq {
    // Add nonce and key to state
    let s = State::from_seq(&nonce_to_u32s(nonce).concat(&key_to_u32s(key)));
    let s = gimli(s);

    let s = process_ad(ad, s);
    let (s, message) = process_ct(ciphertext, s);

    let my_tag = squeeze_block(s);
    let my_tag = Tag::from_seq(&my_tag);

    let mut out = ByteSeq::new(0);
    if my_tag.equal(tag) {
        out = message;
    };

    out
}
