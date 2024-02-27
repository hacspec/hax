use super::State;
use secret_independence::*;

// pub(super) fn to_le_u32s<const L: usize>(bytes: &[u8]) -> [u32; L] {
//     assert_eq!(L, bytes.len() / 4);
//     let mut out = [0; L];
//     for (i, block) in bytes.chunks(4).enumerate() {
//         out[i] = u32::from_le_bytes(block.try_into().unwrap());
//     }
//     out
// }

macro_rules! to_le_u32s_impl {
    ($name:ident,$l:literal) => {
        pub(super) fn $name(bytes: &[u8]) -> [u32; $l] {
            // assert_eq!($l, bytes.len() / 4);
            let mut out = [0; $l];
            // for (i, block) in bytes.chunks(4).enumerate() {
            for i in 0..$l {
                out[i] = u32::from_le_bytes(bytes[4 * i..4 * i + 4].try_into().unwrap());
            }
            out
        }
    };
}
to_le_u32s_impl!(to_le_u32s_3, 3);
to_le_u32s_impl!(to_le_u32s_8, 8);
to_le_u32s_impl!(to_le_u32s_16, 16);

pub(super) fn u32s_to_le_bytes(state: &[u32; 16]) -> [u8; 64] {
    // <const L: usize>
    let mut out = [0; 64];
    for i in 0..state.len() {
        let tmp = state[i].to_le_bytes();
        for j in 0..4 {
            out[i * 4 + j] = tmp[j];
        }
    }
    out
}

pub(super) fn xor_state(mut state: State, other: State) -> State {
    for i in 0..16 {
        state[i] = state[i] ^ other[i];
    }
    state
}

pub(super) fn add_state(mut state: State, other: State) -> State {
    for i in 0..16 {
        state[i] = state[i].wrapping_add(other[i]);
    }
    state
}

pub(super) fn update_array<T:Copy, const N:usize>(mut array: [T; N], val: &[T]) -> [T; N] {
    // <const L: usize>
    assert!(N >= val.len());
    for i in 0..val.len() {
        array[i] = val[i];
    }
    array
}
