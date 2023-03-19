#![allow(unused_assignments)]
#![allow(non_snake_case)]
/*
 * This is a subset of strobe needed to implement Merlin. Some functions
 * are therefore missing. See the Strobe specification for details:
 * https://strobe.sourceforge.io/specs/ 
 *
 * Or see the original research paper:
 * https://strobe.sourceforge.io/papers/strobe-latest.pdf
 */

use hacspec_lib::*;
use hacspec_sha3::*;

// === Constants === //

const STROBE_R: u8 = 166u8;

const FLAG_I: u8 = 1u8; //Not used in this strobe-subset
const FLAG_A: u8 = 1u8 << 1;
const FLAG_C: u8 = 1u8 << 2;
//const FLAG_T: u8 = 1u8 << 3; //Not used in this strobe-subset
const FLAG_M: u8 = 1u8 << 4;
const FLAG_K: u8 = 1u8 << 5;

// === Types === //

type StateU64 = State;
array!(StateU8, 200, U8);

// (state, pos, pos_begin, cur_fl)
pub type Strobe = (StateU8, u8, u8, u8);

// === Helper Functions === //

fn transmute_state_to_u64(state: StateU8) -> StateU64 {
	let mut new_state = StateU64::new();

	for i in 0..new_state.len() {
		let mut word = U64Word::new();
		for j in 0..word.len() {
			word[j] = state[i*8 + j];
		}
		new_state[i] = U64_from_le_bytes(word);
	}

	new_state
}

fn transmute_state_to_u8(state: StateU64) -> StateU8 {
	let mut new_state = StateU8::new();

	for i in 0..state.len() {
		let bytes = state[i].to_le_bytes();
		for j in 0..bytes.len() {
			new_state[i*8+j] = bytes[j]
		}
	}

	new_state
}

// === Internal Functions === //

fn run_f(strobe: Strobe) -> Strobe {
	let (mut state, mut pos, mut pos_begin, cur_fl) = strobe;

	state[pos] = state[pos] ^ U8(pos_begin);
	state[pos + 1u8] = state[pos + 1u8] ^ U8(0x04u8);
	state[STROBE_R + 1u8] = state[STROBE_R + 1u8] ^ U8(0x80u8);
	let state_U64 = transmute_state_to_u64(state);
	state = transmute_state_to_u8(keccakf1600(state_U64));

	pos = 0u8;
	pos_begin = 0u8;

	(state, pos, pos_begin, cur_fl)
}

fn absorb(strobe: Strobe, data: Seq::<U8>) -> Strobe {
	let (mut state, mut pos, mut pos_begin, mut cur_fl) = strobe;

	for i in 0..data.len() {
		state[pos] = state[pos] ^ data[i];
		pos = pos + 1u8;
		if pos == STROBE_R {
			let (s, p, pb, cf) = run_f((state, pos, pos_begin, cur_fl));
			state = s;
			pos = p;
			pos_begin = pb;
			cur_fl = cf;
		}
	}

	(state, pos, pos_begin, cur_fl)
}

fn squeeze(strobe: Strobe, mut data: Seq<U8>) -> (Strobe, Seq<U8>) {
	let (mut state, mut pos, mut pos_begin, mut cur_fl) = strobe;

	for i in 0..data.len() {
		data[i] = state[pos];
		state[pos] = U8::classify(0u8);
		pos = pos + 1u8;
		if pos == STROBE_R {
			let (s, p, pb, cf) = run_f((state.clone(), pos, pos_begin, cur_fl));
			state = s;
			pos = p;
			pos_begin = pb;
			cur_fl = cf;
		}
	}

	((state, pos, pos_begin, cur_fl), data)
}

fn begin_op(strobe: Strobe, flags: u8, more: bool) -> Strobe {
	let (mut state, mut pos, mut pos_begin, mut cur_fl) = strobe;
	let mut ret = (state, pos, pos_begin, cur_fl);

	if !more {
		let old_begin = pos_begin;

		pos_begin = pos + 1u8;
		cur_fl = flags;

		let mut data = Seq::<U8>::new(2);
		data[0usize] = U8(old_begin);
		data[1usize] = U8(flags);

		let (s, p, pb, cf) = absorb((state, pos, pos_begin, cur_fl), data);
		state = s;
		pos = p;
		pos_begin = pb;
		cur_fl = cf;

		// Force running F if C or K is set
		let force_f = 0u8 != (flags & (FLAG_C | FLAG_K));

		if force_f && pos != 0u8 {
			ret = run_f((state, pos, pos_begin, cur_fl))
		}
		else {
			ret = (state, pos, pos_begin, cur_fl)
		}
	}

	ret
}

// === External Functions === //

pub fn new_strobe(protocol_label: Seq<U8>) -> Strobe {
	let mut st = StateU8::new();

	st = st.set_chunk(6,0,&byte_seq!(1u8, 168u8, 1u8, 0u8, 1u8, 96u8));
	// b"STROBEv1.0.2"
	st = st.set_chunk(6,1,&byte_seq!(83u8,  84u8, 82u8, 79u8, 66u8, 69u8));
	st = st.set_chunk(6,2,&byte_seq!(118u8, 49u8, 46u8, 48u8, 46u8, 50u8));

	let st_U64 = transmute_state_to_u64(st);
	st = transmute_state_to_u8(keccakf1600(st_U64));

	meta_ad((st, 0u8, 0u8, 0u8), protocol_label, false)
}

pub fn meta_ad(mut strobe: Strobe, data: Seq<U8>, more: bool) -> Strobe {
	strobe = begin_op(strobe, FLAG_M | FLAG_A, more);
	absorb(strobe, data)
}

pub fn ad(mut strobe: Strobe, data: Seq<U8>, more: bool) -> Strobe {
	strobe = begin_op(strobe, FLAG_A, more);
	absorb(strobe, data)
}

pub fn prf(mut strobe: Strobe, data: Seq<U8>, more: bool) -> (Strobe, Seq<U8>) {
	strobe = begin_op(strobe, FLAG_I | FLAG_A | FLAG_C, more);
	squeeze(strobe, data)
}
