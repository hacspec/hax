module Hacspec_chacha20.Edited

open FStar.Mul
open Hacspec.Lib

type state_t = lseq (uint32) (16)

let state_idx =
  nat_mod (16)

type constants_t = lseq (uint32) (4)

let constants_idx =
  nat_mod (4)

type block_t = lseq (uint8) (64)

type chaChaIV_t = lseq (uint8) (12)

type chaChaKey_t = lseq (uint8) (32)

let x = 3l

class from_seq_tc (t: Type) = {
  inner: Type;
  size: nat;
  from_seq: s:seq inner{seq_len s = size} -> t
}

instance _: from_seq_tc state_t = {
  inner = uint32;
  size = 16;
  from_seq = array_from_seq 16
}

instance _: from_seq_tc block_t = {
  inner = uint8;
  size = 64;
  from_seq = array_from_seq 64
}

let to_le_bytes (#int_ty: inttype{unsigned int_ty /\ int_ty <> U1})
  (#len: uint_size{
    range (len * (match int_ty with U8 -> 1 | U16 -> 2  | U32 -> 4 | U64 -> 8 | U128 -> 16)) U32
  })
  = array_to_le_bytes #int_ty #len

let to_le_U32s = array_to_le_uint32s

class array_assign (o: Type0) = {
  key: Type0;
  value: Type0;
  (.[]<-): o -> key -> value -> o
}

instance array_upd1: array_assign state_t = {
  key = state_idx;
  value = uint32;
  (.[]<-) = array_upd
}

instance array_upd2: array_assign constants_t = {
  key = constants_idx;
  value = uint32;
  (.[]<-) = array_upd
}
class has_default (o: Type) = {new_: o}
instance _: has_default state_t = {new_ = array_new_ (Hacspec_lib.secret 0x0ul) 16}
instance _: has_default constants_t = {new_ = array_new_ (Hacspec_lib.secret 0x0ul) 4}
instance _: has_default block_t = {new_ = array_new_ (Hacspec_lib.secret (pub_u8 0x0)) 64}

class xor (t: Type) = { (^.): t -> t -> t }
instance xor_inherit t l: xor (int_t t l) = { (^.) = logxor }
instance xor_lseq (len: uint_size) (t:Type) {| xor t |}: xor (lseq t len) 
  = { (^.) = array_xor (^.) }

class add (t: Type) = { (+.): t -> t -> t }

instance _: add int = { (+.) = (+) }
instance add_inherit (t:inttype{unsigned t}) l: add (int_t t l) = { (+.) = add_mod }
instance add_lseq (len: uint_size) (t:Type) {| add t |}: add (lseq t len) 
  = { (+.) = array_add (+.) }


let chacha20_line (a b d: state_idx) (s: pos {s < 32}) (m: state_t) : state_t =
  let state:state_t = m in
  let state:state_t = state.[ a ] <- state.[ a ] +. state.[ b ] in
  let state:state_t = state.[ d ] <- state.[ d ] ^. state.[ a ] in
  state.[ d ] <- Secret_integers.rotate_left state.[ d ] s

let chacha20_quarter_round (a b c d: state_idx) (state: state_t) : state_t =
  let state:state_t = chacha20_line a b d 16 state in
  let state:state_t = chacha20_line c d b 12 state in
  let state:state_t = chacha20_line a b d 8 state in
  chacha20_line c d b 7 state

let chacha20_double_round (state: state_t) : state_t =
  let state:state_t = chacha20_quarter_round 0 4 8 12 state in
  let state:state_t = chacha20_quarter_round 1 5 9 13 state in
  let state:state_t = chacha20_quarter_round 2 6 10 14 state in
  let state:state_t = chacha20_quarter_round 3 7 11 15 state in
  let state:state_t = chacha20_quarter_round 0 5 10 15 state in
  let state:state_t = chacha20_quarter_round 1 6 11 12 state in
  let state:state_t = chacha20_quarter_round 2 7 8 13 state in
  chacha20_quarter_round 3 4 9 14 state

let chacha20_rounds (state: state_t) : state_t =
  let st:state_t = state in
  let st =
    foldi 0 10 (fun _i (st: state_t) -> chacha20_double_round st) st
  in
  st


let chacha20_core (ctr: Hacspec_lib.secret_t) (st0: state_t) : state_t =
  let state:state_t = st0 in
  let state:state_t = state.[ 12 ] <- state.[ 12 ] +. ctr in
  let k:state_t = chacha20_rounds state in
  k +. state

let chacha20_constants_init: constants_t =
  let constants:constants_t = new_ in
  let constants:constants_t = constants.[ 0 ] <- Hacspec_lib.secret 1634760805ul in
  let constants:constants_t = constants.[ 1 ] <- Hacspec_lib.secret 857760878ul in
  let constants:constants_t = constants.[ 2 ] <- Hacspec_lib.secret 2036477234ul in
  constants.[ 3 ] <- Hacspec_lib.secret 1797285236ul



let chacha20_init (key: chaChaKey_t) (iv: chaChaIV_t) (ctr: Hacspec_lib.secret_t) : state_t =
  let st:state_t = new_ in
  let st:state_t = Hacspec_lib.update st 0 chacha20_constants_init in
  let st:state_t = Hacspec_lib.update st 4 (to_le_U32s key) in
  let st:state_t = st.[ 12 ] <- ctr in
  Hacspec_lib.update st 13 (to_le_U32s iv)

let chacha20_key_block (state: state_t) : block_t =
  let state:state_t = chacha20_core (Hacspec_lib.secret 0ul) state in
  from_seq (to_le_bytes state)

let chacha20_key_block0 (key: chaChaKey_t) (iv: chaChaIV_t) : block_t =
  let state:state_t = chacha20_init key iv (Hacspec_lib.secret 0ul) in
  chacha20_key_block state

let chacha20_encrypt_block (st0: state_t) (ctr: Hacspec_lib.secret_t) (plain: block_t) : block_t =
  let st:state_t = chacha20_core ctr st0 in
  let pl:state_t = from_seq (to_le_U32s plain) in
  let st:state_t = pl ^. st in
  from_seq (to_le_bytes st)

let chacha20_encrypt_last
      (st0: state_t)
      (ctr: Hacspec_lib.secret_t)
      (plain: Hacspec_lib.seq_t Secret_integers.u8_t {seq_len plain < 64})
    : Hacspec_lib.seq_t Secret_integers.u8_t =
  let b:block_t = new_ in
  let b:block_t = Hacspec_lib.update b 0 plain in
  let b:block_t = chacha20_encrypt_block st0 ctr b in
  array_slice b 0 (Hacspec_lib.len plain)

#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"

let chacha20_update (st0: state_t) (m: Hacspec_lib.seq_t Secret_integers.u8_t): Hacspec_lib.seq_t Secret_integers.u8_t =
  let blocks_out = seq_new_ (Hacspec_lib.secret (pub_u8 0x0)) (seq_len m) in
  let n_blocks: uint_size = seq_num_exact_chunks m 64 in
  let blocks_out = // : lseq uint8 (seq_len m) =
    foldi 0
      n_blocks
      (fun i blocks_out ->
          let msg_block: seq uint8 =
            seq_get_exact_chunk m 64 i
          in
          let b:block_t = chacha20_encrypt_block st0 (Hacspec_lib.secret (pub_u32 i)) (from_seq msg_block) in
          seq_set_exact_chunk blocks_out 64 i b)
      blocks_out
  in
  let last_block:Hacspec_lib.seq_t Secret_integers.u8_t = seq_get_remainder_chunk m 64 in
  let blocks_out =
    if seq_len last_block <> 0
    then
      let b:Hacspec_lib.seq_t Secret_integers.u8_t =
        chacha20_encrypt_last st0 (Hacspec_lib.secret (pub_u32 n_blocks)) last_block
      in
      seq_set_chunk blocks_out 64 n_blocks b
    else blocks_out
  in
  blocks_out

let chacha20
      (key: chaChaKey_t)
      (iv: chaChaIV_t)
      (ctr: pub_uint32)
      (m: Hacspec_lib.seq_t Secret_integers.u8_t)
    : Hacspec_lib.seq_t Secret_integers.u8_t =
  let state:state_t = chacha20_init key iv (Hacspec_lib.secret ctr) in
  chacha20_update state m

