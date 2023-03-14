module Hacspec_chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Hacspec.Lib
open Hacspec_lib_tc

unfold
type state_t = lseq uint32 16
unfold
type state_idx_t = nat_mod 16

unfold
type constants_t = lseq uint32 4
unfold
type constants_idx_t = nat_mod 4

unfold
type block_t = lseq uint8 64

unfold
type chaChaIV_t = lseq uint8 12

unfold
type chaChaKey_t = lseq uint8 32

let chacha20_line (a b d: state_idx_t) (s: pos {s < 32}) (m: state_t) : state_t =
  let state:state_t = m in
  let state:state_t = state.[ a ] <- state.[ a ] +. state.[ b ] in
  let state:state_t = state.[ d ] <- state.[ d ] ^. state.[ a ] in
  state.[ d ] <- Secret_integers.rotate_left state.[ d ] s

let chacha20_quarter_round (a b c d: state_idx_t) (state: state_t) : state_t =
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
  Hacspec.Lib.foldi 0 10 (fun _i st -> chacha20_double_round st) st

let chacha20_core (ctr: Secret_integers.u32_t) (st0: state_t) : state_t =
  let state:state_t = st0 in
  let state:state_t = state.[ 12l ] <- state.[ 12l ] +. ctr in
  let k:state_t = chacha20_rounds state in
  k +. state

let chacha20_constants_init: constants_t =
  let constants:constants_t = new_ in
  let constants:constants_t = constants.[ 0l ] <- Hacspec_lib_tc.secret 1634760805ul in
  let constants:constants_t = constants.[ 1l ] <- Hacspec_lib_tc.secret 857760878ul in
  let constants:constants_t = constants.[ 2l ] <- Hacspec_lib_tc.secret 2036477234ul in
  constants.[ 3l ] <- Hacspec_lib_tc.secret 1797285236ul

let chacha20_init (key: chaChaKey_t) (iv: chaChaIV_t) (ctr: Secret_integers.u32_t) : state_t =
  let st:state_t = new_ in
  let st:state_t = Hacspec_lib_tc.update st 0 chacha20_constants_init in
  let st:state_t = Hacspec_lib_tc.update st 4 (to_le_U32s key) in
  let st:state_t = st.[ 12l ] <- ctr in
  Hacspec_lib_tc.update st 13 (to_le_U32s iv)

let chacha20_key_block (state: state_t) : block_t =
  let state:state_t = chacha20_core (Hacspec_lib_tc.secret 0ul) state in
  from_seq (to_le_bytes state)

let chacha20_key_block0 (key: chaChaKey_t) (iv: chaChaIV_t) : block_t =
  let state:state_t = chacha20_init key iv (Hacspec_lib_tc.secret 0ul) in
  chacha20_key_block state

let chacha20_encrypt_block (st0: state_t) (ctr: Secret_integers.u32_t) (plain: block_t) : block_t =
  let st:state_t = chacha20_core ctr st0 in
  let pl:state_t = from_seq (to_le_U32s plain) in
  let st:state_t = pl ^. st in
  from_seq (to_le_bytes st)

let chacha20_encrypt_last
      (st0: state_t)
      (ctr: Secret_integers.u32_t)
      (plain: Hacspec_lib_tc.seq_t Secret_integers.u8_t {seq_len plain < 64})
    : Hacspec_lib_tc.seq_t Secret_integers.u8_t =
  let b:block_t = new_ in
  let b:block_t = Hacspec_lib_tc.update b 0 plain in
  let b:block_t = chacha20_encrypt_block st0 ctr b in
  slice b 0 (Hacspec_lib_tc.len plain)

let chacha20_update (st0: state_t) (m: Hacspec_lib_tc.seq_t Secret_integers.u8_t)
    : Hacspec_lib_tc.seq_t Secret_integers.u8_t =
  let blocks_out =
    Hacspec_lib_tc.new_seq (Hacspec_lib_tc.len m)
  in
  let n_blocks:uint_size = Hacspec_lib_tc.num_exact_chunks m 64 in
  let blocks_out =
    Hacspec.Lib.foldi 0
      n_blocks
      (fun i blocks_out ->
          let msg_block:Hacspec_lib_tc.seq_t Secret_integers.u8_t =
            Hacspec_lib_tc.get_exact_chunk m 64 i
          in
          let b:block_t =
            chacha20_encrypt_block st0 (Hacspec_lib_tc.secret i) (from_seq msg_block)
          in
          Hacspec_lib_tc.set_exact_chunk blocks_out 64 i b)
      blocks_out
  in
  let last_block:Hacspec_lib_tc.seq_t Secret_integers.u8_t =
    Hacspec_lib_tc.get_remainder_chunk m 64
  in
  if Hacspec_lib_tc.len last_block <> 0
  then
    let b:Hacspec_lib_tc.seq_t Secret_integers.u8_t =
      chacha20_encrypt_last st0 (Hacspec_lib_tc.secret n_blocks) last_block
    in
    Hacspec_lib_tc.set_chunk blocks_out 64 n_blocks b
  else blocks_out

let chacha20
      (key: chaChaKey_t)
      (iv: chaChaIV_t)
      (ctr: UInt32.t)
      (m: Hacspec_lib_tc.seq_t Secret_integers.u8_t)
    : Hacspec_lib_tc.seq_t Secret_integers.u8_t =
  let state:state_t = chacha20_init key iv (Hacspec_lib_tc.secret ctr) in
  chacha20_update state m
