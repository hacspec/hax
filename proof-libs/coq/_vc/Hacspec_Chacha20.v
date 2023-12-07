(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition state_t := nseq (uint32) (usize 16).

Definition state_idx_t :=
  nat_mod (usize 16).
Definition uint_size_in_state_idx_t(n : uint_size) : state_idx_t := int_in_nat_mod n.
Coercion uint_size_in_state_idx_t : uint_size >-> state_idx_t.

Definition constants_t := nseq (uint32) (usize 4).

Definition constants_idx_t :=
  nat_mod (usize 4).
Definition uint_size_in_constants_idx_t(n : uint_size) : constants_idx_t := int_in_nat_mod n.
Coercion uint_size_in_constants_idx_t : uint_size >-> constants_idx_t.

Definition block_t := nseq (uint8) (usize 64).

Definition cha_cha_iv_t := nseq (uint8) (usize 12).

Definition cha_cha_key_t := nseq (uint8) (usize 32).

Definition chacha20_line
  (a_345 : state_idx_t)
  (b_346 : state_idx_t)
  (d_347 : state_idx_t)
  (s_348 : uint_size)
  (m_349 : state_t)
  : state_t :=
  let state_350 : state_t :=
    m_349 in 
  let state_350 :=
    array_upd state_350 (a_345) ((array_index (state_350) (a_345)) .+ (
        array_index (state_350) (b_346))) in 
  let state_350 :=
    array_upd state_350 (d_347) ((array_index (state_350) (d_347)) .^ (
        array_index (state_350) (a_345))) in 
  let state_350 :=
    array_upd state_350 (d_347) (uint32_rotate_left (array_index (state_350) (
          d_347)) (s_348)) in 
  state_350.

Definition chacha20_quarter_round
  (a_351 : state_idx_t)
  (b_352 : state_idx_t)
  (c_353 : state_idx_t)
  (d_354 : state_idx_t)
  (state_355 : state_t)
  : state_t :=
  let state_356 : state_t :=
    chacha20_line (a_351) (b_352) (d_354) (usize 16) (state_355) in 
  let state_357 : state_t :=
    chacha20_line (c_353) (d_354) (b_352) (usize 12) (state_356) in 
  let state_358 : state_t :=
    chacha20_line (a_351) (b_352) (d_354) (usize 8) (state_357) in 
  chacha20_line (c_353) (d_354) (b_352) (usize 7) (state_358).

Definition chacha20_double_round (state_359 : state_t) : state_t :=
  let state_360 : state_t :=
    chacha20_quarter_round (usize 0) (usize 4) (usize 8) (usize 12) (
      state_359) in 
  let state_361 : state_t :=
    chacha20_quarter_round (usize 1) (usize 5) (usize 9) (usize 13) (
      state_360) in 
  let state_362 : state_t :=
    chacha20_quarter_round (usize 2) (usize 6) (usize 10) (usize 14) (
      state_361) in 
  let state_363 : state_t :=
    chacha20_quarter_round (usize 3) (usize 7) (usize 11) (usize 15) (
      state_362) in 
  let state_364 : state_t :=
    chacha20_quarter_round (usize 0) (usize 5) (usize 10) (usize 15) (
      state_363) in 
  let state_365 : state_t :=
    chacha20_quarter_round (usize 1) (usize 6) (usize 11) (usize 12) (
      state_364) in 
  let state_366 : state_t :=
    chacha20_quarter_round (usize 2) (usize 7) (usize 8) (usize 13) (
      state_365) in 
  chacha20_quarter_round (usize 3) (usize 4) (usize 9) (usize 14) (state_366).

Definition chacha20_rounds (state_367 : state_t) : state_t :=
  let st_368 : state_t :=
    state_367 in 
  let st_368 :=
    foldi (usize 0) (usize 10) (fun i_369 st_368 =>
      let st_368 :=
        chacha20_double_round (st_368) in 
      (st_368))
    st_368 in 
  st_368.

Definition chacha20_core (ctr_370 : uint32) (st0_371 : state_t) : state_t :=
  let state_372 : state_t :=
    st0_371 in 
  let state_372 :=
    array_upd state_372 (usize 12) ((array_index (state_372) (usize 12)) .+ (
        ctr_370)) in 
  let k_373 : state_t :=
    chacha20_rounds (state_372) in 
  (k_373) array_add (state_372).

Definition chacha20_constants_init  : constants_t :=
  let constants_374 : constants_t :=
    array_new_ (default : uint32) (4) in 
  let constants_374 :=
    array_upd constants_374 (usize 0) (secret (
        @repr WORDSIZE32 1634760805) : int32) in 
  let constants_374 :=
    array_upd constants_374 (usize 1) (secret (
        @repr WORDSIZE32 857760878) : int32) in 
  let constants_374 :=
    array_upd constants_374 (usize 2) (secret (
        @repr WORDSIZE32 2036477234) : int32) in 
  let constants_374 :=
    array_upd constants_374 (usize 3) (secret (
        @repr WORDSIZE32 1797285236) : int32) in 
  constants_374.

Definition chacha20_init
  (key_375 : cha_cha_key_t)
  (iv_376 : cha_cha_iv_t)
  (ctr_377 : uint32)
  : state_t :=
  let st_378 : state_t :=
    array_new_ (default : uint32) (16) in 
  let st_378 :=
    array_update (st_378) (usize 0) (
      array_to_seq (chacha20_constants_init )) in 
  let st_378 :=
    array_update (st_378) (usize 4) (array_to_le_uint32s (key_375)) in 
  let st_378 :=
    array_upd st_378 (usize 12) (ctr_377) in 
  let st_378 :=
    array_update (st_378) (usize 13) (array_to_le_uint32s (iv_376)) in 
  st_378.

Definition chacha20_key_block (state_379 : state_t) : block_t :=
  let state_380 : state_t :=
    chacha20_core (secret (@repr WORDSIZE32 0) : int32) (state_379) in 
  array_from_seq (64) (array_to_le_bytes (state_380)).

Definition chacha20_key_block0
  (key_381 : cha_cha_key_t)
  (iv_382 : cha_cha_iv_t)
  : block_t :=
  let state_383 : state_t :=
    chacha20_init (key_381) (iv_382) (secret (@repr WORDSIZE32 0) : int32) in 
  chacha20_key_block (state_383).

Definition chacha20_encrypt_block
  (st0_384 : state_t)
  (ctr_385 : uint32)
  (plain_386 : block_t)
  : block_t :=
  let st_387 : state_t :=
    chacha20_core (ctr_385) (st0_384) in 
  let pl_388 : state_t :=
    array_from_seq (16) (array_to_le_uint32s (plain_386)) in 
  let st_389 : state_t :=
    (pl_388) array_xor (st_387) in 
  array_from_seq (64) (array_to_le_bytes (st_389)).

Definition chacha20_encrypt_last
  (st0_390 : state_t)
  (ctr_391 : uint32)
  (plain_392 : byte_seq)
  : byte_seq :=
  let b_393 : block_t :=
    array_new_ (default : uint8) (64) in 
  let b_393 :=
    array_update (b_393) (usize 0) (plain_392) in 
  let b_393 :=
    chacha20_encrypt_block (st0_390) (ctr_391) (b_393) in 
  array_slice (b_393) (usize 0) (seq_len (plain_392)).

Definition chacha20_update (st0_394 : state_t) (m_395 : byte_seq) : byte_seq :=
  let blocks_out_396 : seq uint8 :=
    seq_new_ (default : uint8) (seq_len (m_395)) in 
  let n_blocks_397 : uint_size :=
    seq_num_exact_chunks (m_395) (usize 64) in 
  let blocks_out_396 :=
    foldi (usize 0) (n_blocks_397) (fun i_398 blocks_out_396 =>
      let msg_block_399 : seq uint8 :=
        seq_get_exact_chunk (m_395) (usize 64) (i_398) in 
      let b_400 : block_t :=
        chacha20_encrypt_block (st0_394) (secret (pub_u32 (i_398)) : int32) (
          array_from_seq (64) (msg_block_399)) in 
      let blocks_out_396 :=
        seq_set_exact_chunk (blocks_out_396) (usize 64) (i_398) (
          array_to_seq (b_400)) in 
      (blocks_out_396))
    blocks_out_396 in 
  let last_block_401 : seq uint8 :=
    seq_get_remainder_chunk (m_395) (usize 64) in 
  let '(blocks_out_396) :=
    if (seq_len (last_block_401)) !=.? (usize 0):bool then (
      let b_402 : seq uint8 :=
        chacha20_encrypt_last (st0_394) (secret (pub_u32 (
              n_blocks_397)) : int32) (last_block_401) in 
      let blocks_out_396 :=
        seq_set_chunk (blocks_out_396) (usize 64) (n_blocks_397) (b_402) in 
      (blocks_out_396)) else ((blocks_out_396)) in 
  blocks_out_396.

Definition chacha20
  (key_403 : cha_cha_key_t)
  (iv_404 : cha_cha_iv_t)
  (ctr_405 : int32)
  (m_406 : byte_seq)
  : byte_seq :=
  let state_407 : state_t :=
    chacha20_init (key_403) (iv_404) (secret (ctr_405) : int32) in 
  chacha20_update (state_407) (m_406).

