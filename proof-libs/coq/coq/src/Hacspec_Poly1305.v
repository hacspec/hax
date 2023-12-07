(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition poly_key_t := nseq (uint8) (usize 32).

Definition blocksize_v : uint_size :=
  usize 16.

Definition poly_block_t := nseq (uint8) (usize 16).

Definition poly1305_tag_t := nseq (uint8) (usize 16).

Notation "'sub_block_t'" := (byte_seq) : hacspec_scope.

Notation "'block_index_t'" := (uint_size) : hacspec_scope.

Definition field_canvas_t := nseq (int8) (17).
Definition field_element_t := nat_mod 0x03fffffffffffffffffffffffffffffffb.

Notation "'poly_state_t'" := ((
  field_element_t '×
  field_element_t '×
  poly_key_t
)) : hacspec_scope.

Definition poly1305_encode_r (b_435 : poly_block_t) : field_element_t :=
  let n_436 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_435))) in 
  let n_436 :=
    (n_436) .& (secret (
        @repr WORDSIZE128 21267647620597763993911028882763415551) : int128) in 
  nat_mod_from_secret_literal (n_436).

Definition poly1305_encode_block (b_437 : poly_block_t) : field_element_t :=
  let n_438 : uint128 :=
    uint128_from_le_bytes (array_from_seq (16) (array_to_seq (b_437))) in 
  let f_439 : field_element_t :=
    nat_mod_from_secret_literal (n_438) in 
  (f_439) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) (
      usize 128) : field_element_t).

Definition poly1305_encode_last
  (pad_len_440 : block_index_t)
  (b_441 : sub_block_t)
  : field_element_t :=
  let n_442 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (b_441) (
        usize 0) (seq_len (b_441))) in 
  let f_443 : field_element_t :=
    nat_mod_from_secret_literal (n_442) in 
  (f_443) +% (nat_mod_pow2 (0x03fffffffffffffffffffffffffffffffb) ((usize 8) * (
        pad_len_440)) : field_element_t).

Definition poly1305_init (k_444 : poly_key_t) : poly_state_t :=
  let r_445 : field_element_t :=
    poly1305_encode_r (array_from_slice (default : uint8) (16) (
        array_to_seq (k_444)) (usize 0) (usize 16)) in 
  (nat_mod_zero , r_445, k_444).

Definition poly1305_update_block
  (b_446 : poly_block_t)
  (st_447 : poly_state_t)
  : poly_state_t :=
  let '(acc_448, r_449, k_450) :=
    st_447 in 
  (((poly1305_encode_block (b_446)) +% (acc_448)) *% (r_449), r_449, k_450).

Definition poly1305_update_blocks
  (m_451 : byte_seq)
  (st_452 : poly_state_t)
  : poly_state_t :=
  let st_453 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_452 in 
  let n_blocks_454 : uint_size :=
    (seq_len (m_451)) / (blocksize_v) in 
  let st_453 :=
    foldi (usize 0) (n_blocks_454) (fun i_455 st_453 =>
      let block_456 : poly_block_t :=
        array_from_seq (16) (seq_get_exact_chunk (m_451) (blocksize_v) (
            i_455)) in 
      let st_453 :=
        poly1305_update_block (block_456) (st_453) in 
      (st_453))
    st_453 in 
  st_453.

Definition poly1305_update_last
  (pad_len_457 : uint_size)
  (b_458 : sub_block_t)
  (st_459 : poly_state_t)
  : poly_state_t :=
  let st_460 : (field_element_t '× field_element_t '× poly_key_t) :=
    st_459 in 
  let '(st_460) :=
    if (seq_len (b_458)) !=.? (usize 0):bool then (let '(acc_461, r_462, k_463
        ) :=
        st_460 in 
      let st_460 :=
        (
          ((poly1305_encode_last (pad_len_457) (b_458)) +% (acc_461)) *% (
            r_462),
          r_462,
          k_463
        ) in 
      (st_460)) else ((st_460)) in 
  st_460.

Definition poly1305_update
  (m_464 : byte_seq)
  (st_465 : poly_state_t)
  : poly_state_t :=
  let st_466 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_464) (st_465) in 
  let last_467 : seq uint8 :=
    seq_get_remainder_chunk (m_464) (blocksize_v) in 
  poly1305_update_last (seq_len (last_467)) (last_467) (st_466).

Definition poly1305_finish (st_468 : poly_state_t) : poly1305_tag_t :=
  let '(acc_469, _, k_470) :=
    st_468 in 
  let n_471 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (
        array_to_seq (k_470)) (usize 16) (usize 16)) in 
  let aby_472 : seq uint8 :=
    nat_mod_to_byte_seq_le (acc_469) in 
  let a_473 : uint128 :=
    uint128_from_le_bytes (array_from_slice (default : uint8) (16) (aby_472) (
        usize 0) (usize 16)) in 
  array_from_seq (16) (array_to_seq (uint128_to_le_bytes ((a_473) .+ (n_471)))).

Definition poly1305
  (m_474 : byte_seq)
  (key_475 : poly_key_t)
  : poly1305_tag_t :=
  let st_476 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_init (key_475) in 
  let st_476 :=
    poly1305_update (m_474) (st_476) in 
  poly1305_finish (st_476).

