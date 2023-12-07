(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Chacha20.

Require Import Hacspec_Poly1305.

Inductive error_t :=
| InvalidTag : error_t.

Notation "'cha_cha_poly_key_t'" := (cha_cha_key_t) : hacspec_scope.

Notation "'cha_cha_poly_iv_t'" := (cha_cha_iv_t) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Definition init
  (key_408 : cha_cha_poly_key_t)
  (iv_409 : cha_cha_poly_iv_t)
  : poly_state_t :=
  let key_block0_410 : block_t :=
    chacha20_key_block0 (key_408) (iv_409) in 
  let poly_key_411 : poly_key_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (key_block0_410)) (
      usize 0) (usize 32) in 
  poly1305_init (poly_key_411).

Definition poly1305_update_padded
  (m_412 : byte_seq)
  (st_413 : poly_state_t)
  : poly_state_t :=
  let st_414 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_blocks (m_412) (st_413) in 
  let last_415 : seq uint8 :=
    seq_get_remainder_chunk (m_412) (usize 16) in 
  poly1305_update_last (usize 16) (last_415) (st_414).

Definition finish
  (aad_len_416 : uint_size)
  (cipher_len_417 : uint_size)
  (st_418 : poly_state_t)
  : poly1305_tag_t :=
  let last_block_419 : poly_block_t :=
    array_new_ (default : uint8) (16) in 
  let last_block_419 :=
    array_update (last_block_419) (usize 0) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (aad_len_416)) : int64))) in 
  let last_block_419 :=
    array_update (last_block_419) (usize 8) (array_to_seq (uint64_to_le_bytes (
        secret (pub_u64 (cipher_len_417)) : int64))) in 
  let st_420 : (field_element_t '× field_element_t '× poly_key_t) :=
    poly1305_update_block (last_block_419) (st_418) in 
  poly1305_finish (st_420).

Definition chacha20_poly1305_encrypt
  (key_421 : cha_cha_poly_key_t)
  (iv_422 : cha_cha_poly_iv_t)
  (aad_423 : byte_seq)
  (msg_424 : byte_seq)
  : (byte_seq '× poly1305_tag_t) :=
  let cipher_text_425 : seq uint8 :=
    chacha20 (key_421) (iv_422) (@repr WORDSIZE32 1) (msg_424) in 
  let poly_st_426 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_421) (iv_422) in 
  let poly_st_426 :=
    poly1305_update_padded (aad_423) (poly_st_426) in 
  let poly_st_426 :=
    poly1305_update_padded (cipher_text_425) (poly_st_426) in 
  let tag_427 : poly1305_tag_t :=
    finish (seq_len (aad_423)) (seq_len (cipher_text_425)) (poly_st_426) in 
  (cipher_text_425, tag_427).

Definition chacha20_poly1305_decrypt
  (key_428 : cha_cha_poly_key_t)
  (iv_429 : cha_cha_poly_iv_t)
  (aad_430 : byte_seq)
  (cipher_text_431 : byte_seq)
  (tag_432 : poly1305_tag_t)
  : byte_seq_result_t :=
  let poly_st_433 : (field_element_t '× field_element_t '× poly_key_t) :=
    init (key_428) (iv_429) in 
  let poly_st_433 :=
    poly1305_update_padded (aad_430) (poly_st_433) in 
  let poly_st_433 :=
    poly1305_update_padded (cipher_text_431) (poly_st_433) in 
  let my_tag_434 : poly1305_tag_t :=
    finish (seq_len (aad_430)) (seq_len (cipher_text_431)) (poly_st_433) in 
  (if (array_declassify_eq (my_tag_434) (tag_432)):bool then (
      @Ok byte_seq error_t (chacha20 (key_428) (iv_429) (@repr WORDSIZE32 1) (
          cipher_text_431))) else (@Err byte_seq error_t (InvalidTag))).

