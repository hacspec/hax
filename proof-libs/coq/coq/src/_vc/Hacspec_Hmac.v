(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition block_len_v : uint_size :=
  k_size_v.

Definition prk_t := nseq (uint8) (hash_size_v).

Definition block_t := nseq (uint8) (block_len_v).

Definition i_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8;
        secret (@repr WORDSIZE8 54) : int8
      ] in  l).

Definition o_pad_v : block_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 92) : int8
      ] in  l).

Definition k_block (k_733 : byte_seq) : block_t :=
  (if ((seq_len (k_733)) >.? (block_len_v)):bool then (array_update_start (
        array_new_ (default) (block_len_v)) (array_to_seq (hash (
          k_733)))) else (array_update_start (array_new_ (default) (
          block_len_v)) (k_733))).

Definition hmac (k_734 : byte_seq) (txt_735 : byte_seq) : prk_t :=
  let k_block_736 : block_t :=
    k_block (k_734) in 
  let h_in_737 : seq uint8 :=
    seq_from_seq (array_to_seq ((k_block_736) array_xor (i_pad_v))) in 
  let h_in_737 :=
    seq_concat (h_in_737) (txt_735) in 
  let h_inner_738 : sha256_digest_t :=
    hash (h_in_737) in 
  let h_in_739 : seq uint8 :=
    seq_from_seq (array_to_seq ((k_block_736) array_xor (o_pad_v))) in 
  let h_in_739 :=
    seq_concat (h_in_739) (array_to_seq (h_inner_738)) in 
  array_from_seq (hash_size_v) (array_to_seq (hash (h_in_739))).

