(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Require Import Hacspec_Rsa_Pkcs1.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  one_v.

Definition vrf_mgf1
  (n_2644 : rsa_int_t)
  (alpha_2645 : byte_seq)
  : byte_seq_result_t :=
  bind (i2osp (rsa_int_from_literal (@cast _ uint128 _ (byte_size_v))) (
      @repr WORDSIZE32 4)) (fun mgf_salt1_2646 => bind (i2osp (n_2644) (
        byte_size_v)) (fun mgf_salt2_2647 => let mgf_salt_2648 : seq uint8 :=
        seq_concat (mgf_salt1_2646) (mgf_salt2_2647) in 
      let mgf_string_2649 : seq uint8 :=
        seq_concat (seq_concat (array_concat (suite_string_v) (
              array_to_seq (one_v))) (mgf_salt_2648)) (alpha_2645) in 
      bind (mgf1 (mgf_string_2649) ((@cast _ uint32 _ (byte_size_v)) - (
            usize 1))) (fun mgf_2650 => @Ok seq uint8 error_t (mgf_2650)))).

Definition prove (sk_2651 : sk_t) (alpha_2652 : byte_seq) : byte_seq_result_t :=
  let '(n_2653, d_2654) :=
    (sk_2651) in 
  bind (vrf_mgf1 (n_2653) (alpha_2652)) (fun em_2655 =>
    let m_2656 : rsa_int_t :=
      os2ip (em_2655) in 
    bind (rsasp1 (sk_2651) (m_2656)) (fun s_2657 => i2osp (s_2657) (
        byte_size_v))).

Definition proof_to_hash (pi_string_2658 : byte_seq) : byte_seq_result_t :=
  let hash_string_2659 : seq uint8 :=
    array_concat (suite_string_v) (array_concat (two_v) (pi_string_2658)) in 
  @Ok seq uint8 error_t (array_slice (sha256 (hash_string_2659)) (usize 0) (
      usize 32)).

Definition verify
  (pk_2660 : pk_t)
  (alpha_2661 : byte_seq)
  (pi_string_2662 : byte_seq)
  : byte_seq_result_t :=
  let '(n_2663, e_2664) :=
    (pk_2660) in 
  let s_2665 : rsa_int_t :=
    os2ip (pi_string_2662) in 
  bind (rsavp1 (pk_2660) (s_2665)) (fun m_2666 => bind (vrf_mgf1 (n_2663) (
        alpha_2661)) (fun em_prime_2667 => let m_prime_2668 : rsa_int_t :=
        os2ip (em_prime_2667) in 
      (if ((m_2666) =.? (m_prime_2668)):bool then (proof_to_hash (
            pi_string_2662)) else (@Err seq uint8 error_t (
            VerificationFailed))))).

