(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Hmac.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition hash_len_v : uint_size :=
  (usize 256) / (usize 8).

Inductive hkdf_error_t :=
| InvalidOutputLength : hkdf_error_t.

Notation "'hkdf_byte_seq_result_t'" := ((
  result byte_seq hkdf_error_t)) : hacspec_scope.

Definition extract (salt_713 : byte_seq) (ikm_714 : byte_seq) : prk_t :=
  let salt_or_zero_715 : seq uint8 :=
    seq_new_ (default) (hash_len_v) in 
  let '(salt_or_zero_715) :=
    if (seq_len (salt_713)) >.? (usize 0):bool then (let salt_or_zero_715 :=
        seq_from_seq (salt_713) in 
      (salt_or_zero_715)) else ((salt_or_zero_715)) in 
  array_from_seq (_) (array_to_seq (hmac (salt_or_zero_715) (ikm_714))).

Definition build_hmac_txt
  (t_716 : byte_seq)
  (info_717 : byte_seq)
  (iteration_718 : uint8)
  : byte_seq :=
  let out_719 : seq uint8 :=
    seq_new_ (default) (((seq_len (t_716)) + (seq_len (info_717))) + (
        usize 1)) in 
  let out_719 :=
    seq_update (out_719) (usize 0) (t_716) in 
  let out_719 :=
    seq_update (out_719) (seq_len (t_716)) (info_717) in 
  let out_719 :=
    seq_upd out_719 ((seq_len (t_716)) + (seq_len (info_717))) (
      iteration_718) in 
  out_719.

Definition div_ceil (a_720 : uint_size) (b_721 : uint_size) : uint_size :=
  let q_722 : uint_size :=
    (a_720) / (b_721) in 
  let '(q_722) :=
    if ((a_720) %% (b_721)) !=.? (usize 0):bool then (let q_722 :=
        (q_722) + (usize 1) in 
      (q_722)) else ((q_722)) in 
  q_722.

Definition check_output_limit
  (l_723 : uint_size)
  : (result uint_size hkdf_error_t) :=
  let n_724 : uint_size :=
    div_ceil (l_723) (hash_len_v) in 
  (if ((n_724) <=.? (usize 255)):bool then (@Ok uint_size hkdf_error_t (
        n_724)) else (@Err uint_size hkdf_error_t (InvalidOutputLength))).

Definition expand
  (prk_725 : byte_seq)
  (info_726 : byte_seq)
  (l_727 : uint_size)
  : hkdf_byte_seq_result_t :=
  bind (check_output_limit (l_727)) (fun n_728 => let t_i_729 : prk_t :=
      array_new_ (default) (_) in 
    let t_730 : seq uint8 :=
      seq_new_ (default) ((n_728) * (hash_size_v)) in 
    let '(t_i_729, t_730) :=
      foldi (usize 0) (n_728) (fun i_731 '(t_i_729, t_730) =>
        let hmac_txt_in_732 : seq uint8 :=
          (if ((i_731) =.? (usize 0)):bool then (build_hmac_txt (seq_new_ (
                  default) (usize 0)) (info_726) (secret ((pub_u8 (i_731)) .+ (
                    @repr WORDSIZE8 1)) : int8)) else (build_hmac_txt (
                seq_from_seq (array_to_seq (t_i_729))) (info_726) (secret ((
                    pub_u8 (i_731)) .+ (@repr WORDSIZE8 1)) : int8))) in 
        let t_i_729 :=
          hmac (prk_725) (hmac_txt_in_732) in 
        let t_730 :=
          seq_update (t_730) ((i_731) * (array_len (t_i_729))) (
            array_to_seq (t_i_729)) in 
        (t_i_729, t_730))
      (t_i_729, t_730) in 
    @Ok byte_seq hkdf_error_t (seq_slice (t_730) (usize 0) (l_727))).

