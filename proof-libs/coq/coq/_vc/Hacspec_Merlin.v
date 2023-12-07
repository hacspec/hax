(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Strobe.

Notation "'transcript_t'" := (strobe_t) : hacspec_scope.

Definition merlin_protocol_label  : seq uint8 :=
  [
    secret (@repr WORDSIZE8 77) : int8;
    secret (@repr WORDSIZE8 101) : int8;
    secret (@repr WORDSIZE8 114) : int8;
    secret (@repr WORDSIZE8 108) : int8;
    secret (@repr WORDSIZE8 105) : int8;
    secret (@repr WORDSIZE8 110) : int8;
    secret (@repr WORDSIZE8 32) : int8;
    secret (@repr WORDSIZE8 118) : int8;
    secret (@repr WORDSIZE8 49) : int8;
    secret (@repr WORDSIZE8 46) : int8;
    secret (@repr WORDSIZE8 48) : int8
  ].

Definition encode_uint64 (x_1051 : uint64) : seq uint8 :=
  array_to_le_bytes (uint64_to_le_bytes (x_1051)).

Definition encode_usize_as_u32 (x_1052 : uint_size) : seq uint8 :=
  let x_uint32_1053 : uint32 :=
    uint32_classify (pub_u32 (x_1052)) in 
  array_to_le_bytes (uint32_to_le_bytes (x_uint32_1053)).

Definition new_ (label_1054 : seq uint8) : transcript_t :=
  let transcript_1055 : (state_uint8_t '× int8 '× int8 '× int8) :=
    new_strobe (merlin_protocol_label ) in 
  let dom_sep_1056 : seq uint8 :=
    [
      secret (@repr WORDSIZE8 100) : int8;
      secret (@repr WORDSIZE8 111) : int8;
      secret (@repr WORDSIZE8 109) : int8;
      secret (@repr WORDSIZE8 45) : int8;
      secret (@repr WORDSIZE8 115) : int8;
      secret (@repr WORDSIZE8 101) : int8;
      secret (@repr WORDSIZE8 112) : int8
    ] in 
  append_message (transcript_1055) (dom_sep_1056) (label_1054).

Definition append_message
  (transcript_1057 : transcript_t)
  (label_1058 : seq uint8)
  (message_1059 : seq uint8)
  : transcript_t :=
  let data_len_1060 : seq uint8 :=
    array_to_be_bytes (uint32_to_le_bytes (uint32_classify (pub_u32 (seq_len (
              message_1059))))) in 
  let transcript_1057 :=
    meta_ad (transcript_1057) (label_1058) (false) in 
  let transcript_1057 :=
    meta_ad (transcript_1057) (data_len_1060) (true) in 
  let transcript_1057 :=
    ad (transcript_1057) (message_1059) (false) in 
  transcript_1057.

Definition challenge_bytes
  (transcript_1061 : transcript_t)
  (label_1062 : seq uint8)
  (dest_1063 : seq uint8)
  : (transcript_t '× seq uint8) :=
  let data_len_1064 : seq uint8 :=
    encode_usize_as_u32 (seq_len (dest_1063)) in 
  let transcript_1061 :=
    meta_ad (transcript_1061) (label_1062) (false) in 
  let transcript_1061 :=
    meta_ad (transcript_1061) (data_len_1064) (true) in 
  prf (transcript_1061) (dest_1063) (false).

Definition append_uint64
  (transcript_1065 : transcript_t)
  (label_1066 : seq uint8)
  (x_1067 : uint64)
  : transcript_t :=
  append_message (transcript_1065) (label_1066) (encode_uint64 (x_1067)).

