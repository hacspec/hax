(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  array_from_list int64 (let l :=
      [
        @repr WORDSIZE64 1;
        @repr WORDSIZE64 32898;
        @repr WORDSIZE64 9223372036854808714;
        @repr WORDSIZE64 9223372039002292224;
        @repr WORDSIZE64 32907;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808585;
        @repr WORDSIZE64 138;
        @repr WORDSIZE64 136;
        @repr WORDSIZE64 2147516425;
        @repr WORDSIZE64 2147483658;
        @repr WORDSIZE64 2147516555;
        @repr WORDSIZE64 9223372036854775947;
        @repr WORDSIZE64 9223372036854808713;
        @repr WORDSIZE64 9223372036854808579;
        @repr WORDSIZE64 9223372036854808578;
        @repr WORDSIZE64 9223372036854775936;
        @repr WORDSIZE64 32778;
        @repr WORDSIZE64 9223372039002259466;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808704;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292232
      ] in  l).

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 1;
        usize 62;
        usize 28;
        usize 27;
        usize 36;
        usize 44;
        usize 6;
        usize 55;
        usize 20;
        usize 3;
        usize 10;
        usize 43;
        usize 25;
        usize 39;
        usize 41;
        usize 45;
        usize 15;
        usize 21;
        usize 8;
        usize 18;
        usize 2;
        usize 61;
        usize 56;
        usize 14
      ] in  l).

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 6;
        usize 12;
        usize 18;
        usize 24;
        usize 3;
        usize 9;
        usize 10;
        usize 16;
        usize 22;
        usize 1;
        usize 7;
        usize 13;
        usize 19;
        usize 20;
        usize 4;
        usize 5;
        usize 11;
        usize 17;
        usize 23;
        usize 2;
        usize 8;
        usize 14;
        usize 15;
        usize 21
      ] in  l).

Definition theta (s_1068 : state_t) : state_t :=
  let b_1069 : row_t :=
    array_new_ (default : uint64) (5) in 
  let b_1069 :=
    foldi (usize 0) (usize 5) (fun i_1070 b_1069 =>
      let b_1069 :=
        array_upd b_1069 (i_1070) (((((array_index (s_1068) (i_1070)) .^ (
                  array_index (s_1068) ((i_1070) + (usize 5)))) .^ (
                array_index (s_1068) ((i_1070) + (usize 10)))) .^ (array_index (
                s_1068) ((i_1070) + (usize 15)))) .^ (array_index (s_1068) ((
                i_1070) + (usize 20)))) in 
      (b_1069))
    b_1069 in 
  let s_1068 :=
    foldi (usize 0) (usize 5) (fun i_1071 s_1068 =>
      let u_1072 : uint64 :=
        array_index (b_1069) (((i_1071) + (usize 1)) %% (usize 5)) in 
      let t_1073 : uint64 :=
        (array_index (b_1069) (((i_1071) + (usize 4)) %% (usize 5))) .^ (
          uint64_rotate_left (u_1072) (usize 1)) in 
      let s_1068 :=
        foldi (usize 0) (usize 5) (fun j_1074 s_1068 =>
          let s_1068 :=
            array_upd s_1068 (((usize 5) * (j_1074)) + (i_1071)) ((array_index (
                  s_1068) (((usize 5) * (j_1074)) + (i_1071))) .^ (t_1073)) in 
          (s_1068))
        s_1068 in 
      (s_1068))
    s_1068 in 
  s_1068.

Definition rho (s_1075 : state_t) : state_t :=
  let s_1075 :=
    foldi (usize 0) (usize 25) (fun i_1076 s_1075 =>
      let u_1077 : uint64 :=
        array_index (s_1075) (i_1076) in 
      let s_1075 :=
        array_upd s_1075 (i_1076) (uint64_rotate_left (u_1077) (array_index (
              rotc_v) (i_1076))) in 
      (s_1075))
    s_1075 in 
  s_1075.

Definition pi (s_1078 : state_t) : state_t :=
  let v_1079 : state_t :=
    array_new_ (default : uint64) (25) in 
  let v_1079 :=
    foldi (usize 0) (usize 25) (fun i_1080 v_1079 =>
      let v_1079 :=
        array_upd v_1079 (i_1080) (array_index (s_1078) (array_index (pi_v) (
              i_1080))) in 
      (v_1079))
    v_1079 in 
  v_1079.

Definition chi (s_1081 : state_t) : state_t :=
  let b_1082 : row_t :=
    array_new_ (default : uint64) (5) in 
  let '(s_1081, b_1082) :=
    foldi (usize 0) (usize 5) (fun i_1083 '(s_1081, b_1082) =>
      let b_1082 :=
        foldi (usize 0) (usize 5) (fun j_1084 b_1082 =>
          let b_1082 :=
            array_upd b_1082 (j_1084) (array_index (s_1081) (((usize 5) * (
                    i_1083)) + (j_1084))) in 
          (b_1082))
        b_1082 in 
      let s_1081 :=
        foldi (usize 0) (usize 5) (fun j_1085 s_1081 =>
          let u_1086 : uint64 :=
            array_index (b_1082) (((j_1085) + (usize 1)) %% (usize 5)) in 
          let s_1081 :=
            array_upd s_1081 (((usize 5) * (i_1083)) + (j_1085)) ((array_index (
                  s_1081) (((usize 5) * (i_1083)) + (j_1085))) .^ ((not (
                    u_1086)) .& (array_index (b_1082) (((j_1085) + (
                        usize 2)) %% (usize 5))))) in 
          (s_1081))
        s_1081 in 
      (s_1081, b_1082))
    (s_1081, b_1082) in 
  s_1081.

Definition iota (s_1087 : state_t) (rndconst_1088 : int64) : state_t :=
  let s_1087 :=
    array_upd s_1087 (usize 0) ((array_index (s_1087) (usize 0)) .^ (
        uint64_classify (rndconst_1088))) in 
  s_1087.

Definition keccakf1600 (s_1089 : state_t) : state_t :=
  let s_1089 :=
    foldi (usize 0) (rounds_v) (fun i_1090 s_1089 =>
      let s_1089 :=
        theta (s_1089) in 
      let s_1089 :=
        rho (s_1089) in 
      let s_1089 :=
        pi (s_1089) in 
      let s_1089 :=
        chi (s_1089) in 
      let s_1089 :=
        iota (s_1089) (array_index (roundconstants_v) (i_1090)) in 
      (s_1089))
    s_1089 in 
  s_1089.

Definition absorb_block (s_1091 : state_t) (block_1092 : byte_seq) : state_t :=
  let s_1091 :=
    foldi (usize 0) (seq_len (block_1092)) (fun i_1093 s_1091 =>
      let w_1094 : uint_size :=
        (i_1093) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1095 : uint_size :=
        (usize 8) * ((i_1093) .& (usize 7)) in 
      let s_1091 :=
        array_upd s_1091 (w_1094) ((array_index (s_1091) (w_1094)) .^ ((
              uint64_from_uint8 (seq_index (block_1092) (i_1093))) shift_left (
              o_1095))) in 
      (s_1091))
    s_1091 in 
  keccakf1600 (s_1091).

Definition squeeze
  (s_1096 : state_t)
  (nbytes_1097 : uint_size)
  (rate_1098 : uint_size)
  : byte_seq :=
  let out_1099 : seq uint8 :=
    seq_new_ (default : uint8) (nbytes_1097) in 
  let '(s_1096, out_1099) :=
    foldi (usize 0) (nbytes_1097) (fun i_1100 '(s_1096, out_1099) =>
      let pos_1101 : uint_size :=
        (i_1100) %% (rate_1098) in 
      let w_1102 : uint_size :=
        (pos_1101) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_1103 : uint_size :=
        (usize 8) * ((pos_1101) .& (usize 7)) in 
      let b_1104 : uint64 :=
        ((array_index (s_1096) (w_1102)) shift_right (o_1103)) .& (
          uint64_classify (@repr WORDSIZE64 255)) in 
      let out_1099 :=
        seq_upd out_1099 (i_1100) (uint8_from_uint64 (b_1104)) in 
      let '(s_1096) :=
        if (((i_1100) + (usize 1)) %% (rate_1098)) =.? (usize 0):bool then (
          let s_1096 :=
            keccakf1600 (s_1096) in 
          (s_1096)) else ((s_1096)) in 
      (s_1096, out_1099))
    (s_1096, out_1099) in 
  out_1099.

Definition keccak
  (rate_1105 : uint_size)
  (data_1106 : byte_seq)
  (p_1107 : int8)
  (outbytes_1108 : uint_size)
  : byte_seq :=
  let buf_1109 : seq uint8 :=
    seq_new_ (default : uint8) (rate_1105) in 
  let last_block_len_1110 : uint_size :=
    usize 0 in 
  let s_1111 : state_t :=
    array_new_ (default : uint64) (25) in 
  let '(buf_1109, last_block_len_1110, s_1111) :=
    foldi (usize 0) (seq_num_chunks (data_1106) (rate_1105)) (fun i_1112 '(
        buf_1109,
        last_block_len_1110,
        s_1111
      ) =>
      let '(block_len_1113, block_1114) :=
        seq_get_chunk (data_1106) (rate_1105) (i_1112) in 
      let '(buf_1109, last_block_len_1110, s_1111) :=
        if (block_len_1113) =.? (rate_1105):bool then (let s_1111 :=
            absorb_block (s_1111) (block_1114) in 
          (buf_1109, last_block_len_1110, s_1111)) else (let buf_1109 :=
            seq_update_start (buf_1109) (block_1114) in 
          let last_block_len_1110 :=
            block_len_1113 in 
          (buf_1109, last_block_len_1110, s_1111)) in 
      (buf_1109, last_block_len_1110, s_1111))
    (buf_1109, last_block_len_1110, s_1111) in 
  let buf_1109 :=
    seq_upd buf_1109 (last_block_len_1110) (secret (p_1107) : int8) in 
  let buf_1109 :=
    seq_upd buf_1109 ((rate_1105) - (usize 1)) ((seq_index (buf_1109) ((
            rate_1105) - (usize 1))) .| (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let s_1111 :=
    absorb_block (s_1111) (buf_1109) in 
  squeeze (s_1111) (outbytes_1108) (rate_1105).

Definition sha3224 (data_1115 : byte_seq) : digest224_t :=
  let t_1116 : seq uint8 :=
    keccak (sha3224_rate_v) (data_1115) (@repr WORDSIZE8 6) (usize 28) in 
  array_from_seq (28) (t_1116).

Definition sha3256 (data_1117 : byte_seq) : digest256_t :=
  let t_1118 : seq uint8 :=
    keccak (sha3256_rate_v) (data_1117) (@repr WORDSIZE8 6) (usize 32) in 
  array_from_seq (32) (t_1118).

Definition sha3384 (data_1119 : byte_seq) : digest384_t :=
  let t_1120 : seq uint8 :=
    keccak (sha3384_rate_v) (data_1119) (@repr WORDSIZE8 6) (usize 48) in 
  array_from_seq (48) (t_1120).

Definition sha3512 (data_1121 : byte_seq) : digest512_t :=
  let t_1122 : seq uint8 :=
    keccak (sha3512_rate_v) (data_1121) (@repr WORDSIZE8 6) (usize 64) in 
  array_from_seq (64) (t_1122).

Definition shake128
  (data_1123 : byte_seq)
  (outlen_1124 : uint_size)
  : byte_seq :=
  keccak (shake128_rate_v) (data_1123) (@repr WORDSIZE8 31) (outlen_1124).

Definition shake256
  (data_1125 : byte_seq)
  (outlen_1126 : uint_size)
  : byte_seq :=
  keccak (shake256_rate_v) (data_1125) (@repr WORDSIZE8 31) (outlen_1126).

