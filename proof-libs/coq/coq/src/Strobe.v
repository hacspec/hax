(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha3.

Definition strobe_r_v : int8 :=
  @repr WORDSIZE8 166.

Definition flag_i_v : int8 :=
  @repr WORDSIZE8 1.

Definition flag_a_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 1).

Definition flag_c_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 2).

Definition flag_m_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 4).

Definition flag_k_v : int8 :=
  (@repr WORDSIZE8 1) shift_left (usize 5).

Notation "'state_uint64_t'" := (state_t) : hacspec_scope.

Definition state_uint8_t := nseq (uint8) (usize 200).

Notation "'strobe_t'" := ((state_uint8_t '× int8 '× int8 '× int8
)) : hacspec_scope.

Definition transmute_state_to_u64
  (state_986 : state_uint8_t)
  : state_uint64_t :=
  let new_state_987 : state_t :=
    array_new_ (default : uint64) (25) in 
  let new_state_987 :=
    foldi (usize 0) (array_len (new_state_987)) (fun i_988 new_state_987 =>
      let word_989 : uint64_word_t :=
        array_new_ (default : uint8) (8) in 
      let word_989 :=
        foldi (usize 0) (array_len (word_989)) (fun j_990 word_989 =>
          let word_989 :=
            array_upd word_989 (j_990) (array_index (state_986) (((i_988) * (
                    usize 8)) + (j_990))) in 
          (word_989))
        word_989 in 
      let new_state_987 :=
        array_upd new_state_987 (i_988) (uint64_from_le_bytes (word_989)) in 
      (new_state_987))
    new_state_987 in 
  new_state_987.

Definition transmute_state_to_u8 (state_991 : state_uint64_t) : state_uint8_t :=
  let new_state_992 : state_uint8_t :=
    array_new_ (default : uint8) (200) in 
  let new_state_992 :=
    foldi (usize 0) (array_len (state_991)) (fun i_993 new_state_992 =>
      let bytes_994 : seq uint8 :=
        uint64_to_le_bytes (array_index (state_991) (i_993)) in 
      let new_state_992 :=
        foldi (usize 0) (seq_len (bytes_994)) (fun j_995 new_state_992 =>
          let new_state_992 :=
            array_upd new_state_992 (((i_993) * (usize 8)) + (j_995)) (
              seq_index (bytes_994) (j_995)) in 
          (new_state_992))
        new_state_992 in 
      (new_state_992))
    new_state_992 in 
  new_state_992.

Definition run_f (strobe_996 : strobe_t) : strobe_t :=
  let '(state_997, pos_998, pos_begin_999, cur_fl_1000) :=
    strobe_996 in 
  let state_997 :=
    array_upd state_997 (pos_998) ((array_index (state_997) (pos_998)) .^ (
        secret (pos_begin_999) : int8)) in 
  let state_997 :=
    array_upd state_997 ((pos_998) .+ (@repr WORDSIZE8 1)) ((array_index (
          state_997) ((pos_998) .+ (@repr WORDSIZE8 1))) .^ (secret (
          @repr WORDSIZE8 4) : int8)) in 
  let state_997 :=
    array_upd state_997 ((strobe_r_v) .+ (@repr WORDSIZE8 1)) ((array_index (
          state_997) ((strobe_r_v) .+ (@repr WORDSIZE8 1))) .^ (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let state_uint64_1001 : state_t :=
    transmute_state_to_u64 (state_997) in 
  let state_997 :=
    transmute_state_to_u8 (keccakf1600 (state_uint64_1001)) in 
  let pos_998 :=
    @repr WORDSIZE8 0 in 
  let pos_begin_999 :=
    @repr WORDSIZE8 0 in 
  (state_997, pos_998, pos_begin_999, cur_fl_1000).

Definition absorb (strobe_1002 : strobe_t) (data_1003 : seq uint8) : strobe_t :=
  let '(state_1004, pos_1005, pos_begin_1006, cur_fl_1007) :=
    strobe_1002 in 
  let '(state_1004, pos_1005, pos_begin_1006, cur_fl_1007) :=
    foldi (usize 0) (seq_len (data_1003)) (fun i_1008 '(
        state_1004,
        pos_1005,
        pos_begin_1006,
        cur_fl_1007
      ) =>
      let state_1004 :=
        array_upd state_1004 (pos_1005) ((array_index (state_1004) (
              pos_1005)) .^ (seq_index (data_1003) (i_1008))) in 
      let pos_1005 :=
        (pos_1005) .+ (@repr WORDSIZE8 1) in 
      let '(state_1004, pos_1005, pos_begin_1006, cur_fl_1007) :=
        if (pos_1005) =.? (strobe_r_v):bool then (let '(
              s_1009,
              p_1010,
              pb_1011,
              cf_1012
            ) :=
            run_f ((state_1004, pos_1005, pos_begin_1006, cur_fl_1007)) in 
          let state_1004 :=
            s_1009 in 
          let pos_1005 :=
            p_1010 in 
          let pos_begin_1006 :=
            pb_1011 in 
          let cur_fl_1007 :=
            cf_1012 in 
          (state_1004, pos_1005, pos_begin_1006, cur_fl_1007)) else ((
            state_1004,
            pos_1005,
            pos_begin_1006,
            cur_fl_1007
          )) in 
      (state_1004, pos_1005, pos_begin_1006, cur_fl_1007))
    (state_1004, pos_1005, pos_begin_1006, cur_fl_1007) in 
  (state_1004, pos_1005, pos_begin_1006, cur_fl_1007).

Definition squeeze
  (strobe_1013 : strobe_t)
  (data_1014 : seq uint8)
  : (strobe_t '× seq uint8) :=
  let '(state_1015, pos_1016, pos_begin_1017, cur_fl_1018) :=
    strobe_1013 in 
  let '(data_1014, state_1015, pos_1016, pos_begin_1017, cur_fl_1018) :=
    foldi (usize 0) (seq_len (data_1014)) (fun i_1019 '(
        data_1014,
        state_1015,
        pos_1016,
        pos_begin_1017,
        cur_fl_1018
      ) =>
      let data_1014 :=
        seq_upd data_1014 (i_1019) (array_index (state_1015) (pos_1016)) in 
      let state_1015 :=
        array_upd state_1015 (pos_1016) (uint8_classify (@repr WORDSIZE8 0)) in 
      let pos_1016 :=
        (pos_1016) .+ (@repr WORDSIZE8 1) in 
      let '(state_1015, pos_1016, pos_begin_1017, cur_fl_1018) :=
        if (pos_1016) =.? (strobe_r_v):bool then (let '(
              s_1020,
              p_1021,
              pb_1022,
              cf_1023
            ) :=
            run_f (((state_1015), pos_1016, pos_begin_1017, cur_fl_1018)) in 
          let state_1015 :=
            s_1020 in 
          let pos_1016 :=
            p_1021 in 
          let pos_begin_1017 :=
            pb_1022 in 
          let cur_fl_1018 :=
            cf_1023 in 
          (state_1015, pos_1016, pos_begin_1017, cur_fl_1018)) else ((
            state_1015,
            pos_1016,
            pos_begin_1017,
            cur_fl_1018
          )) in 
      (data_1014, state_1015, pos_1016, pos_begin_1017, cur_fl_1018))
    (data_1014, state_1015, pos_1016, pos_begin_1017, cur_fl_1018) in 
  ((state_1015, pos_1016, pos_begin_1017, cur_fl_1018), data_1014).

Definition begin_op
  (strobe_1024 : strobe_t)
  (flags_1025 : int8)
  (more_1026 : bool)
  : strobe_t :=
  let '(state_1027, pos_1028, pos_begin_1029, cur_fl_1030) :=
    strobe_1024 in 
  let ret_1031 : (state_uint8_t '× int8 '× int8 '× int8) :=
    (state_1027, pos_1028, pos_begin_1029, cur_fl_1030) in 
  let '(state_1027, pos_1028, pos_begin_1029, cur_fl_1030, ret_1031) :=
    if negb (more_1026):bool then (let old_begin_1032 : int8 :=
        pos_begin_1029 in 
      let pos_begin_1029 :=
        (pos_1028) .+ (@repr WORDSIZE8 1) in 
      let cur_fl_1030 :=
        flags_1025 in 
      let data_1033 : seq uint8 :=
        seq_new_ (default : uint8) (usize 2) in 
      let data_1033 :=
        seq_upd data_1033 (usize 0) (secret (old_begin_1032) : int8) in 
      let data_1033 :=
        seq_upd data_1033 (usize 1) (secret (flags_1025) : int8) in 
      let '(s_1034, p_1035, pb_1036, cf_1037) :=
        absorb ((state_1027, pos_1028, pos_begin_1029, cur_fl_1030)) (
          data_1033) in 
      let state_1027 :=
        s_1034 in 
      let pos_1028 :=
        p_1035 in 
      let pos_begin_1029 :=
        pb_1036 in 
      let cur_fl_1030 :=
        cf_1037 in 
      let force_f_1038 : bool :=
        (@repr WORDSIZE8 0) !=.? ((flags_1025) .& ((flag_c_v) .| (
              flag_k_v))) in 
      let '(ret_1031) :=
        if (force_f_1038) && ((pos_1028) !=.? (@repr WORDSIZE8 0)):bool then (
          let ret_1031 :=
            run_f ((state_1027, pos_1028, pos_begin_1029, cur_fl_1030)) in 
          (ret_1031)) else (let ret_1031 :=
            (state_1027, pos_1028, pos_begin_1029, cur_fl_1030) in 
          (ret_1031)) in 
      (state_1027, pos_1028, pos_begin_1029, cur_fl_1030, ret_1031)) else ((
        state_1027,
        pos_1028,
        pos_begin_1029,
        cur_fl_1030,
        ret_1031
      )) in 
  ret_1031.

Definition new_strobe (protocol_label_1039 : seq uint8) : strobe_t :=
  let st_1040 : state_uint8_t :=
    array_new_ (default : uint8) (200) in 
  let st_1040 :=
    array_set_chunk (st_1040) (usize 6) (usize 0) ([
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 168) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 1) : int8;
        secret (@repr WORDSIZE8 96) : int8
      ]) in 
  let st_1040 :=
    array_set_chunk (st_1040) (usize 6) (usize 1) ([
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 84) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 79) : int8;
        secret (@repr WORDSIZE8 66) : int8;
        secret (@repr WORDSIZE8 69) : int8
      ]) in 
  let st_1040 :=
    array_set_chunk (st_1040) (usize 6) (usize 2) ([
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 48) : int8;
        secret (@repr WORDSIZE8 46) : int8;
        secret (@repr WORDSIZE8 50) : int8
      ]) in 
  let st_uint64_1041 : state_t :=
    transmute_state_to_u64 (st_1040) in 
  let st_1040 :=
    transmute_state_to_u8 (keccakf1600 (st_uint64_1041)) in 
  meta_ad ((st_1040, @repr WORDSIZE8 0, @repr WORDSIZE8 0, @repr WORDSIZE8 0)) (
    protocol_label_1039) (false).

Definition meta_ad
  (strobe_1042 : strobe_t)
  (data_1043 : seq uint8)
  (more_1044 : bool)
  : strobe_t :=
  let strobe_1042 :=
    begin_op (strobe_1042) ((flag_m_v) .| (flag_a_v)) (more_1044) in 
  absorb (strobe_1042) (data_1043).

Definition ad
  (strobe_1045 : strobe_t)
  (data_1046 : seq uint8)
  (more_1047 : bool)
  : strobe_t :=
  let strobe_1045 :=
    begin_op (strobe_1045) (flag_a_v) (more_1047) in 
  absorb (strobe_1045) (data_1046).

Definition prf
  (strobe_1048 : strobe_t)
  (data_1049 : seq uint8)
  (more_1050 : bool)
  : (strobe_t '× seq uint8) :=
  let strobe_1048 :=
    begin_op (strobe_1048) (((flag_i_v) .| (flag_a_v)) .| (flag_c_v)) (
      more_1050) in 
  squeeze (strobe_1048) (data_1049).

