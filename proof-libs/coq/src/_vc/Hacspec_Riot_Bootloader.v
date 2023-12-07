(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition riotboot_magic_v : int32 :=
  @repr WORDSIZE32 1414482258.

Notation "'fletcher_t'" := ((int32 × int32)) : hacspec_scope.

Definition new_fletcher  : fletcher_t :=
  (@repr WORDSIZE32 65535, @repr WORDSIZE32 65535).

Definition max_chunk_size  : uint_size :=
  usize 360.

Definition reduce_u32 (x_951 : int32) : int32 :=
  ((x_951) .& (@repr WORDSIZE32 65535)) .+ ((x_951) shift_right (
      @repr WORDSIZE32 16)).

Definition combine (lower_952 : int32) (upper_953 : int32) : int32 :=
  (lower_952) .| ((upper_953) shift_left (@repr WORDSIZE32 16)).

Definition update_fletcher
  (f_954 : fletcher_t)
  (data_955 : seq int16)
  : fletcher_t :=
  let max_chunk_size_956 : uint_size :=
    max_chunk_size  in 
  let '(a_957, b_958) :=
    f_954 in 
  let '(a_957, b_958) :=
    foldi (usize 0) (seq_num_chunks (data_955) (
          max_chunk_size_956)) (fun i_959 '(a_957, b_958) =>
      let '(chunk_len_960, chunk_961) :=
        seq_get_chunk (data_955) (max_chunk_size_956) (i_959) in 
      let intermediate_a_962 : int32 :=
        a_957 in 
      let intermediate_b_963 : int32 :=
        b_958 in 
      let '(intermediate_a_962, intermediate_b_963) :=
        foldi (usize 0) (chunk_len_960) (fun j_964 '(
            intermediate_a_962,
            intermediate_b_963
          ) =>
          let intermediate_a_962 :=
            (intermediate_a_962) .+ (@cast _ uint32 _ (seq_index (chunk_961) (
                  j_964))) in 
          let intermediate_b_963 :=
            (intermediate_b_963) .+ (intermediate_a_962) in 
          (intermediate_a_962, intermediate_b_963))
        (intermediate_a_962, intermediate_b_963) in 
      let a_957 :=
        reduce_u32 (intermediate_a_962) in 
      let b_958 :=
        reduce_u32 (intermediate_b_963) in 
      (a_957, b_958))
    (a_957, b_958) in 
  let a_957 :=
    reduce_u32 (a_957) in 
  let b_958 :=
    reduce_u32 (b_958) in 
  (a_957, b_958).

Definition value (x_965 : fletcher_t) : int32 :=
  let '(a_966, b_967) :=
    x_965 in 
  combine (a_966) (b_967).

Notation "'header_t'" := ((int32 × int32 × int32 × int32)) : hacspec_scope.

Definition header_as_u16_slice (h_968 : header_t) : seq int16 :=
  let '(magic_969, seq_number_970, start_addr_971, _) :=
    h_968 in 
  let magic_972 : u32_word_t :=
    u32_to_be_bytes (magic_969) in 
  let seq_number_973 : u32_word_t :=
    u32_to_be_bytes (seq_number_970) in 
  let start_addr_974 : u32_word_t :=
    u32_to_be_bytes (start_addr_971) in 
  let u8_seq_975 : seq int8 :=
    seq_new_ (default) (usize 12) in 
  let u8_seq_976 : seq int8 :=
    seq_update_slice (u8_seq_975) (usize 0) (array_to_seq (magic_972)) (
      usize 0) (usize 4) in 
  let u8_seq_977 : seq int8 :=
    seq_update_slice (u8_seq_976) (usize 4) (array_to_seq (seq_number_973)) (
      usize 0) (usize 4) in 
  let u8_seq_978 : seq int8 :=
    seq_update_slice (u8_seq_977) (usize 8) (array_to_seq (start_addr_974)) (
      usize 0) (usize 4) in 
  let u16_seq_979 : seq int16 :=
    seq_new_ (default) (usize 6) in 
  let u16_seq_979 :=
    foldi (usize 0) (usize 3) (fun i_980 u16_seq_979 =>
      let u16_word_981 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_978) ((i_980) * (usize 4)) (
            usize 2)) in 
      let u16_value_982 : int16 :=
        u16_from_be_bytes (u16_word_981) in 
      let u16_seq_979 :=
        seq_upd u16_seq_979 (((usize 2) * (i_980)) + (usize 1)) (
          u16_value_982) in 
      let u16_word_983 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_978) (((i_980) * (usize 4)) + (
              usize 2)) (usize 2)) in 
      let u16_value_984 : int16 :=
        u16_from_be_bytes (u16_word_983) in 
      let u16_seq_979 :=
        seq_upd u16_seq_979 ((usize 2) * (i_980)) (u16_value_984) in 
      (u16_seq_979))
    u16_seq_979 in 
  u16_seq_979.

Definition is_valid_header (h_985 : header_t) : bool :=
  let '(magic_number_986, seq_number_987, start_addr_988, checksum_989) :=
    h_985 in 
  let slice_990 : seq int16 :=
    header_as_u16_slice ((
        magic_number_986,
        seq_number_987,
        start_addr_988,
        checksum_989
      )) in 
  let result_991 : bool :=
    false in 
  let '(result_991) :=
    if (magic_number_986) =.? (riotboot_magic_v):bool then (let fletcher_992 : (
          int32 ×
          int32
        ) :=
        new_fletcher  in 
      let fletcher_993 : (int32 × int32) :=
        update_fletcher (fletcher_992) (slice_990) in 
      let sum_994 : int32 :=
        value (fletcher_993) in 
      let result_991 :=
        (sum_994) =.? (checksum_989) in 
      (result_991)) else ((result_991)) in 
  result_991.

Definition choose_image (images_995 : seq header_t) : (bool × int32) :=
  let image_996 : int32 :=
    @repr WORDSIZE32 0 in 
  let image_found_997 : bool :=
    false in 
  let '(image_996, image_found_997) :=
    foldi (usize 0) (seq_len (images_995)) (fun i_998 '(
        image_996,
        image_found_997
      ) =>
      let header_999 : (int32 × int32 × int32 × int32) :=
        seq_index (images_995) (i_998) in 
      let '(magic_number_1000, seq_number_1001, start_addr_1002, checksum_1003
        ) :=
        header_999 in 
      let '(image_996, image_found_997) :=
        if is_valid_header ((
            magic_number_1000,
            seq_number_1001,
            start_addr_1002,
            checksum_1003
          )):bool then (let change_image_1004 : bool :=
            negb ((image_found_997) && ((seq_number_1001) <=.? (image_996))) in 
          let '(image_996, image_found_997) :=
            if change_image_1004:bool then (let image_996 :=
                start_addr_1002 in 
              let image_found_997 :=
                true in 
              (image_996, image_found_997)) else ((image_996, image_found_997
              )) in 
          (image_996, image_found_997)) else ((image_996, image_found_997)) in 
      (image_996, image_found_997))
    (image_996, image_found_997) in 
  (image_found_997, image_996).

