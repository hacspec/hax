(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition riotboot_magic_v : int32 :=
  @repr WORDSIZE32 1414482258.

Notation "'fletcher_t'" := ((int32 '× int32)) : hacspec_scope.

Definition new_fletcher  : fletcher_t :=
  (@repr WORDSIZE32 65535, @repr WORDSIZE32 65535).

Definition max_chunk_size  : uint_size :=
  usize 360.

Definition reduce_u32 (x_1293 : int32) : int32 :=
  ((x_1293) .& (@repr WORDSIZE32 65535)) .+ ((x_1293) shift_right (
      @repr WORDSIZE32 16)).

Definition combine (lower_1294 : int32) (upper_1295 : int32) : int32 :=
  (lower_1294) .| ((upper_1295) shift_left (@repr WORDSIZE32 16)).

Definition update_fletcher
  (f_1296 : fletcher_t)
  (data_1297 : seq int16)
  : fletcher_t :=
  let max_chunk_size_1298 : uint_size :=
    max_chunk_size  in 
  let '(a_1299, b_1300) :=
    f_1296 in 
  let '(a_1299, b_1300) :=
    foldi (usize 0) (seq_num_chunks (data_1297) (
          max_chunk_size_1298)) (fun i_1301 '(a_1299, b_1300) =>
      let '(chunk_len_1302, chunk_1303) :=
        seq_get_chunk (data_1297) (max_chunk_size_1298) (i_1301) in 
      let intermediate_a_1304 : int32 :=
        a_1299 in 
      let intermediate_b_1305 : int32 :=
        b_1300 in 
      let '(intermediate_a_1304, intermediate_b_1305) :=
        foldi (usize 0) (chunk_len_1302) (fun j_1306 '(
            intermediate_a_1304,
            intermediate_b_1305
          ) =>
          let intermediate_a_1304 :=
            (intermediate_a_1304) .+ (@cast _ uint32 _ (seq_index (chunk_1303) (
                  j_1306))) in 
          let intermediate_b_1305 :=
            (intermediate_b_1305) .+ (intermediate_a_1304) in 
          (intermediate_a_1304, intermediate_b_1305))
        (intermediate_a_1304, intermediate_b_1305) in 
      let a_1299 :=
        reduce_u32 (intermediate_a_1304) in 
      let b_1300 :=
        reduce_u32 (intermediate_b_1305) in 
      (a_1299, b_1300))
    (a_1299, b_1300) in 
  let a_1299 :=
    reduce_u32 (a_1299) in 
  let b_1300 :=
    reduce_u32 (b_1300) in 
  (a_1299, b_1300).

Definition value (x_1307 : fletcher_t) : int32 :=
  let '(a_1308, b_1309) :=
    x_1307 in 
  combine (a_1308) (b_1309).

Notation "'header_t'" := ((int32 '× int32 '× int32 '× int32
)) : hacspec_scope.

Definition header_as_u16_slice (h_1310 : header_t) : seq int16 :=
  let '(magic_1311, seq_number_1312, start_addr_1313, _) :=
    h_1310 in 
  let magic_1314 : u32_word_t :=
    u32_to_be_bytes (magic_1311) in 
  let seq_number_1315 : u32_word_t :=
    u32_to_be_bytes (seq_number_1312) in 
  let start_addr_1316 : u32_word_t :=
    u32_to_be_bytes (start_addr_1313) in 
  let u8_seq_1317 : seq int8 :=
    seq_new_ (default : int8) (usize 12) in 
  let u8_seq_1318 : seq int8 :=
    seq_update_slice (u8_seq_1317) (usize 0) (array_to_seq (magic_1314)) (
      usize 0) (usize 4) in 
  let u8_seq_1319 : seq int8 :=
    seq_update_slice (u8_seq_1318) (usize 4) (array_to_seq (seq_number_1315)) (
      usize 0) (usize 4) in 
  let u8_seq_1320 : seq int8 :=
    seq_update_slice (u8_seq_1319) (usize 8) (array_to_seq (start_addr_1316)) (
      usize 0) (usize 4) in 
  let u16_seq_1321 : seq int16 :=
    seq_new_ (default : int16) (usize 6) in 
  let u16_seq_1321 :=
    foldi (usize 0) (usize 3) (fun i_1322 u16_seq_1321 =>
      let u16_word_1323 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1320) ((i_1322) * (usize 4)) (
            usize 2)) in 
      let u16_value_1324 : int16 :=
        u16_from_be_bytes (u16_word_1323) in 
      let u16_seq_1321 :=
        seq_upd u16_seq_1321 (((usize 2) * (i_1322)) + (usize 1)) (
          u16_value_1324) in 
      let u16_word_1325 : u16_word_t :=
        array_from_seq (2) (seq_slice (u8_seq_1320) (((i_1322) * (usize 4)) + (
              usize 2)) (usize 2)) in 
      let u16_value_1326 : int16 :=
        u16_from_be_bytes (u16_word_1325) in 
      let u16_seq_1321 :=
        seq_upd u16_seq_1321 ((usize 2) * (i_1322)) (u16_value_1326) in 
      (u16_seq_1321))
    u16_seq_1321 in 
  u16_seq_1321.

Definition is_valid_header (h_1327 : header_t) : bool :=
  let '(magic_number_1328, seq_number_1329, start_addr_1330, checksum_1331) :=
    h_1327 in 
  let slice_1332 : seq int16 :=
    header_as_u16_slice ((
        magic_number_1328,
        seq_number_1329,
        start_addr_1330,
        checksum_1331
      )) in 
  let result_1333 : bool :=
    false in 
  let '(result_1333) :=
    if (magic_number_1328) =.? (riotboot_magic_v):bool then (
      let fletcher_1334 : (int32 '× int32) :=
        new_fletcher  in 
      let fletcher_1335 : (int32 '× int32) :=
        update_fletcher (fletcher_1334) (slice_1332) in 
      let sum_1336 : int32 :=
        value (fletcher_1335) in 
      let result_1333 :=
        (sum_1336) =.? (checksum_1331) in 
      (result_1333)) else ((result_1333)) in 
  result_1333.

Definition choose_image (images_1337 : seq header_t) : (bool '× int32) :=
  let image_1338 : int32 :=
    @repr WORDSIZE32 0 in 
  let image_found_1339 : bool :=
    false in 
  let '(image_1338, image_found_1339) :=
    foldi (usize 0) (seq_len (images_1337)) (fun i_1340 '(
        image_1338,
        image_found_1339
      ) =>
      let header_1341 : (int32 '× int32 '× int32 '× int32) :=
        seq_index (images_1337) (i_1340) in 
      let '(magic_number_1342, seq_number_1343, start_addr_1344, checksum_1345
        ) :=
        header_1341 in 
      let '(image_1338, image_found_1339) :=
        if is_valid_header ((
            magic_number_1342,
            seq_number_1343,
            start_addr_1344,
            checksum_1345
          )):bool then (let change_image_1346 : bool :=
            negb ((image_found_1339) && ((seq_number_1343) <=.? (
                  image_1338))) in 
          let '(image_1338, image_found_1339) :=
            if change_image_1346:bool then (let image_1338 :=
                start_addr_1344 in 
              let image_found_1339 :=
                true in 
              (image_1338, image_found_1339)) else ((
                image_1338,
                image_found_1339
              )) in 
          (image_1338, image_found_1339)) else ((image_1338, image_found_1339
          )) in 
      (image_1338, image_found_1339))
    (image_1338, image_found_1339) in 
  (image_found_1339, image_1338).

