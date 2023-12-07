(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition schedule_t := nseq (uint32) (usize 80).

Definition block_words_v : uint_size :=
  (usize 512) / (usize 32).

Definition hash_words_v : uint_size :=
  (usize 160) / (usize 32).

Definition block_t := nseq (uint32) (block_words_v).

Definition hash_t := nseq (uint32) (hash_words_v).

Definition block_bytes_v : uint_size :=
  (usize 512) / (usize 8).

Definition hash_bytes_v : uint_size :=
  (usize 160) / (usize 8).

Definition block_bytes_t := nseq (uint8) (block_bytes_v).

Definition sha1_digest_t := nseq (uint8) (hash_bytes_v).

Definition bitlength_bytes_v : uint_size :=
  (usize 64) / (usize 8).

Definition ch (x_1225 : uint32) (y_1226 : uint32) (z_1227 : uint32) : uint32 :=
  ((x_1225) .& (y_1226)) .^ ((not (x_1225)) .& (z_1227)).

Definition parity
  (x_1228 : uint32)
  (y_1229 : uint32)
  (z_1230 : uint32)
  : uint32 :=
  ((x_1228) .^ (y_1229)) .^ (z_1230).

Definition maj (x_1231 : uint32) (y_1232 : uint32) (z_1233 : uint32) : uint32 :=
  (((x_1231) .& (y_1232)) .^ ((x_1231) .& (z_1233))) .^ ((y_1232) .& (z_1233)).

Definition hash_init_v : hash_t :=
  array_from_list uint32 (let l :=
      [
        secret (@repr WORDSIZE32 1732584193) : int32;
        secret (@repr WORDSIZE32 4023233417) : int32;
        secret (@repr WORDSIZE32 2562383102) : int32;
        secret (@repr WORDSIZE32 271733878) : int32;
        secret (@repr WORDSIZE32 3285377520) : int32
      ] in  l).

Definition compress (m_bytes_1234 : block_bytes_t) (h_1235 : hash_t) : hash_t :=
  let m_1236 : seq uint32 :=
    array_to_be_uint32s (m_bytes_1234) in 
  let w_1237 : schedule_t :=
    array_new_ (default : uint32) (80) in 
  let w_1237 :=
    foldi (usize 0) (usize 80) (fun t_1238 w_1237 =>
      let '(w_1237) :=
        if (t_1238) <.? (usize 16):bool then (let w_1237 :=
            array_upd w_1237 (t_1238) (seq_index (m_1236) (t_1238)) in 
          (w_1237)) else (let w_1237 :=
            array_upd w_1237 (t_1238) (uint32_rotate_left ((((array_index (
                        w_1237) ((t_1238) - (usize 3))) .^ (array_index (
                        w_1237) ((t_1238) - (usize 8)))) .^ (array_index (
                      w_1237) ((t_1238) - (usize 14)))) .^ (array_index (
                    w_1237) ((t_1238) - (usize 16)))) (usize 1)) in 
          (w_1237)) in 
      (w_1237))
    w_1237 in 
  let a_1239 : uint32 :=
    array_index (h_1235) (usize 0) in 
  let b_1240 : uint32 :=
    array_index (h_1235) (usize 1) in 
  let c_1241 : uint32 :=
    array_index (h_1235) (usize 2) in 
  let d_1242 : uint32 :=
    array_index (h_1235) (usize 3) in 
  let e_1243 : uint32 :=
    array_index (h_1235) (usize 4) in 
  let '(a_1239, b_1240, c_1241, d_1242, e_1243) :=
    foldi (usize 0) (usize 80) (fun t_1244 '(
        a_1239,
        b_1240,
        c_1241,
        d_1242,
        e_1243
      ) =>
      let t_1245 : uint32 :=
        uint32_zero  in 
      let '(t_1245) :=
        if ((usize 0) <=.? (t_1244)) && ((t_1244) <.? (usize 20)):bool then (
          let t_1245 :=
            ((((uint32_rotate_left (a_1239) (usize 5)) .+ (ch (b_1240) (
                      c_1241) (d_1242))) .+ (e_1243)) .+ (secret (
                  @repr WORDSIZE32 1518500249) : int32)) .+ (array_index (
                w_1237) (t_1244)) in 
          (t_1245)) else ((t_1245)) in 
      let '(t_1245) :=
        if ((usize 20) <=.? (t_1244)) && ((t_1244) <.? (usize 40)):bool then (
          let t_1245 :=
            ((((uint32_rotate_left (a_1239) (usize 5)) .+ (parity (b_1240) (
                      c_1241) (d_1242))) .+ (e_1243)) .+ (secret (
                  @repr WORDSIZE32 1859775393) : int32)) .+ (array_index (
                w_1237) (t_1244)) in 
          (t_1245)) else ((t_1245)) in 
      let '(t_1245) :=
        if ((usize 40) <=.? (t_1244)) && ((t_1244) <.? (usize 60)):bool then (
          let t_1245 :=
            ((((uint32_rotate_left (a_1239) (usize 5)) .+ (maj (b_1240) (
                      c_1241) (d_1242))) .+ (e_1243)) .+ (secret (
                  @repr WORDSIZE32 2400959708) : int32)) .+ (array_index (
                w_1237) (t_1244)) in 
          (t_1245)) else ((t_1245)) in 
      let '(t_1245) :=
        if ((usize 60) <=.? (t_1244)) && ((t_1244) <.? (usize 80)):bool then (
          let t_1245 :=
            ((((uint32_rotate_left (a_1239) (usize 5)) .+ (parity (b_1240) (
                      c_1241) (d_1242))) .+ (e_1243)) .+ (secret (
                  @repr WORDSIZE32 3395469782) : int32)) .+ (array_index (
                w_1237) (t_1244)) in 
          (t_1245)) else ((t_1245)) in 
      let e_1243 :=
        d_1242 in 
      let d_1242 :=
        c_1241 in 
      let c_1241 :=
        uint32_rotate_left (b_1240) (usize 30) in 
      let b_1240 :=
        a_1239 in 
      let a_1239 :=
        t_1245 in 
      (a_1239, b_1240, c_1241, d_1242, e_1243))
    (a_1239, b_1240, c_1241, d_1242, e_1243) in 
  let h_1235 :=
    array_upd h_1235 (usize 0) ((a_1239) .+ (array_index (h_1235) (
          usize 0))) in 
  let h_1235 :=
    array_upd h_1235 (usize 1) ((b_1240) .+ (array_index (h_1235) (
          usize 1))) in 
  let h_1235 :=
    array_upd h_1235 (usize 2) ((c_1241) .+ (array_index (h_1235) (
          usize 2))) in 
  let h_1235 :=
    array_upd h_1235 (usize 3) ((d_1242) .+ (array_index (h_1235) (
          usize 3))) in 
  let h_1235 :=
    array_upd h_1235 (usize 4) ((e_1243) .+ (array_index (h_1235) (
          usize 4))) in 
  h_1235.

Definition hash (msg_1246 : byte_seq) : sha1_digest_t :=
  let h_1247 : hash_t :=
    hash_init_v in 
  let h_1247 :=
    foldi (usize 0) (seq_num_exact_chunks (msg_1246) (
          block_bytes_v)) (fun i_1248 h_1247 =>
      let raw_bytes_1249 : seq uint8 :=
        seq_get_exact_chunk (msg_1246) (block_bytes_v) (i_1248) in 
      let block_bytes_1250 : block_bytes_t :=
        array_from_seq (block_bytes_v) (raw_bytes_1249) in 
      let h_1247 :=
        compress (block_bytes_1250) (h_1247) in 
      (h_1247))
    h_1247 in 
  let raw_bytes_1251 : seq uint8 :=
    seq_get_remainder_chunk (msg_1246) (block_bytes_v) in 
  let block_bytes_1252 : block_bytes_t :=
    array_update_start (array_new_ (default : uint8) (block_bytes_v)) (
      raw_bytes_1251) in 
  let block_bytes_1252 :=
    array_upd block_bytes_1252 (seq_len (raw_bytes_1251)) (secret (
        @repr WORDSIZE8 128) : int8) in 
  let message_bitlength_1253 : uint64 :=
    secret (pub_u64 ((seq_len (msg_1246)) * (usize 8))) : int64 in 
  let '(h_1247, block_bytes_1252) :=
    if (seq_len (raw_bytes_1251)) <.? ((block_bytes_v) - (
        bitlength_bytes_v)):bool then (let block_bytes_1252 :=
        array_update (block_bytes_1252) ((block_bytes_v) - (
            bitlength_bytes_v)) (array_to_seq (uint64_to_be_bytes (
            message_bitlength_1253))) in 
      let h_1247 :=
        compress (block_bytes_1252) (h_1247) in 
      (h_1247, block_bytes_1252)) else (let h_1247 :=
        compress (block_bytes_1252) (h_1247) in 
      let pad_block_1254 : block_bytes_t :=
        array_new_ (default : uint8) (block_bytes_v) in 
      let pad_block_1254 :=
        array_update (pad_block_1254) ((block_bytes_v) - (bitlength_bytes_v)) (
          array_to_seq (uint64_to_be_bytes (message_bitlength_1253))) in 
      let h_1247 :=
        compress (pad_block_1254) (h_1247) in 
      (h_1247, block_bytes_1252)) in 
  array_from_seq (hash_bytes_v) (array_to_be_bytes (h_1247)).

Definition sha1 (msg_1255 : byte_seq) : sha1_digest_t :=
  hash (msg_1255).

