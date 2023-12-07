(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Aes.

Require Import Hacspec_Gf128.

Notation "'aes_gcm_byte_seq_result_t'" := ((
  result byte_seq int8)) : hacspec_scope.

Definition invalid_tag_v : int8 :=
  @repr WORDSIZE8 1.

Definition pad_aad_msg (aad_278 : byte_seq) (msg_279 : byte_seq) : byte_seq :=
  let laad_280 : uint_size :=
    seq_len (aad_278) in 
  let lmsg_281 : uint_size :=
    seq_len (msg_279) in 
  let pad_aad_282 : uint_size :=
    (if (((laad_280) %% (usize 16)) =.? (usize 0)):bool then (laad_280) else ((
          laad_280) + ((usize 16) - ((laad_280) %% (usize 16))))) in 
  let pad_msg_283 : uint_size :=
    (if (((lmsg_281) %% (usize 16)) =.? (usize 0)):bool then (lmsg_281) else ((
          lmsg_281) + ((usize 16) - ((lmsg_281) %% (usize 16))))) in 
  let padded_msg_284 : seq uint8 :=
    seq_new_ (default : uint8) (((pad_aad_282) + (pad_msg_283)) + (
        usize 16)) in 
  let padded_msg_284 :=
    seq_update (padded_msg_284) (usize 0) (aad_278) in 
  let padded_msg_284 :=
    seq_update (padded_msg_284) (pad_aad_282) (msg_279) in 
  let padded_msg_284 :=
    seq_update (padded_msg_284) ((pad_aad_282) + (pad_msg_283)) (
      array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (
              laad_280)) : int64) .* (secret (
            @repr WORDSIZE64 8) : int64)))) in 
  let padded_msg_284 :=
    seq_update (padded_msg_284) (((pad_aad_282) + (pad_msg_283)) + (usize 8)) (
      array_to_seq (uint64_to_be_bytes ((secret (pub_u64 (
              lmsg_281)) : int64) .* (secret (
            @repr WORDSIZE64 8) : int64)))) in 
  padded_msg_284.

Definition encrypt_aes
  (key_285 : byte_seq)
  (iv_286 : aes_nonce_t)
  (aad_287 : byte_seq)
  (msg_288 : byte_seq)
  : (byte_seq '× gf128_tag_t) :=
  let iv0_289 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
  let mac_key_290 : block_t :=
    result_unwrap (aes_ctr_key_block (key_285) (iv0_289) (secret (
          @repr WORDSIZE32 0) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) in 
  let tag_mix_291 : block_t :=
    result_unwrap (aes_ctr_key_block (key_285) ((iv_286)) (secret (
          @repr WORDSIZE32 1) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) in 
  let cipher_text_292 : seq uint8 :=
    aes128_encrypt (array_from_seq (_) (key_285)) (iv_286) (secret (
        @repr WORDSIZE32 2) : int32) (msg_288) in 
  let padded_msg_293 : seq uint8 :=
    pad_aad_msg (aad_287) (cipher_text_292) in 
  let tag_294 : gf128_tag_t :=
    gmac (padded_msg_293) (array_from_seq (_) (array_to_seq (mac_key_290))) in 
  let tag_295 : block_t :=
    xor_block (array_from_seq (_) (array_to_seq (tag_294))) (tag_mix_291) in 
  (cipher_text_292, array_from_seq (_) (array_to_seq (tag_295))).

Definition encrypt_aes128
  (key_296 : key128_t)
  (iv_297 : aes_nonce_t)
  (aad_298 : byte_seq)
  (msg_299 : byte_seq)
  : (byte_seq '× gf128_tag_t) :=
  encrypt_aes (seq_from_seq (array_to_seq (key_296))) (iv_297) (aad_298) (
    msg_299).

Definition decrypt_aes
  (key_300 : byte_seq)
  (iv_301 : aes_nonce_t)
  (aad_302 : byte_seq)
  (cipher_text_303 : byte_seq)
  (tag_304 : gf128_tag_t)
  : aes_gcm_byte_seq_result_t :=
  let iv0_305 : aes_nonce_t :=
    array_new_ (default : uint8) (_) in 
  bind (aes_ctr_key_block (key_300) (iv0_305) (secret (
        @repr WORDSIZE32 0) : int32) (key_length_v) (rounds_v) (
      key_schedule_length_v) (key_length_v) (iterations_v)) (fun mac_key_306 =>
    bind (aes_ctr_key_block (key_300) ((iv_301)) (secret (
          @repr WORDSIZE32 1) : int32) (key_length_v) (rounds_v) (
        key_schedule_length_v) (key_length_v) (iterations_v)) (
      fun tag_mix_307 => let padded_msg_308 : seq uint8 :=
        pad_aad_msg (aad_302) (cipher_text_303) in 
      let my_tag_309 : gf128_tag_t :=
        gmac (padded_msg_308) (array_from_seq (_) (
            array_to_seq (mac_key_306))) in 
      let my_tag_310 : block_t :=
        xor_block (array_from_seq (_) (array_to_seq (my_tag_309))) (
          tag_mix_307) in 
      let ptxt_311 : seq uint8 :=
        aes128_decrypt (array_from_seq (_) (key_300)) (iv_301) (secret (
            @repr WORDSIZE32 2) : int32) (cipher_text_303) in 
      (if (array_declassify_eq (my_tag_310) (array_from_seq (_) (
              array_to_seq (tag_304)))):bool then (@Ok byte_seq int8 (
            ptxt_311)) else (@Err byte_seq int8 (invalid_tag_v))))).

Definition decrypt_aes128
  (key_312 : key128_t)
  (iv_313 : aes_nonce_t)
  (aad_314 : byte_seq)
  (cipher_text_315 : byte_seq)
  (tag_316 : gf128_tag_t)
  : aes_gcm_byte_seq_result_t :=
  decrypt_aes (seq_from_seq (array_to_seq (key_312))) (iv_313) (aad_314) (
    cipher_text_315) (tag_316).

