(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition blocksize_v : uint_size :=
  usize 16.

Definition gf128_block_t := nseq (uint8) (blocksize_v).

Definition gf128_key_t := nseq (uint8) (blocksize_v).

Definition gf128_tag_t := nseq (uint8) (blocksize_v).

Notation "'element_t'" := (uint128) : hacspec_scope.

Definition irred_v : element_t :=
  secret (@repr WORDSIZE128 299076299051606071403356588563077529600) : int128.

Definition fadd (x_317 : element_t) (y_318 : element_t) : element_t :=
  (x_317) .^ (y_318).

Definition fmul (x_319 : element_t) (y_320 : element_t) : element_t :=
  let res_321 : element_t :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let sh_322 : uint128 :=
    x_319 in 
  let '(res_321, sh_322) :=
    foldi (usize 0) (usize 128) (fun i_323 '(res_321, sh_322) =>
      let '(res_321) :=
        if (uint128_declassify ((y_320) .& ((secret (
                  @repr WORDSIZE128 1) : int128) shift_left ((usize 127) - (
                  i_323))))) !=.? (uint128_declassify (secret (
              @repr WORDSIZE128 0) : int128)):bool then (let res_321 :=
            (res_321) .^ (sh_322) in 
          (res_321)) else ((res_321)) in 
      let '(sh_322) :=
        if (uint128_declassify ((sh_322) .& (secret (
                @repr WORDSIZE128 1) : int128))) !=.? (uint128_declassify (
            secret (@repr WORDSIZE128 0) : int128)):bool then (let sh_322 :=
            ((sh_322) shift_right (usize 1)) .^ (irred_v) in 
          (sh_322)) else (let sh_322 :=
            (sh_322) shift_right (usize 1) in 
          (sh_322)) in 
      (res_321, sh_322))
    (res_321, sh_322) in 
  res_321.

Definition encode (block_324 : gf128_block_t) : element_t :=
  uint128_from_be_bytes (array_from_seq (16) (array_to_seq (block_324))).

Definition decode (e_325 : element_t) : gf128_block_t :=
  array_from_seq (blocksize_v) (array_to_seq (uint128_to_be_bytes (e_325))).

Definition update
  (r_326 : element_t)
  (block_327 : gf128_block_t)
  (acc_328 : element_t)
  : element_t :=
  fmul (fadd (encode (block_327)) (acc_328)) (r_326).

Definition poly (msg_329 : byte_seq) (r_330 : element_t) : element_t :=
  let l_331 : uint_size :=
    seq_len (msg_329) in 
  let n_blocks_332 : uint_size :=
    (l_331) / (blocksize_v) in 
  let rem_333 : uint_size :=
    (l_331) %% (blocksize_v) in 
  let acc_334 : uint128 :=
    secret (@repr WORDSIZE128 0) : int128 in 
  let acc_334 :=
    foldi (usize 0) (n_blocks_332) (fun i_335 acc_334 =>
      let k_336 : uint_size :=
        (i_335) * (blocksize_v) in 
      let block_337 : gf128_block_t :=
        array_new_ (default) (blocksize_v) in 
      let block_337 :=
        array_update_start (block_337) (seq_slice_range (msg_329) ((
              k_336,
              (k_336) + (blocksize_v)
            ))) in 
      let acc_334 :=
        update (r_330) (block_337) (acc_334) in 
      (acc_334))
    acc_334 in 
  let '(acc_334) :=
    if (rem_333) !=.? (usize 0):bool then (let k_338 : uint_size :=
        (n_blocks_332) * (blocksize_v) in 
      let last_block_339 : gf128_block_t :=
        array_new_ (default) (blocksize_v) in 
      let last_block_339 :=
        array_update_slice (last_block_339) (usize 0) (msg_329) (k_338) (
          rem_333) in 
      let acc_334 :=
        update (r_330) (last_block_339) (acc_334) in 
      (acc_334)) else ((acc_334)) in 
  acc_334.

Definition gmac (text_340 : byte_seq) (k_341 : gf128_key_t) : gf128_tag_t :=
  let s_342 : gf128_block_t :=
    array_new_ (default) (blocksize_v) in 
  let r_343 : uint128 :=
    encode (array_from_seq (blocksize_v) (array_to_seq (k_341))) in 
  let a_344 : uint128 :=
    poly (text_340) (r_343) in 
  array_from_seq (blocksize_v) (array_to_seq (decode (fadd (a_344) (encode (
          s_342))))).

