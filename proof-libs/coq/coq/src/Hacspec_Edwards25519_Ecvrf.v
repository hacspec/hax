(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Edwards25519.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519_Hash.

Inductive errorec_t :=
| FailedVerify : errorec_t
| MessageTooLarge : errorec_t
| InvalidProof : errorec_t
| InvalidPublicKey : errorec_t
| FailedDecompression : errorec_t
| FailedE2C : errorec_t.

Notation "'byte_seq_result_t'" := ((result byte_seq errorec_t)) : hacspec_scope.

Notation "'proof_result_t'" := ((result (ed_point_t '× scalar_t '× scalar_t
  ) errorec_t)) : hacspec_scope.

Notation "'ed_point_result_t'" := ((
  result ed_point_t errorec_t)) : hacspec_scope.

Definition large_mod_canvas_t := nseq (int8) (32).
Definition large_mod_t :=
  nat_mod 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff.

Definition arr_large_mod_t := nseq (uint64) (usize 4).

Definition q_v : arr_large_mod_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 9223372036854775807) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551615) : int64;
        secret (@repr WORDSIZE64 18446744073709551597) : int64
      ] in  l).

Definition c_len_v : uint_size :=
  usize 16.

Definition pt_len_v : uint_size :=
  usize 32.

Definition q_len_v : uint_size :=
  usize 32.

Definition int_byte_t := nseq (uint8) (usize 1).

Definition zero_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 0) : int8] in  l).

Definition one_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 1) : int8] in  l).

Definition two_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 2) : int8] in  l).

Definition three_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 3) : int8] in  l).

Definition four_v : int_byte_t :=
  array_from_list uint8 (let l := [secret (@repr WORDSIZE8 4) : int8] in  l).

Definition suite_string_v : int_byte_t :=
  four_v.

Definition dst_t := nseq (uint8) (usize 39).

Definition h2c_suite_id_string_v : dst_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 67) : int8;
        secret (@repr WORDSIZE8 86) : int8;
        secret (@repr WORDSIZE8 82) : int8;
        secret (@repr WORDSIZE8 70) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 97) : int8;
        secret (@repr WORDSIZE8 114) : int8;
        secret (@repr WORDSIZE8 100) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 57) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 68) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 72) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 45) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 49) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 69) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 76) : int8;
        secret (@repr WORDSIZE8 50) : int8;
        secret (@repr WORDSIZE8 95) : int8;
        secret (@repr WORDSIZE8 78) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 95) : int8
      ] in  l).

Definition ecvrf_encode_to_curve_try_and_increment
  (encode_to_curve_salt_2457 : byte_seq)
  (alpha_2458 : byte_seq)
  : ed_point_result_t :=
  let h_2459 : (option ed_point_t) :=
    @None ed_point_t in 
  let x_2460 : ed25519_field_element_t :=
    nat_mod_zero  in 
  let '(h_2459, x_2460) :=
    foldi (usize 1) (usize 256) (fun ctr_2461 '(h_2459, x_2460) =>
      let '(h_2459, x_2460) :=
        if ((h_2459)) =.? (@None ed_point_t):bool then (
          let ctr_string_2462 : seq uint8 :=
            seq_slice (nat_mod_to_byte_seq_be (x_2460)) (usize 31) (usize 1) in 
          let hash_string_2463 : sha512_digest_t :=
            sha512 (seq_concat (seq_concat (seq_concat (seq_concat (
                      array_concat (suite_string_v) (array_to_seq (one_v))) (
                      encode_to_curve_salt_2457)) (alpha_2458)) (
                  ctr_string_2462)) (array_to_seq (zero_v))) in 
          let h_2459 :=
            decompress (array_from_slice (default : uint8) (32) (
                array_to_seq (hash_string_2463)) (usize 0) (usize 32)) in 
          let x_2460 :=
            (x_2460) +% (nat_mod_one ) in 
          (h_2459, x_2460)) else ((h_2459, x_2460)) in 
      (h_2459, x_2460))
    (h_2459, x_2460) in 
  bind (option_ok_or (h_2459) (FailedE2C)) (fun h_2464 =>
    @Ok ed_point_t errorec_t (point_mul_by_cofactor (h_2464))).

Definition ecvrf_encode_to_curve_h2c_suite
  (encode_to_curve_salt_2465 : byte_seq)
  (alpha_2466 : byte_seq)
  : ed_point_result_t :=
  let string_to_be_hashed_2467 : seq uint8 :=
    seq_concat (encode_to_curve_salt_2465) (alpha_2466) in 
  let dst_2468 : seq uint8 :=
    array_concat (h2c_suite_id_string_v) (array_to_seq (suite_string_v)) in 
  let h_2469 : (result (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) error_t) :=
    ed_encode_to_curve (string_to_be_hashed_2467) (dst_2468) in 
  bind (option_ok_or (result_ok (h_2469)) (FailedE2C)) (fun h_2470 =>
    @Ok ed_point_t errorec_t (h_2470)).

Definition ecvrf_nonce_generation
  (sk_2471 : secret_key_t)
  (h_string_2472 : byte_seq)
  : scalar_t :=
  let hashed_sk_string_2473 : sha512_digest_t :=
    sha512 (array_to_le_bytes (sk_2471)) in 
  let truncated_hashed_sk_string_2474 : seq uint8 :=
    array_slice (hashed_sk_string_2473) (usize 32) (usize 32) in 
  let k_string_2475 : sha512_digest_t :=
    sha512 (seq_concat (truncated_hashed_sk_string_2474) (h_string_2472)) in 
  let nonce_2476 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (k_string_2475)) : big_scalar_t in 
  let nonceseq_2477 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (nonce_2476)) (usize 0) (usize 32) in 
  nat_mod_from_byte_seq_le (nonceseq_2477) : scalar_t.

Definition ecvrf_challenge_generation
  (p1_2478 : ed_point_t)
  (p2_2479 : ed_point_t)
  (p3_2480 : ed_point_t)
  (p4_2481 : ed_point_t)
  (p5_2482 : ed_point_t)
  : scalar_t :=
  let string_2483 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (seq_concat (
                array_concat (suite_string_v) (array_to_seq (two_v))) (encode (
                  p1_2478))) (encode (p2_2479))) (encode (p3_2480))) (encode (
            p4_2481))) (encode (p5_2482))) (array_to_seq (zero_v)) in 
  let c_string_2484 : sha512_digest_t :=
    sha512 (string_2483) in 
  let truncated_c_string_2485 : seq uint8 :=
    seq_concat (array_slice (c_string_2484) (usize 0) (c_len_v)) (seq_new_ (
        default : uint8) (usize 16)) in 
  nat_mod_from_byte_seq_le (truncated_c_string_2485) : scalar_t.

Definition ecvrf_decode_proof (pi_2486 : byte_seq) : proof_result_t :=
  let gamma_string_2487 : seq uint8 :=
    seq_slice (pi_2486) (usize 0) (pt_len_v) in 
  let c_string_2488 : seq uint8 :=
    seq_slice (pi_2486) (pt_len_v) (c_len_v) in 
  let s_string_2489 : seq uint8 :=
    seq_slice (pi_2486) ((pt_len_v) + (c_len_v)) (q_len_v) in 
  bind (option_ok_or (decompress (array_from_slice (default : uint8) (32) (
          gamma_string_2487) (usize 0) (usize 32))) (InvalidProof)) (
    fun gamma_2490 => let c_2491 : scalar_t :=
      nat_mod_from_byte_seq_le (seq_concat (c_string_2488) (seq_new_ (
            default : uint8) (usize 16))) : scalar_t in 
    let s_2492 : scalar_t :=
      nat_mod_from_byte_seq_le ((s_string_2489)) : scalar_t in 
    let s_test_2493 : large_mod_t :=
      nat_mod_from_byte_seq_le (s_string_2489) : large_mod_t in 
    let q_2494 : large_mod_t :=
      nat_mod_from_byte_seq_be (array_to_be_bytes (q_v)) : large_mod_t in 
    (if ((s_test_2493) >=.? (q_2494)):bool then (@Err (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t (InvalidProof)) else (@Ok (
          ed_point_t '×
          scalar_t '×
          scalar_t
        ) errorec_t ((gamma_2490, c_2491, s_2492))))).

Definition ecvrf_validate_key
  (y_2495 : public_key_t)
  : (result unit errorec_t) :=
  bind (option_ok_or (decompress (y_2495)) (InvalidPublicKey)) (fun y_2496 =>
    let y_prime_2497 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (y_2496) in 
    (if ((y_prime_2497) =.? (point_identity )):bool then (@Err unit errorec_t (
          InvalidPublicKey)) else (@Ok unit errorec_t (tt)))).

Definition ecvrf_prove
  (sk_2498 : secret_key_t)
  (alpha_2499 : byte_seq)
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2500 =>
    let '(x_2501, _) :=
      secret_expand (sk_2498) in 
    let x_2502 : scalar_t :=
      nat_mod_from_byte_seq_le (array_to_seq (x_2501)) : scalar_t in 
    let y_2503 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (x_2502) (b_2500) in 
    let pk_2504 : compressed_ed_point_t :=
      compress (y_2503) in 
    let encode_to_curve_salt_2505 : seq uint8 :=
      array_slice (pk_2504) (usize 0) (usize 32) in 
    bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2505) (
        alpha_2499)) (fun h_2506 => let h_string_2507 : seq uint8 :=
        encode (h_2506) in 
      let gamma_2508 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (x_2502) (h_2506) in 
      let k_2509 : scalar_t :=
        ecvrf_nonce_generation (sk_2498) (h_string_2507) in 
      let u_2510 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2509) (b_2500) in 
      let v_2511 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2509) (h_2506) in 
      let c_2512 : scalar_t :=
        ecvrf_challenge_generation (y_2503) (h_2506) (gamma_2508) (u_2510) (
          v_2511) in 
      let s_2513 : scalar_t :=
        (k_2509) +% ((c_2512) *% (x_2502)) in 
      @Ok byte_seq errorec_t (seq_slice (seq_concat (seq_concat (encode (
                gamma_2508)) (seq_slice (nat_mod_to_byte_seq_le (c_2512)) (
                usize 0) (c_len_v))) (seq_slice (nat_mod_to_byte_seq_le (
                s_2513)) (usize 0) (q_len_v))) (usize 0) (((c_len_v) + (
              q_len_v)) + (pt_len_v))))).

Definition ecvrf_proof_to_hash (pi_2514 : byte_seq) : byte_seq_result_t :=
  bind (ecvrf_decode_proof (pi_2514)) (fun '(gamma_2515, _, _) =>
    @Ok byte_seq errorec_t (array_slice (sha512 (seq_concat (seq_concat (
              array_concat (suite_string_v) (array_to_seq (three_v))) (encode (
                point_mul_by_cofactor (gamma_2515)))) (
            array_to_seq (zero_v)))) (usize 0) (usize 64))).

Definition ecvrf_verify
  (pk_2516 : public_key_t)
  (alpha_2517 : byte_seq)
  (pi_2518 : byte_seq)
  (validate_key_2519 : bool)
  : byte_seq_result_t :=
  bind (option_ok_or (decompress (base_v)) (FailedDecompression)) (fun b_2520 =>
    bind (option_ok_or (decompress (pk_2516)) (InvalidPublicKey)) (fun y_2521 =>
      ifbnd validate_key_2519 : bool
      thenbnd (bind (ecvrf_validate_key (pk_2516)) (fun _ =>
          @Ok unit errorec_t (tt)))
      else (tt) >> (fun 'tt =>
      bind (ecvrf_decode_proof (pi_2518)) (fun '(gamma_2522, c_2523, s_2524) =>
        let encode_to_curve_salt_2525 : seq uint8 :=
          array_slice (pk_2516) (usize 0) (usize 32) in 
        bind (ecvrf_encode_to_curve_h2c_suite (encode_to_curve_salt_2525) (
            alpha_2517)) (fun h_2526 => let u_2527 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2524) (b_2520)) (point_neg (point_mul (
                  c_2523) (y_2521))) in 
          let v_2528 : (
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t '×
              ed25519_field_element_t
            ) :=
            point_add (point_mul (s_2524) (h_2526)) (point_neg (point_mul (
                  c_2523) (gamma_2522))) in 
          let c_prime_2529 : scalar_t :=
            ecvrf_challenge_generation (y_2521) (h_2526) (gamma_2522) (u_2527) (
              v_2528) in 
          (if ((c_2523) =.? (c_prime_2529)):bool then (ecvrf_proof_to_hash (
                pi_2518)) else (@Err byte_seq errorec_t (FailedVerify)))))))).

