(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition field_canvas_t := nseq (int8) (32).
Definition x25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.

Notation "'point_t'" := ((x25519_field_element_t '× x25519_field_element_t
)) : hacspec_scope.

Definition x25519_serialized_point_t := nseq (uint8) (usize 32).

Definition x25519_serialized_scalar_t := nseq (uint8) (usize 32).

Definition mask_scalar
  (s_477 : x25519_serialized_scalar_t)
  : x25519_serialized_scalar_t :=
  let k_478 : x25519_serialized_scalar_t :=
    s_477 in 
  let k_478 :=
    array_upd k_478 (usize 0) ((array_index (k_478) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let k_478 :=
    array_upd k_478 (usize 31) ((array_index (k_478) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let k_478 :=
    array_upd k_478 (usize 31) ((array_index (k_478) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  k_478.

Definition decode_scalar (s_479 : x25519_serialized_scalar_t) : scalar_t :=
  let k_480 : x25519_serialized_scalar_t :=
    mask_scalar (s_479) in 
  nat_mod_from_byte_seq_le (array_to_seq (k_480)) : scalar_t.

Definition decode_point (u_481 : x25519_serialized_point_t) : point_t :=
  let u_482 : x25519_serialized_point_t :=
    u_481 in 
  let u_482 :=
    array_upd u_482 (usize 31) ((array_index (u_482) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  (
    nat_mod_from_byte_seq_le (array_to_seq (u_482)) : x25519_field_element_t,
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 1) : x25519_field_element_t
  ).

Definition encode_point (p_483 : point_t) : x25519_serialized_point_t :=
  let '(x_484, y_485) :=
    p_483 in 
  let b_486 : x25519_field_element_t :=
    (x_484) *% (nat_mod_inv (y_485)) in 
  array_update_start (array_new_ (default : uint8) (32)) (
    nat_mod_to_byte_seq_le (b_486)).

Definition point_add_and_double
  (q_487 : point_t)
  (np_488 : (point_t '× point_t))
  : (point_t '× point_t) :=
  let '(nq_489, nqp1_490) :=
    np_488 in 
  let '(x_1_491, z_1_492) :=
    q_487 in 
  let '(x_2_493, z_2_494) :=
    nq_489 in 
  let '(x_3_495, z_3_496) :=
    nqp1_490 in 
  let a_497 : x25519_field_element_t :=
    (x_2_493) +% (z_2_494) in 
  let aa_498 : x25519_field_element_t :=
    nat_mod_pow (a_497) (@repr WORDSIZE128 2) in 
  let b_499 : x25519_field_element_t :=
    (x_2_493) -% (z_2_494) in 
  let bb_500 : x25519_field_element_t :=
    (b_499) *% (b_499) in 
  let e_501 : x25519_field_element_t :=
    (aa_498) -% (bb_500) in 
  let c_502 : x25519_field_element_t :=
    (x_3_495) +% (z_3_496) in 
  let d_503 : x25519_field_element_t :=
    (x_3_495) -% (z_3_496) in 
  let da_504 : x25519_field_element_t :=
    (d_503) *% (a_497) in 
  let cb_505 : x25519_field_element_t :=
    (c_502) *% (b_499) in 
  let x_3_506 : x25519_field_element_t :=
    nat_mod_pow ((da_504) +% (cb_505)) (@repr WORDSIZE128 2) in 
  let z_3_507 : x25519_field_element_t :=
    (x_1_491) *% (nat_mod_pow ((da_504) -% (cb_505)) (@repr WORDSIZE128 2)) in 
  let x_2_508 : x25519_field_element_t :=
    (aa_498) *% (bb_500) in 
  let e121665_509 : x25519_field_element_t :=
    nat_mod_from_literal (
      0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
      @repr WORDSIZE128 121665) : x25519_field_element_t in 
  let z_2_510 : x25519_field_element_t :=
    (e_501) *% ((aa_498) +% ((e121665_509) *% (e_501))) in 
  ((x_2_508, z_2_510), (x_3_506, z_3_507)).

Definition swap (x_511 : (point_t '× point_t)) : (point_t '× point_t) :=
  let '(x0_512, x1_513) :=
    x_511 in 
  (x1_513, x0_512).

Definition montgomery_ladder
  (k_514 : scalar_t)
  (init_515 : point_t)
  : point_t :=
  let inf_516 : (x25519_field_element_t '× x25519_field_element_t) :=
    (
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 1) : x25519_field_element_t,
      nat_mod_from_literal (
        0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
        @repr WORDSIZE128 0) : x25519_field_element_t
    ) in 
  let acc_517 : (point_t '× point_t) :=
    (inf_516, init_515) in 
  let acc_517 :=
    foldi (usize 0) (usize 256) (fun i_518 acc_517 =>
      let '(acc_517) :=
        if nat_mod_bit (k_514) ((usize 255) - (i_518)):bool then (let acc_517 :=
            swap (acc_517) in 
          let acc_517 :=
            point_add_and_double (init_515) (acc_517) in 
          let acc_517 :=
            swap (acc_517) in 
          (acc_517)) else (let acc_517 :=
            point_add_and_double (init_515) (acc_517) in 
          (acc_517)) in 
      (acc_517))
    acc_517 in 
  let '(out_519, _) :=
    acc_517 in 
  out_519.

Definition x25519_scalarmult
  (s_520 : x25519_serialized_scalar_t)
  (p_521 : x25519_serialized_point_t)
  : x25519_serialized_point_t :=
  let s_522 : scalar_t :=
    decode_scalar (s_520) in 
  let p_523 : (x25519_field_element_t '× x25519_field_element_t) :=
    decode_point (p_521) in 
  let r_524 : (x25519_field_element_t '× x25519_field_element_t) :=
    montgomery_ladder (s_522) (p_523) in 
  encode_point (r_524).

Definition x25519_secret_to_public
  (s_525 : x25519_serialized_scalar_t)
  : x25519_serialized_point_t :=
  let base_526 : x25519_serialized_point_t :=
    array_new_ (default : uint8) (32) in 
  let base_526 :=
    array_upd base_526 (usize 0) (secret (@repr WORDSIZE8 9) : int8) in 
  x25519_scalarmult (s_525) (base_526).

