(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_P256.

Require Import Hacspec_Sha256.

Inductive error_t :=
| InvalidScalar : error_t
| InvalidSignature : error_t.

Notation "'p256_public_key_t'" := (affine_t) : hacspec_scope.

Notation "'p256_secret_key_t'" := (p256_scalar_t) : hacspec_scope.

Notation "'p256_signature_t'" := ((p256_scalar_t '× p256_scalar_t
)) : hacspec_scope.

Notation "'p256_signature_result_t'" := ((
  result p256_signature_t error_t)) : hacspec_scope.

Notation "'p256_verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'check_result_t'" := ((result unit error_t)) : hacspec_scope.

Notation "'arithmetic_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Definition check_scalar_zero (r_527 : p256_scalar_t) : check_result_t :=
  (if (nat_mod_equal (r_527) (nat_mod_zero )):bool then (@Err unit error_t (
        InvalidScalar)) else (@Ok unit error_t (tt))).

Definition ecdsa_point_mul_base (x_528 : p256_scalar_t) : arithmetic_result_t :=
  match p256_point_mul_base (x_528) with
  | Ok (s_529) => @Ok affine_t error_t (s_529)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.

Definition ecdsa_point_mul
  (k_530 : p256_scalar_t)
  (p_531 : affine_t)
  : arithmetic_result_t :=
  match p256_point_mul (k_530) (p_531) with
  | Ok (s_532) => @Ok affine_t error_t (s_532)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.

Definition ecdsa_point_add
  (p_533 : affine_t)
  (q_534 : affine_t)
  : arithmetic_result_t :=
  match point_add (p_533) (q_534) with
  | Ok (s_535) => @Ok affine_t error_t (s_535)
  | Err (_) => @Err affine_t error_t (InvalidScalar)
  end.

Definition sign
  (payload_536 : byte_seq)
  (sk_537 : p256_secret_key_t)
  (nonce_538 : p256_scalar_t)
  : p256_signature_result_t :=
  bind (check_scalar_zero (nonce_538)) (fun _ => bind (ecdsa_point_mul_base (
        nonce_538)) (fun '(k_x_539, k_y_540) => let r_541 : p256_scalar_t :=
        nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
            k_x_539)) : p256_scalar_t in 
      bind (check_scalar_zero (r_541)) (fun _ =>
        let payload_hash_542 : sha256_digest_t :=
          hash (payload_536) in 
        let payload_hash_543 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (
            array_to_seq (payload_hash_542)) : p256_scalar_t in 
        let rsk_544 : p256_scalar_t :=
          (r_541) *% (sk_537) in 
        let hash_rsk_545 : p256_scalar_t :=
          (payload_hash_543) +% (rsk_544) in 
        let nonce_inv_546 : p256_scalar_t :=
          nat_mod_inv (nonce_538) in 
        let s_547 : p256_scalar_t :=
          (nonce_inv_546) *% (hash_rsk_545) in 
        @Ok p256_signature_t error_t ((r_541, s_547))))).

Definition ecdsa_p256_sha256_sign
  (payload_548 : byte_seq)
  (sk_549 : p256_secret_key_t)
  (nonce_550 : p256_scalar_t)
  : p256_signature_result_t :=
  sign (payload_548) (sk_549) (nonce_550).

Definition verify
  (payload_551 : byte_seq)
  (pk_552 : p256_public_key_t)
  (signature_553 : p256_signature_t)
  : p256_verify_result_t :=
  let '(r_554, s_555) :=
    signature_553 in 
  let payload_hash_556 : sha256_digest_t :=
    hash (payload_551) in 
  let payload_hash_557 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (
      array_to_seq (payload_hash_556)) : p256_scalar_t in 
  let s_inv_558 : p256_scalar_t :=
    nat_mod_inv (s_555) in 
  let u1_559 : p256_scalar_t :=
    (payload_hash_557) *% (s_inv_558) in 
  bind (ecdsa_point_mul_base (u1_559)) (fun u1_560 =>
    let u2_561 : p256_scalar_t :=
      (r_554) *% (s_inv_558) in 
    bind (ecdsa_point_mul (u2_561) (pk_552)) (fun u2_562 => bind (
        ecdsa_point_add (u1_560) (u2_562)) (fun '(x_563, y_564) =>
        let x_565 : p256_scalar_t :=
          nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
              x_563)) : p256_scalar_t in 
        (if ((x_565) =.? (r_554)):bool then (@Ok unit error_t (tt)) else (
            @Err unit error_t (InvalidSignature)))))).

Definition ecdsa_p256_sha256_verify
  (payload_566 : byte_seq)
  (pk_567 : p256_public_key_t)
  (signature_568 : p256_signature_t)
  : p256_verify_result_t :=
  verify (payload_566) (pk_567) (signature_568).

