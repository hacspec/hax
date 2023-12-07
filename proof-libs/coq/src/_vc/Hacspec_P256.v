(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Inductive error_t :=
| InvalidAddition : error_t.

Definition bits_v : uint_size :=
  usize 256.

Definition field_canvas_t := nseq (int8) (32).
Definition p256_field_element_t :=
  nat_mod 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff.

Definition scalar_canvas_t := nseq (int8) (32).
Definition p256_scalar_t :=
  nat_mod 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551.

Notation "'affine_t'" := ((p256_field_element_t × p256_field_element_t
)) : hacspec_scope.

Notation "'affine_result_t'" := ((result affine_t error_t)) : hacspec_scope.

Notation "'p256_jacobian_t'" := ((
  p256_field_element_t ×
  p256_field_element_t ×
  p256_field_element_t
)) : hacspec_scope.

Notation "'jacobian_result_t'" := ((
  result p256_jacobian_t error_t)) : hacspec_scope.

Definition element_t := nseq (uint8) (usize 32).

Definition jacobian_to_affine (p_569 : p256_jacobian_t) : affine_t :=
  let '(x_570, y_571, z_572) :=
    p_569 in 
  let z2_573 : p256_field_element_t :=
    nat_mod_exp (z_572) (@repr WORDSIZE32 2) in 
  let z2i_574 : p256_field_element_t :=
    nat_mod_inv (z2_573) in 
  let z3_575 : p256_field_element_t :=
    (z_572) *% (z2_573) in 
  let z3i_576 : p256_field_element_t :=
    nat_mod_inv (z3_575) in 
  let x_577 : p256_field_element_t :=
    (x_570) *% (z2i_574) in 
  let y_578 : p256_field_element_t :=
    (y_571) *% (z3i_576) in 
  (x_577, y_578).

Definition affine_to_jacobian (p_579 : affine_t) : p256_jacobian_t :=
  let '(x_580, y_581) :=
    p_579 in 
  (
    x_580,
    y_581,
    nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 1) : p256_field_element_t
  ).

Definition point_double (p_582 : p256_jacobian_t) : p256_jacobian_t :=
  let '(x1_583, y1_584, z1_585) :=
    p_582 in 
  let delta_586 : p256_field_element_t :=
    nat_mod_exp (z1_585) (@repr WORDSIZE32 2) in 
  let gamma_587 : p256_field_element_t :=
    nat_mod_exp (y1_584) (@repr WORDSIZE32 2) in 
  let beta_588 : p256_field_element_t :=
    (x1_583) *% (gamma_587) in 
  let alpha_1_589 : p256_field_element_t :=
    (x1_583) -% (delta_586) in 
  let alpha_2_590 : p256_field_element_t :=
    (x1_583) +% (delta_586) in 
  let alpha_591 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 3) : p256_field_element_t) *% ((alpha_1_589) *% (
        alpha_2_590)) in 
  let x3_592 : p256_field_element_t :=
    (nat_mod_exp (alpha_591) (@repr WORDSIZE32 2)) -% ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 8) : p256_field_element_t) *% (beta_588)) in 
  let z3_593 : p256_field_element_t :=
    nat_mod_exp ((y1_584) +% (z1_585)) (@repr WORDSIZE32 2) in 
  let z3_594 : p256_field_element_t :=
    (z3_593) -% ((gamma_587) +% (delta_586)) in 
  let y3_1_595 : p256_field_element_t :=
    ((nat_mod_from_literal (
          0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
          @repr WORDSIZE128 4) : p256_field_element_t) *% (beta_588)) -% (
      x3_592) in 
  let y3_2_596 : p256_field_element_t :=
    (nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 8) : p256_field_element_t) *% ((gamma_587) *% (
        gamma_587)) in 
  let y3_597 : p256_field_element_t :=
    ((alpha_591) *% (y3_1_595)) -% (y3_2_596) in 
  (x3_592, y3_597, z3_594).

Definition is_point_at_infinity (p_598 : p256_jacobian_t) : bool :=
  let '(x_599, y_600, z_601) :=
    p_598 in 
  nat_mod_equal (z_601) (nat_mod_from_literal (
      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
      @repr WORDSIZE128 0) : p256_field_element_t).

Definition s1_equal_s2
  (s1_602 : p256_field_element_t)
  (s2_603 : p256_field_element_t)
  : jacobian_result_t :=
  (if (nat_mod_equal (s1_602) (s2_603)):bool then (
      @Err p256_jacobian_t error_t (InvalidAddition)) else (
      @Ok p256_jacobian_t error_t ((
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 1) : p256_field_element_t,
          nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 0) : p256_field_element_t
        )))).

Definition point_add_jacob
  (p_604 : p256_jacobian_t)
  (q_605 : p256_jacobian_t)
  : jacobian_result_t :=
  let result_606 : (result p256_jacobian_t error_t) :=
    @Ok p256_jacobian_t error_t (q_605) in 
  let '(result_606) :=
    if negb (is_point_at_infinity (p_604)):bool then (let '(result_606) :=
        if is_point_at_infinity (q_605):bool then (let result_606 :=
            @Ok p256_jacobian_t error_t (p_604) in 
          (result_606)) else (let '(x1_607, y1_608, z1_609) :=
            p_604 in 
          let '(x2_610, y2_611, z2_612) :=
            q_605 in 
          let z1z1_613 : p256_field_element_t :=
            nat_mod_exp (z1_609) (@repr WORDSIZE32 2) in 
          let z2z2_614 : p256_field_element_t :=
            nat_mod_exp (z2_612) (@repr WORDSIZE32 2) in 
          let u1_615 : p256_field_element_t :=
            (x1_607) *% (z2z2_614) in 
          let u2_616 : p256_field_element_t :=
            (x2_610) *% (z1z1_613) in 
          let s1_617 : p256_field_element_t :=
            ((y1_608) *% (z2_612)) *% (z2z2_614) in 
          let s2_618 : p256_field_element_t :=
            ((y2_611) *% (z1_609)) *% (z1z1_613) in 
          let '(result_606) :=
            if nat_mod_equal (u1_615) (u2_616):bool then (let result_606 :=
                s1_equal_s2 (s1_617) (s2_618) in 
              (result_606)) else (let h_619 : p256_field_element_t :=
                (u2_616) -% (u1_615) in 
              let i_620 : p256_field_element_t :=
                nat_mod_exp ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (h_619)) (
                  @repr WORDSIZE32 2) in 
              let j_621 : p256_field_element_t :=
                (h_619) *% (i_620) in 
              let r_622 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% ((
                    s2_618) -% (s1_617)) in 
              let v_623 : p256_field_element_t :=
                (u1_615) *% (i_620) in 
              let x3_1_624 : p256_field_element_t :=
                (nat_mod_from_literal (
                    0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                    @repr WORDSIZE128 2) : p256_field_element_t) *% (v_623) in 
              let x3_2_625 : p256_field_element_t :=
                (nat_mod_exp (r_622) (@repr WORDSIZE32 2)) -% (j_621) in 
              let x3_626 : p256_field_element_t :=
                (x3_2_625) -% (x3_1_624) in 
              let y3_1_627 : p256_field_element_t :=
                ((nat_mod_from_literal (
                      0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
                      @repr WORDSIZE128 2) : p256_field_element_t) *% (
                    s1_617)) *% (j_621) in 
              let y3_2_628 : p256_field_element_t :=
                (r_622) *% ((v_623) -% (x3_626)) in 
              let y3_629 : p256_field_element_t :=
                (y3_2_628) -% (y3_1_627) in 
              let z3_630 : p256_field_element_t :=
                nat_mod_exp ((z1_609) +% (z2_612)) (@repr WORDSIZE32 2) in 
              let z3_631 : p256_field_element_t :=
                ((z3_630) -% ((z1z1_613) +% (z2z2_614))) *% (h_619) in 
              let result_606 :=
                @Ok p256_jacobian_t error_t ((x3_626, y3_629, z3_631)) in 
              (result_606)) in 
          (result_606)) in 
      (result_606)) else ((result_606)) in 
  result_606.

Definition ltr_mul
  (k_632 : p256_scalar_t)
  (p_633 : p256_jacobian_t)
  : jacobian_result_t :=
  let q_634 : (
      p256_field_element_t ×
      p256_field_element_t ×
      p256_field_element_t
    ) :=
    (
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 1) : p256_field_element_t,
      nat_mod_from_literal (
        0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
        @repr WORDSIZE128 0) : p256_field_element_t
    ) in 
  bind (foldibnd (usize 0) to (bits_v) for q_634 >> (fun i_635 q_634 =>
    let q_634 :=
      point_double (q_634) in 
    ifbnd nat_mod_equal (nat_mod_get_bit (k_632) (((bits_v) - (usize 1)) - (
          i_635))) (nat_mod_one ) : bool
    thenbnd (bind (point_add_jacob (q_634) (p_633)) (fun q_634  => Ok ((q_634
          ))))
    else ((q_634)) >> (fun '(q_634) =>
    Ok ((q_634))))) (fun q_634 => @Ok p256_jacobian_t error_t (q_634)).

Definition p256_point_mul
  (k_636 : p256_scalar_t)
  (p_637 : affine_t)
  : affine_result_t :=
  bind (ltr_mul (k_636) (affine_to_jacobian (p_637))) (fun jac_638 =>
    @Ok affine_t error_t (jacobian_to_affine (jac_638))).

Definition p256_point_mul_base (k_639 : p256_scalar_t) : affine_result_t :=
  let base_point_640 : (p256_field_element_t × p256_field_element_t) :=
    (
      nat_mod_from_byte_seq_be (array_to_seq (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 23) : int8;
              secret (@repr WORDSIZE8 209) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 225) : int8;
              secret (@repr WORDSIZE8 44) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 71) : int8;
              secret (@repr WORDSIZE8 248) : int8;
              secret (@repr WORDSIZE8 188) : int8;
              secret (@repr WORDSIZE8 230) : int8;
              secret (@repr WORDSIZE8 229) : int8;
              secret (@repr WORDSIZE8 99) : int8;
              secret (@repr WORDSIZE8 164) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 242) : int8;
              secret (@repr WORDSIZE8 119) : int8;
              secret (@repr WORDSIZE8 3) : int8;
              secret (@repr WORDSIZE8 125) : int8;
              secret (@repr WORDSIZE8 129) : int8;
              secret (@repr WORDSIZE8 45) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 160) : int8;
              secret (@repr WORDSIZE8 244) : int8;
              secret (@repr WORDSIZE8 161) : int8;
              secret (@repr WORDSIZE8 57) : int8;
              secret (@repr WORDSIZE8 69) : int8;
              secret (@repr WORDSIZE8 216) : int8;
              secret (@repr WORDSIZE8 152) : int8;
              secret (@repr WORDSIZE8 194) : int8;
              secret (@repr WORDSIZE8 150) : int8
            ] in  l))) : p256_field_element_t,
      nat_mod_from_byte_seq_be (array_to_seq (array_from_list uint8 (let l :=
            [
              secret (@repr WORDSIZE8 79) : int8;
              secret (@repr WORDSIZE8 227) : int8;
              secret (@repr WORDSIZE8 66) : int8;
              secret (@repr WORDSIZE8 226) : int8;
              secret (@repr WORDSIZE8 254) : int8;
              secret (@repr WORDSIZE8 26) : int8;
              secret (@repr WORDSIZE8 127) : int8;
              secret (@repr WORDSIZE8 155) : int8;
              secret (@repr WORDSIZE8 142) : int8;
              secret (@repr WORDSIZE8 231) : int8;
              secret (@repr WORDSIZE8 235) : int8;
              secret (@repr WORDSIZE8 74) : int8;
              secret (@repr WORDSIZE8 124) : int8;
              secret (@repr WORDSIZE8 15) : int8;
              secret (@repr WORDSIZE8 158) : int8;
              secret (@repr WORDSIZE8 22) : int8;
              secret (@repr WORDSIZE8 43) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 51) : int8;
              secret (@repr WORDSIZE8 87) : int8;
              secret (@repr WORDSIZE8 107) : int8;
              secret (@repr WORDSIZE8 49) : int8;
              secret (@repr WORDSIZE8 94) : int8;
              secret (@repr WORDSIZE8 206) : int8;
              secret (@repr WORDSIZE8 203) : int8;
              secret (@repr WORDSIZE8 182) : int8;
              secret (@repr WORDSIZE8 64) : int8;
              secret (@repr WORDSIZE8 104) : int8;
              secret (@repr WORDSIZE8 55) : int8;
              secret (@repr WORDSIZE8 191) : int8;
              secret (@repr WORDSIZE8 81) : int8;
              secret (@repr WORDSIZE8 245) : int8
            ] in  l))) : p256_field_element_t
    ) in 
  p256_point_mul (k_639) (base_point_640).

Definition point_add_distinct
  (p_641 : affine_t)
  (q_642 : affine_t)
  : affine_result_t :=
  bind (point_add_jacob (affine_to_jacobian (p_641)) (affine_to_jacobian (
        q_642))) (fun r_643 => @Ok affine_t error_t (jacobian_to_affine (
        r_643))).

Definition point_add (p_644 : affine_t) (q_645 : affine_t) : affine_result_t :=
  (if ((p_644) !=.? (q_645)):bool then (point_add_distinct (p_644) (
        q_645)) else (@Ok affine_t error_t (jacobian_to_affine (point_double (
            affine_to_jacobian (p_644)))))).

Definition p256_validate_private_key (k_646 : byte_seq) : bool :=
  let valid_647 : bool :=
    true in 
  let k_element_648 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (k_646) : p256_scalar_t in 
  let k_element_bytes_649 : seq uint8 :=
    nat_mod_to_byte_seq_be (k_element_648) in 
  let all_zero_650 : bool :=
    true in 
  let '(valid_647, all_zero_650) :=
    foldi (usize 0) (seq_len (k_646)) (fun i_651 '(valid_647, all_zero_650) =>
      let '(all_zero_650) :=
        if negb (uint8_equal (seq_index (k_646) (i_651)) (secret (
              @repr WORDSIZE8 0) : int8)):bool then (let all_zero_650 :=
            false in 
          (all_zero_650)) else ((all_zero_650)) in 
      let '(valid_647) :=
        if negb (uint8_equal (seq_index (k_element_bytes_649) (i_651)) (
            seq_index (k_646) (i_651))):bool then (let valid_647 :=
            false in 
          (valid_647)) else ((valid_647)) in 
      (valid_647, all_zero_650))
    (valid_647, all_zero_650) in 
  (valid_647) && (negb (all_zero_650)).

Definition p256_validate_public_key (p_652 : affine_t) : bool :=
  let b_653 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 75) : int8
      ]) : p256_field_element_t in 
  let point_at_infinity_654 : bool :=
    is_point_at_infinity (affine_to_jacobian (p_652)) in 
  let '(x_655, y_656) :=
    p_652 in 
  let on_curve_657 : bool :=
    ((y_656) *% (y_656)) =.? (((((x_655) *% (x_655)) *% (x_655)) -% ((
            nat_mod_from_literal (
              0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
              @repr WORDSIZE128 3) : p256_field_element_t) *% (x_655))) +% (
        b_653)) in 
  (negb (point_at_infinity_654)) && (on_curve_657).

Definition p256_calculate_w
  (x_658 : p256_field_element_t)
  : p256_field_element_t :=
  let b_659 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 90) : int8;
        secret (@repr WORDSIZE8 198) : int8;
        secret (@repr WORDSIZE8 53) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 170) : int8;
        secret (@repr WORDSIZE8 58) : int8;
        secret (@repr WORDSIZE8 147) : int8;
        secret (@repr WORDSIZE8 231) : int8;
        secret (@repr WORDSIZE8 179) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 189) : int8;
        secret (@repr WORDSIZE8 85) : int8;
        secret (@repr WORDSIZE8 118) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 134) : int8;
        secret (@repr WORDSIZE8 188) : int8;
        secret (@repr WORDSIZE8 101) : int8;
        secret (@repr WORDSIZE8 29) : int8;
        secret (@repr WORDSIZE8 6) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 204) : int8;
        secret (@repr WORDSIZE8 83) : int8;
        secret (@repr WORDSIZE8 176) : int8;
        secret (@repr WORDSIZE8 246) : int8;
        secret (@repr WORDSIZE8 59) : int8;
        secret (@repr WORDSIZE8 206) : int8;
        secret (@repr WORDSIZE8 60) : int8;
        secret (@repr WORDSIZE8 62) : int8;
        secret (@repr WORDSIZE8 39) : int8;
        secret (@repr WORDSIZE8 210) : int8;
        secret (@repr WORDSIZE8 96) : int8;
        secret (@repr WORDSIZE8 75) : int8
      ]) : p256_field_element_t in 
  let exp_660 : p256_field_element_t :=
    nat_mod_from_byte_seq_be ([
        secret (@repr WORDSIZE8 63) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 255) : int8;
        secret (@repr WORDSIZE8 192) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8
      ]) : p256_field_element_t in 
  let z_661 : p256_field_element_t :=
    ((((x_658) *% (x_658)) *% (x_658)) -% ((nat_mod_from_literal (
            0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff) (
            @repr WORDSIZE128 3) : p256_field_element_t) *% (x_658))) +% (
      b_659) in 
  let w_662 : p256_field_element_t :=
    nat_mod_pow_felem (z_661) (exp_660) in 
  w_662.

