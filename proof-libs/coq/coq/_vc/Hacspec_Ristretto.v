(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Notation "'ristretto_point_t'" := ((
  field_element_t '×
  field_element_t '×
  field_element_t '×
  field_element_t
)) : hacspec_scope.

Notation "'decode_result_t'" := ((
  result ristretto_point_t int8)) : hacspec_scope.

Definition ristretto_point_encoded_t := nseq (uint8) (usize 32).

Definition byte_string_t := nseq (uint8) (usize 64).

Definition field_canvas_t := nseq (int8) (32).
Definition field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition decoding_error_v : int8 :=
  @repr WORDSIZE8 20.

Definition p  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 127) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 237) : int8
    ]) : field_element_t.

Definition d  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 82) : int8;
      secret (@repr WORDSIZE8 3) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 238) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 111) : int8;
      secret (@repr WORDSIZE8 254) : int8;
      secret (@repr WORDSIZE8 115) : int8;
      secret (@repr WORDSIZE8 140) : int8;
      secret (@repr WORDSIZE8 199) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 121) : int8;
      secret (@repr WORDSIZE8 119) : int8;
      secret (@repr WORDSIZE8 121) : int8;
      secret (@repr WORDSIZE8 232) : int8;
      secret (@repr WORDSIZE8 152) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 112) : int8;
      secret (@repr WORDSIZE8 10) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 216) : int8;
      secret (@repr WORDSIZE8 171) : int8;
      secret (@repr WORDSIZE8 117) : int8;
      secret (@repr WORDSIZE8 235) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 202) : int8;
      secret (@repr WORDSIZE8 19) : int8;
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 163) : int8
    ]) : field_element_t.

Definition sqrt_m1  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 131) : int8;
      secret (@repr WORDSIZE8 36) : int8;
      secret (@repr WORDSIZE8 128) : int8;
      secret (@repr WORDSIZE8 79) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 223) : int8;
      secret (@repr WORDSIZE8 11) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 61) : int8;
      secret (@repr WORDSIZE8 251) : int8;
      secret (@repr WORDSIZE8 215) : int8;
      secret (@repr WORDSIZE8 167) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 67) : int8;
      secret (@repr WORDSIZE8 24) : int8;
      secret (@repr WORDSIZE8 6) : int8;
      secret (@repr WORDSIZE8 173) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 228) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 196) : int8;
      secret (@repr WORDSIZE8 238) : int8;
      secret (@repr WORDSIZE8 27) : int8;
      secret (@repr WORDSIZE8 39) : int8;
      secret (@repr WORDSIZE8 74) : int8;
      secret (@repr WORDSIZE8 14) : int8;
      secret (@repr WORDSIZE8 160) : int8;
      secret (@repr WORDSIZE8 176) : int8
    ]) : field_element_t.

Definition invsqrt_a_minus_d  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 137) : int8;
      secret (@repr WORDSIZE8 5) : int8;
      secret (@repr WORDSIZE8 207) : int8;
      secret (@repr WORDSIZE8 175) : int8;
      secret (@repr WORDSIZE8 252) : int8;
      secret (@repr WORDSIZE8 162) : int8;
      secret (@repr WORDSIZE8 22) : int8;
      secret (@repr WORDSIZE8 194) : int8;
      secret (@repr WORDSIZE8 123) : int8;
      secret (@repr WORDSIZE8 145) : int8;
      secret (@repr WORDSIZE8 254) : int8;
      secret (@repr WORDSIZE8 1) : int8;
      secret (@repr WORDSIZE8 216) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 157) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 22) : int8;
      secret (@repr WORDSIZE8 23) : int8;
      secret (@repr WORDSIZE8 90) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 114) : int8;
      secret (@repr WORDSIZE8 190) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 200) : int8;
      secret (@repr WORDSIZE8 253) : int8;
      secret (@repr WORDSIZE8 170) : int8;
      secret (@repr WORDSIZE8 128) : int8;
      secret (@repr WORDSIZE8 93) : int8;
      secret (@repr WORDSIZE8 64) : int8;
      secret (@repr WORDSIZE8 234) : int8
    ]) : field_element_t.

Definition sqrt_ad_minus_one  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 55) : int8;
      secret (@repr WORDSIZE8 105) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 191) : int8;
      secret (@repr WORDSIZE8 43) : int8;
      secret (@repr WORDSIZE8 131) : int8;
      secret (@repr WORDSIZE8 72) : int8;
      secret (@repr WORDSIZE8 172) : int8;
      secret (@repr WORDSIZE8 15) : int8;
      secret (@repr WORDSIZE8 60) : int8;
      secret (@repr WORDSIZE8 252) : int8;
      secret (@repr WORDSIZE8 201) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 245) : int8;
      secret (@repr WORDSIZE8 209) : int8;
      secret (@repr WORDSIZE8 253) : int8;
      secret (@repr WORDSIZE8 175) : int8;
      secret (@repr WORDSIZE8 157) : int8;
      secret (@repr WORDSIZE8 142) : int8;
      secret (@repr WORDSIZE8 12) : int8;
      secret (@repr WORDSIZE8 27) : int8;
      secret (@repr WORDSIZE8 120) : int8;
      secret (@repr WORDSIZE8 84) : int8;
      secret (@repr WORDSIZE8 189) : int8;
      secret (@repr WORDSIZE8 126) : int8;
      secret (@repr WORDSIZE8 151) : int8;
      secret (@repr WORDSIZE8 246) : int8;
      secret (@repr WORDSIZE8 160) : int8;
      secret (@repr WORDSIZE8 73) : int8;
      secret (@repr WORDSIZE8 123) : int8;
      secret (@repr WORDSIZE8 46) : int8;
      secret (@repr WORDSIZE8 27) : int8
    ]) : field_element_t.

Definition one_minus_d_sq  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 2) : int8;
      secret (@repr WORDSIZE8 144) : int8;
      secret (@repr WORDSIZE8 114) : int8;
      secret (@repr WORDSIZE8 168) : int8;
      secret (@repr WORDSIZE8 178) : int8;
      secret (@repr WORDSIZE8 179) : int8;
      secret (@repr WORDSIZE8 224) : int8;
      secret (@repr WORDSIZE8 215) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 148) : int8;
      secret (@repr WORDSIZE8 171) : int8;
      secret (@repr WORDSIZE8 221) : int8;
      secret (@repr WORDSIZE8 190) : int8;
      secret (@repr WORDSIZE8 112) : int8;
      secret (@repr WORDSIZE8 223) : int8;
      secret (@repr WORDSIZE8 228) : int8;
      secret (@repr WORDSIZE8 44) : int8;
      secret (@repr WORDSIZE8 129) : int8;
      secret (@repr WORDSIZE8 161) : int8;
      secret (@repr WORDSIZE8 56) : int8;
      secret (@repr WORDSIZE8 205) : int8;
      secret (@repr WORDSIZE8 94) : int8;
      secret (@repr WORDSIZE8 53) : int8;
      secret (@repr WORDSIZE8 15) : int8;
      secret (@repr WORDSIZE8 226) : int8;
      secret (@repr WORDSIZE8 124) : int8;
      secret (@repr WORDSIZE8 9) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 148) : int8;
      secret (@repr WORDSIZE8 95) : int8;
      secret (@repr WORDSIZE8 193) : int8;
      secret (@repr WORDSIZE8 118) : int8
    ]) : field_element_t.

Definition d_minus_one_sq  : field_element_t :=
  nat_mod_from_byte_seq_be ([
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 104) : int8;
      secret (@repr WORDSIZE8 179) : int8;
      secret (@repr WORDSIZE8 122) : int8;
      secret (@repr WORDSIZE8 246) : int8;
      secret (@repr WORDSIZE8 108) : int8;
      secret (@repr WORDSIZE8 34) : int8;
      secret (@repr WORDSIZE8 65) : int8;
      secret (@repr WORDSIZE8 76) : int8;
      secret (@repr WORDSIZE8 220) : int8;
      secret (@repr WORDSIZE8 211) : int8;
      secret (@repr WORDSIZE8 47) : int8;
      secret (@repr WORDSIZE8 82) : int8;
      secret (@repr WORDSIZE8 155) : int8;
      secret (@repr WORDSIZE8 78) : int8;
      secret (@repr WORDSIZE8 235) : int8;
      secret (@repr WORDSIZE8 210) : int8;
      secret (@repr WORDSIZE8 158) : int8;
      secret (@repr WORDSIZE8 74) : int8;
      secret (@repr WORDSIZE8 44) : int8;
      secret (@repr WORDSIZE8 176) : int8;
      secret (@repr WORDSIZE8 30) : int8;
      secret (@repr WORDSIZE8 25) : int8;
      secret (@repr WORDSIZE8 153) : int8;
      secret (@repr WORDSIZE8 49) : int8;
      secret (@repr WORDSIZE8 173) : int8;
      secret (@repr WORDSIZE8 90) : int8;
      secret (@repr WORDSIZE8 170) : int8;
      secret (@repr WORDSIZE8 68) : int8;
      secret (@repr WORDSIZE8 237) : int8;
      secret (@repr WORDSIZE8 77) : int8;
      secret (@repr WORDSIZE8 32) : int8
    ]) : field_element_t.

Definition base_point_encoded  : ristretto_point_encoded_t :=
  array_from_seq (32) ([
      secret (@repr WORDSIZE8 226) : int8;
      secret (@repr WORDSIZE8 242) : int8;
      secret (@repr WORDSIZE8 174) : int8;
      secret (@repr WORDSIZE8 10) : int8;
      secret (@repr WORDSIZE8 106) : int8;
      secret (@repr WORDSIZE8 188) : int8;
      secret (@repr WORDSIZE8 78) : int8;
      secret (@repr WORDSIZE8 113) : int8;
      secret (@repr WORDSIZE8 168) : int8;
      secret (@repr WORDSIZE8 132) : int8;
      secret (@repr WORDSIZE8 169) : int8;
      secret (@repr WORDSIZE8 97) : int8;
      secret (@repr WORDSIZE8 197) : int8;
      secret (@repr WORDSIZE8 0) : int8;
      secret (@repr WORDSIZE8 81) : int8;
      secret (@repr WORDSIZE8 95) : int8;
      secret (@repr WORDSIZE8 88) : int8;
      secret (@repr WORDSIZE8 227) : int8;
      secret (@repr WORDSIZE8 11) : int8;
      secret (@repr WORDSIZE8 106) : int8;
      secret (@repr WORDSIZE8 165) : int8;
      secret (@repr WORDSIZE8 130) : int8;
      secret (@repr WORDSIZE8 221) : int8;
      secret (@repr WORDSIZE8 141) : int8;
      secret (@repr WORDSIZE8 182) : int8;
      secret (@repr WORDSIZE8 166) : int8;
      secret (@repr WORDSIZE8 89) : int8;
      secret (@repr WORDSIZE8 69) : int8;
      secret (@repr WORDSIZE8 224) : int8;
      secret (@repr WORDSIZE8 141) : int8;
      secret (@repr WORDSIZE8 45) : int8;
      secret (@repr WORDSIZE8 118) : int8
    ]).

Definition base_point  : ristretto_point_t :=
  result_unwrap (decode (base_point_encoded )).

Definition identity_point  : ristretto_point_t :=
  (fe (usize 0), fe (usize 1), fe (usize 1), fe (usize 0)).

Definition fe (x_740 : uint_size) : field_element_t :=
  nat_mod_from_literal (
    0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed) (
    pub_u128 (x_740)) : field_element_t.

Definition geq_p (x_741 : seq uint8) : bool :=
  let p_seq_742 : seq uint8 :=
    [
      secret (@repr WORDSIZE8 237) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 255) : int8;
      secret (@repr WORDSIZE8 127) : int8
    ] in 
  let res_743 : bool :=
    true in 
  let res_743 :=
    foldi (usize 0) (seq_len (p_seq_742)) (fun index_744 res_743 =>
      let x_index_745 : int8 :=
        uint8_declassify (seq_index (x_741) (index_744)) in 
      let p_index_746 : int8 :=
        uint8_declassify (seq_index (p_seq_742) (index_744)) in 
      let '(res_743) :=
        if (x_index_745) !=.? (p_index_746):bool then (let res_743 :=
            (x_index_745) >.? (p_index_746) in 
          (res_743)) else ((res_743)) in 
      (res_743))
    res_743 in 
  res_743.

Definition is_negative (e_747 : field_element_t) : bool :=
  ((e_747) rem (fe (usize 2))) =.? (fe (usize 1)).

Definition eq (u_748 : field_element_t) (v_749 : field_element_t) : bool :=
  (u_748) =.? (v_749).

Definition select
  (u_750 : field_element_t)
  (cond_751 : bool)
  (v_752 : field_element_t)
  : field_element_t :=
  (if (cond_751):bool then (u_750) else (v_752)).

Definition neg_fe (u_753 : field_element_t) : field_element_t :=
  (fe (usize 0)) -% (u_753).

Definition abs (u_754 : field_element_t) : field_element_t :=
  select (neg_fe (u_754)) (is_negative (u_754)) (u_754).

Definition sqrt_ratio_m1
  (u_755 : field_element_t)
  (v_756 : field_element_t)
  : (bool '× field_element_t) :=
  let v3_757 : field_element_t :=
    (nat_mod_pow (v_756) (@repr WORDSIZE128 2)) *% (v_756) in 
  let v7_758 : field_element_t :=
    (nat_mod_pow (v3_757) (@repr WORDSIZE128 2)) *% (v_756) in 
  let r_759 : field_element_t :=
    ((u_755) *% (v3_757)) *% (nat_mod_pow_felem ((u_755) *% (v7_758)) (((
            p ) -% (fe (usize 5))) /% (fe (usize 8)))) in 
  let check_760 : field_element_t :=
    (v_756) *% (nat_mod_pow (r_759) (@repr WORDSIZE128 2)) in 
  let correct_sign_sqrt_761 : bool :=
    eq (check_760) (u_755) in 
  let flipped_sign_sqrt_762 : bool :=
    eq (check_760) (neg_fe (u_755)) in 
  let flipped_sign_sqrt_i_763 : bool :=
    eq (check_760) ((neg_fe (u_755)) *% (sqrt_m1 )) in 
  let r_prime_764 : field_element_t :=
    (sqrt_m1 ) *% (r_759) in 
  let r_759 :=
    select (r_prime_764) ((flipped_sign_sqrt_762) || (
        flipped_sign_sqrt_i_763)) (r_759) in 
  let r_759 :=
    abs (r_759) in 
  let was_square_765 : bool :=
    (correct_sign_sqrt_761) || (flipped_sign_sqrt_762) in 
  (was_square_765, r_759).

Definition map (t_766 : field_element_t) : ristretto_point_t :=
  let one_767 : field_element_t :=
    fe (usize 1) in 
  let minus_one_768 : field_element_t :=
    neg_fe (one_767) in 
  let r_769 : field_element_t :=
    (sqrt_m1 ) *% (nat_mod_pow (t_766) (@repr WORDSIZE128 2)) in 
  let u_770 : field_element_t :=
    ((r_769) +% (one_767)) *% (one_minus_d_sq ) in 
  let v_771 : field_element_t :=
    ((minus_one_768) -% ((r_769) *% (d ))) *% ((r_769) +% (d )) in 
  let '(was_square_772, s_773) :=
    sqrt_ratio_m1 (u_770) (v_771) in 
  let s_prime_774 : field_element_t :=
    neg_fe (abs ((s_773) *% (t_766))) in 
  let s_773 :=
    select (s_773) (was_square_772) (s_prime_774) in 
  let c_775 : field_element_t :=
    select (minus_one_768) (was_square_772) (r_769) in 
  let n_776 : field_element_t :=
    (((c_775) *% ((r_769) -% (one_767))) *% (d_minus_one_sq )) -% (v_771) in 
  let w0_777 : field_element_t :=
    ((fe (usize 2)) *% (s_773)) *% (v_771) in 
  let w1_778 : field_element_t :=
    (n_776) *% (sqrt_ad_minus_one ) in 
  let w2_779 : field_element_t :=
    (one_767) -% (nat_mod_pow (s_773) (@repr WORDSIZE128 2)) in 
  let w3_780 : field_element_t :=
    (one_767) +% (nat_mod_pow (s_773) (@repr WORDSIZE128 2)) in 
  (
    (w0_777) *% (w3_780),
    (w2_779) *% (w1_778),
    (w1_778) *% (w3_780),
    (w0_777) *% (w2_779)
  ).

Definition one_way_map (b_781 : byte_string_t) : ristretto_point_t :=
  let r0_bytes_782 : seq uint8 :=
    array_slice (b_781) (usize 0) (usize 32) in 
  let r1_bytes_783 : seq uint8 :=
    array_slice (b_781) (usize 32) (usize 32) in 
  let r0_bytes_784 : seq int8 :=
    seq_declassify (r0_bytes_782) in 
  let r1_bytes_785 : seq int8 :=
    seq_declassify (r1_bytes_783) in 
  let r0_bytes_784 :=
    seq_upd r0_bytes_784 (usize 31) ((seq_index (r0_bytes_784) (usize 31)) .% (
        @repr WORDSIZE8 128)) in 
  let r1_bytes_785 :=
    seq_upd r1_bytes_785 (usize 31) ((seq_index (r1_bytes_785) (usize 31)) .% (
        @repr WORDSIZE8 128)) in 
  let r0_786 : field_element_t :=
    nat_mod_from_public_byte_seq_le (r0_bytes_784) in 
  let r1_787 : field_element_t :=
    nat_mod_from_public_byte_seq_le (r1_bytes_785) in 
  let p1_788 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    map (r0_786) in 
  let p2_789 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    map (r1_787) in 
  add (p1_788) (p2_789).

Definition encode (u_790 : ristretto_point_t) : ristretto_point_encoded_t :=
  let '(x0_791, y0_792, z0_793, t0_794) :=
    u_790 in 
  let u1_795 : field_element_t :=
    ((z0_793) +% (y0_792)) *% ((z0_793) -% (y0_792)) in 
  let u2_796 : field_element_t :=
    (x0_791) *% (y0_792) in 
  let '(_, invsqrt_797) :=
    sqrt_ratio_m1 (fe (usize 1)) ((u1_795) *% (nat_mod_pow (u2_796) (
          @repr WORDSIZE128 2))) in 
  let den1_798 : field_element_t :=
    (invsqrt_797) *% (u1_795) in 
  let den2_799 : field_element_t :=
    (invsqrt_797) *% (u2_796) in 
  let z_inv_800 : field_element_t :=
    ((den1_798) *% (den2_799)) *% (t0_794) in 
  let ix0_801 : field_element_t :=
    (x0_791) *% (sqrt_m1 ) in 
  let iy0_802 : field_element_t :=
    (y0_792) *% (sqrt_m1 ) in 
  let enchanted_denominator_803 : field_element_t :=
    (den1_798) *% (invsqrt_a_minus_d ) in 
  let rotate_804 : bool :=
    is_negative ((t0_794) *% (z_inv_800)) in 
  let x_805 : field_element_t :=
    select (iy0_802) (rotate_804) (x0_791) in 
  let y_806 : field_element_t :=
    select (ix0_801) (rotate_804) (y0_792) in 
  let z_807 : field_element_t :=
    z0_793 in 
  let den_inv_808 : field_element_t :=
    select (enchanted_denominator_803) (rotate_804) (den2_799) in 
  let y_806 :=
    select (neg_fe (y_806)) (is_negative ((x_805) *% (z_inv_800))) (y_806) in 
  let s_809 : field_element_t :=
    abs ((den_inv_808) *% ((z_807) -% (y_806))) in 
  array_update_start (array_new_ (default : uint8) (32)) (
    nat_mod_to_byte_seq_le (s_809)).

Definition decode (u_810 : ristretto_point_encoded_t) : decode_result_t :=
  let ret_811 : (result ristretto_point_t int8) :=
    @Err ristretto_point_t int8 (decoding_error_v) in 
  let s_812 : field_element_t :=
    nat_mod_from_byte_seq_le (array_to_seq (u_810)) : field_element_t in 
  let '(ret_811) :=
    if (negb (geq_p (array_to_le_bytes (u_810)))) && (negb (is_negative (
          s_812))):bool then (let one_813 : field_element_t :=
        fe (usize 1) in 
      let ss_814 : field_element_t :=
        nat_mod_pow (s_812) (@repr WORDSIZE128 2) in 
      let u1_815 : field_element_t :=
        (one_813) -% (ss_814) in 
      let u2_816 : field_element_t :=
        (one_813) +% (ss_814) in 
      let u2_sqr_817 : field_element_t :=
        nat_mod_pow (u2_816) (@repr WORDSIZE128 2) in 
      let v_818 : field_element_t :=
        (neg_fe ((d ) *% (nat_mod_pow (u1_815) (@repr WORDSIZE128 2)))) -% (
          u2_sqr_817) in 
      let '(was_square_819, invsqrt_820) :=
        sqrt_ratio_m1 (one_813) ((v_818) *% (u2_sqr_817)) in 
      let den_x_821 : field_element_t :=
        (invsqrt_820) *% (u2_816) in 
      let den_y_822 : field_element_t :=
        ((invsqrt_820) *% (den_x_821)) *% (v_818) in 
      let x_823 : field_element_t :=
        abs (((s_812) +% (s_812)) *% (den_x_821)) in 
      let y_824 : field_element_t :=
        (u1_815) *% (den_y_822) in 
      let t_825 : field_element_t :=
        (x_823) *% (y_824) in 
      let '(ret_811) :=
        if negb (((negb (was_square_819)) || (is_negative (t_825))) || ((
              y_824) =.? (fe (usize 0)))):bool then (let ret_811 :=
            @Ok ristretto_point_t int8 ((x_823, y_824, one_813, t_825)) in 
          (ret_811)) else ((ret_811)) in 
      (ret_811)) else ((ret_811)) in 
  ret_811.

Definition equals
  (u_826 : ristretto_point_t)
  (v_827 : ristretto_point_t)
  : bool :=
  let '(x1_828, y1_829, _, _) :=
    u_826 in 
  let '(x2_830, y2_831, _, _) :=
    v_827 in 
  (((x1_828) *% (y2_831)) =.? ((x2_830) *% (y1_829))) || (((y1_829) *% (
        y2_831)) =.? ((x1_828) *% (x2_830))).

Definition add
  (u_832 : ristretto_point_t)
  (v_833 : ristretto_point_t)
  : ristretto_point_t :=
  let '(x1_834, y1_835, z1_836, t1_837) :=
    u_832 in 
  let '(x2_838, y2_839, z2_840, t2_841) :=
    v_833 in 
  let a_842 : field_element_t :=
    ((y1_835) -% (x1_834)) *% ((y2_839) +% (x2_838)) in 
  let b_843 : field_element_t :=
    ((y1_835) +% (x1_834)) *% ((y2_839) -% (x2_838)) in 
  let c_844 : field_element_t :=
    ((fe (usize 2)) *% (z1_836)) *% (t2_841) in 
  let d_845 : field_element_t :=
    ((fe (usize 2)) *% (t1_837)) *% (z2_840) in 
  let e_846 : field_element_t :=
    (d_845) +% (c_844) in 
  let f_847 : field_element_t :=
    (b_843) -% (a_842) in 
  let g_848 : field_element_t :=
    (b_843) +% (a_842) in 
  let h_849 : field_element_t :=
    (d_845) -% (c_844) in 
  let x3_850 : field_element_t :=
    (e_846) *% (f_847) in 
  let y3_851 : field_element_t :=
    (g_848) *% (h_849) in 
  let t3_852 : field_element_t :=
    (e_846) *% (h_849) in 
  let z3_853 : field_element_t :=
    (f_847) *% (g_848) in 
  (x3_850, y3_851, z3_853, t3_852).

Definition neg (u_854 : ristretto_point_t) : ristretto_point_t :=
  let '(x1_855, y1_856, z1_857, t1_858) :=
    u_854 in 
  (neg_fe (x1_855), y1_856, neg_fe (z1_857), t1_858).

Definition sub
  (u_859 : ristretto_point_t)
  (v_860 : ristretto_point_t)
  : ristretto_point_t :=
  add (u_859) (neg (v_860)).

Definition double (u_861 : ristretto_point_t) : ristretto_point_t :=
  let '(x1_862, y1_863, z1_864, _) :=
    u_861 in 
  let a_865 : field_element_t :=
    nat_mod_pow (x1_862) (@repr WORDSIZE128 2) in 
  let b_866 : field_element_t :=
    nat_mod_pow (y1_863) (@repr WORDSIZE128 2) in 
  let c_867 : field_element_t :=
    (fe (usize 2)) *% (nat_mod_pow (z1_864) (@repr WORDSIZE128 2)) in 
  let h_868 : field_element_t :=
    (a_865) +% (b_866) in 
  let e_869 : field_element_t :=
    (h_868) -% (nat_mod_pow ((x1_862) +% (y1_863)) (@repr WORDSIZE128 2)) in 
  let g_870 : field_element_t :=
    (a_865) -% (b_866) in 
  let f_871 : field_element_t :=
    (c_867) +% (g_870) in 
  let x2_872 : field_element_t :=
    (e_869) *% (f_871) in 
  let y2_873 : field_element_t :=
    (g_870) *% (h_868) in 
  let t2_874 : field_element_t :=
    (e_869) *% (h_868) in 
  let z2_875 : field_element_t :=
    (f_871) *% (g_870) in 
  (x2_872, y2_873, z2_875, t2_874).

Definition mul
  (k_876 : scalar_t)
  (p_877 : ristretto_point_t)
  : ristretto_point_t :=
  let res_878 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    identity_point  in 
  let temp_879 : (
      field_element_t '×
      field_element_t '×
      field_element_t '×
      field_element_t
    ) :=
    p_877 in 
  let '(res_878, temp_879) :=
    foldi (usize 0) (usize 256) (fun i_880 '(res_878, temp_879) =>
      let '(res_878) :=
        if (nat_mod_get_bit (k_876) (i_880)) =.? (nat_mod_from_literal (
            0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed) (
            @repr WORDSIZE128 1) : scalar_t):bool then (let res_878 :=
            add (res_878) (temp_879) in 
          (res_878)) else ((res_878)) in 
      let temp_879 :=
        double (temp_879) in 
      (res_878, temp_879))
    (res_878, temp_879) in 
  res_878.

