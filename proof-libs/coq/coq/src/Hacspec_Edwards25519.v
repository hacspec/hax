(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Definition field_canvas_t := nseq (int8) (32).
Definition ed25519_field_element_t :=
  nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_scalar_canvas_t := nseq (int8) (64).
Definition big_scalar_t :=
  nat_mod 0x1000000000000000000000000000000014def9dea2f79cd65812631a5cf5d3ed.

Definition big_integer_canvas_t := nseq (int8) (32).
Definition big_integer_t :=
  nat_mod 0x8000000000000000000000000000000080000000000000000000000000000000.

Notation "'ed_point_t'" := ((
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t '×
  ed25519_field_element_t
)) : hacspec_scope.

Definition compressed_ed_point_t := nseq (uint8) (usize 32).

Definition serialized_scalar_t := nseq (uint8) (usize 32).

Definition signature_t := nseq (uint8) (usize 64).

Notation "'public_key_t'" := (compressed_ed_point_t) : hacspec_scope.

Notation "'secret_key_t'" := (serialized_scalar_t) : hacspec_scope.

Inductive error_t :=
| InvalidPublickey : error_t
| InvalidSignature : error_t
| InvalidS : error_t
| InvalidR : error_t
| SmallOrderPoint : error_t
| NotEnoughRandomness : error_t.

Notation "'verify_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition base_v : compressed_ed_point_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8;
        secret (@repr WORDSIZE8 102) : int8
      ] in  l).

Definition constant_p_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
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
      ] in  l).

Definition constant_l_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 237) : int8;
        secret (@repr WORDSIZE8 211) : int8;
        secret (@repr WORDSIZE8 245) : int8;
        secret (@repr WORDSIZE8 92) : int8;
        secret (@repr WORDSIZE8 26) : int8;
        secret (@repr WORDSIZE8 99) : int8;
        secret (@repr WORDSIZE8 18) : int8;
        secret (@repr WORDSIZE8 88) : int8;
        secret (@repr WORDSIZE8 214) : int8;
        secret (@repr WORDSIZE8 156) : int8;
        secret (@repr WORDSIZE8 247) : int8;
        secret (@repr WORDSIZE8 162) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 249) : int8;
        secret (@repr WORDSIZE8 222) : int8;
        secret (@repr WORDSIZE8 20) : int8;
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
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 16) : int8
      ] in  l).

Definition constant_p3_8_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 254) : int8;
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
        secret (@repr WORDSIZE8 15) : int8
      ] in  l).

Definition constant_p1_4_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 251) : int8;
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
        secret (@repr WORDSIZE8 31) : int8
      ] in  l).

Definition constant_d_v : serialized_scalar_t :=
  array_from_list uint8 (let l :=
      [
        secret (@repr WORDSIZE8 163) : int8;
        secret (@repr WORDSIZE8 120) : int8;
        secret (@repr WORDSIZE8 89) : int8;
        secret (@repr WORDSIZE8 19) : int8;
        secret (@repr WORDSIZE8 202) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 235) : int8;
        secret (@repr WORDSIZE8 117) : int8;
        secret (@repr WORDSIZE8 171) : int8;
        secret (@repr WORDSIZE8 216) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 65) : int8;
        secret (@repr WORDSIZE8 77) : int8;
        secret (@repr WORDSIZE8 10) : int8;
        secret (@repr WORDSIZE8 112) : int8;
        secret (@repr WORDSIZE8 0) : int8;
        secret (@repr WORDSIZE8 152) : int8;
        secret (@repr WORDSIZE8 232) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 119) : int8;
        secret (@repr WORDSIZE8 121) : int8;
        secret (@repr WORDSIZE8 64) : int8;
        secret (@repr WORDSIZE8 199) : int8;
        secret (@repr WORDSIZE8 140) : int8;
        secret (@repr WORDSIZE8 115) : int8;
        secret (@repr WORDSIZE8 254) : int8;
        secret (@repr WORDSIZE8 111) : int8;
        secret (@repr WORDSIZE8 43) : int8;
        secret (@repr WORDSIZE8 238) : int8;
        secret (@repr WORDSIZE8 108) : int8;
        secret (@repr WORDSIZE8 3) : int8;
        secret (@repr WORDSIZE8 82) : int8
      ] in  l).

Definition is_negative (x_2125 : ed25519_field_element_t) : uint8 :=
  (if (nat_mod_bit (x_2125) (usize 0)):bool then (secret (
        @repr WORDSIZE8 1) : int8) else (secret (@repr WORDSIZE8 0) : int8)).

Definition compress (p_2126 : ed_point_t) : compressed_ed_point_t :=
  let '(x_2127, y_2128, z_2129, _) :=
    p_2126 in 
  let z_inv_2130 : ed25519_field_element_t :=
    nat_mod_inv (z_2129) in 
  let x_2131 : ed25519_field_element_t :=
    (x_2127) *% (z_inv_2130) in 
  let y_2132 : ed25519_field_element_t :=
    (y_2128) *% (z_inv_2130) in 
  let s_2133 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2132) in 
  let s_2133 :=
    seq_upd s_2133 (usize 31) ((seq_index (s_2133) (usize 31)) .^ ((
          is_negative (x_2131)) shift_left (usize 7))) in 
  array_from_slice (default : uint8) (32) (s_2133) (usize 0) (usize 32).

Definition sqrt
  (a_2134 : ed25519_field_element_t)
  : (option ed25519_field_element_t) :=
  let p3_8_2135 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p3_8_v)) : ed25519_field_element_t in 
  let p1_4_2136 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_p1_4_v)) : ed25519_field_element_t in 
  let x_c_2137 : ed25519_field_element_t :=
    nat_mod_pow_self (a_2134) (p3_8_2135) in 
  let result_2138 : (option ed25519_field_element_t) :=
    @None ed25519_field_element_t in 
  let '(result_2138) :=
    if ((x_c_2137) *% (x_c_2137)) =.? (a_2134):bool then (let result_2138 :=
        some (x_c_2137) in 
      (result_2138)) else ((result_2138)) in 
  let '(result_2138) :=
    if ((x_c_2137) *% (x_c_2137)) =.? ((nat_mod_zero ) -% (a_2134)):bool then (
      let x_2139 : ed25519_field_element_t :=
        (nat_mod_pow_self (nat_mod_two ) (p1_4_2136)) *% (x_c_2137) in 
      let result_2138 :=
        some (x_2139) in 
      (result_2138)) else ((result_2138)) in 
  result_2138.

Definition check_canonical_point (x_2140 : compressed_ed_point_t) : bool :=
  let x_2140 :=
    array_upd x_2140 (usize 31) ((array_index (x_2140) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let x_2141 : big_integer_t :=
    nat_mod_from_byte_seq_le (array_to_seq (x_2140)) : big_integer_t in 
  (x_2141) <.? (nat_mod_from_byte_seq_le (
      array_to_seq (constant_p_v)) : big_integer_t).

Definition decompress (q_2142 : compressed_ed_point_t) : (option ed_point_t) :=
  let d_2143 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2144 : uint8 :=
    ((array_index (q_2142) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2145 : compressed_ed_point_t :=
    q_2142 in 
  let y_s_2145 :=
    array_upd y_s_2145 (usize 31) ((array_index (y_s_2145) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  ifbnd negb (check_canonical_point (y_s_2145)) : bool
  thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
  else (tt) >> (fun 'tt =>
  let y_2146 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2145)) : ed25519_field_element_t in 
  let z_2147 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2148 : ed25519_field_element_t :=
    (y_2146) *% (y_2146) in 
  let u_2149 : ed25519_field_element_t :=
    (yy_2148) -% (z_2147) in 
  let v_2150 : ed25519_field_element_t :=
    ((d_2143) *% (yy_2148)) +% (z_2147) in 
  let xx_2151 : ed25519_field_element_t :=
    (u_2149) *% (nat_mod_inv (v_2150)) in 
  bind (sqrt (xx_2151)) (fun x_2152 => let x_r_2153 : uint8 :=
      is_negative (x_2152) in 
    ifbnd ((x_2152) =.? (nat_mod_zero )) && ((uint8_declassify (x_s_2144)) =.? (
        @repr WORDSIZE8 1)) : bool
    thenbnd (bind (@None ed_point_t) (fun _ => @Some unit (tt)))
    else (tt) >> (fun 'tt =>
    let '(x_2152) :=
      if (uint8_declassify (x_r_2153)) !=.? (uint8_declassify (
          x_s_2144)):bool then (let x_2152 :=
          (nat_mod_zero ) -% (x_2152) in 
        (x_2152)) else ((x_2152)) in 
    some ((x_2152, y_2146, z_2147, (x_2152) *% (y_2146)))))).

Definition decompress_non_canonical
  (p_2154 : compressed_ed_point_t)
  : (option ed_point_t) :=
  let d_2155 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let x_s_2156 : uint8 :=
    ((array_index (p_2154) (usize 31)) .& (secret (
          @repr WORDSIZE8 128) : int8)) shift_right (usize 7) in 
  let y_s_2157 : compressed_ed_point_t :=
    p_2154 in 
  let y_s_2157 :=
    array_upd y_s_2157 (usize 31) ((array_index (y_s_2157) (usize 31)) .& (
        secret (@repr WORDSIZE8 127) : int8)) in 
  let y_2158 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (y_s_2157)) : ed25519_field_element_t in 
  let z_2159 : ed25519_field_element_t :=
    nat_mod_one  in 
  let yy_2160 : ed25519_field_element_t :=
    (y_2158) *% (y_2158) in 
  let u_2161 : ed25519_field_element_t :=
    (yy_2160) -% (z_2159) in 
  let v_2162 : ed25519_field_element_t :=
    ((d_2155) *% (yy_2160)) +% (z_2159) in 
  let xx_2163 : ed25519_field_element_t :=
    (u_2161) *% (nat_mod_inv (v_2162)) in 
  bind (sqrt (xx_2163)) (fun x_2164 => let x_r_2165 : uint8 :=
      is_negative (x_2164) in 
    let '(x_2164) :=
      if (uint8_declassify (x_r_2165)) !=.? (uint8_declassify (
          x_s_2156)):bool then (let x_2164 :=
          (nat_mod_zero ) -% (x_2164) in 
        (x_2164)) else ((x_2164)) in 
    some ((x_2164, y_2158, z_2159, (x_2164) *% (y_2158)))).

Definition encode (p_2166 : ed_point_t) : byte_seq :=
  let '(x_2167, y_2168, z_2169, _) :=
    p_2166 in 
  let z_inv_2170 : ed25519_field_element_t :=
    nat_mod_inv (z_2169) in 
  let x_2171 : ed25519_field_element_t :=
    (x_2167) *% (z_inv_2170) in 
  let y_2172 : ed25519_field_element_t :=
    (y_2168) *% (z_inv_2170) in 
  let s_2173 : byte_seq :=
    nat_mod_to_byte_seq_le (y_2172) in 
  let s_2173 :=
    seq_upd s_2173 (usize 31) ((seq_index (s_2173) (usize 31)) .^ ((
          is_negative (x_2171)) shift_left (usize 7))) in 
  s_2173.

Definition decode (q_s_2174 : byte_seq) : (option ed_point_t) :=
  let q_2175 : compressed_ed_point_t :=
    array_from_slice (default : uint8) (32) (q_s_2174) (usize 0) (usize 32) in 
  decompress (q_2175).

Definition point_add (p_2176 : ed_point_t) (q_2177 : ed_point_t) : ed_point_t :=
  let d_c_2178 : ed25519_field_element_t :=
    nat_mod_from_byte_seq_le (
      array_to_seq (constant_d_v)) : ed25519_field_element_t in 
  let two_2179 : ed25519_field_element_t :=
    nat_mod_two  in 
  let '(x1_2180, y1_2181, z1_2182, t1_2183) :=
    p_2176 in 
  let '(x2_2184, y2_2185, z2_2186, t2_2187) :=
    q_2177 in 
  let a_2188 : ed25519_field_element_t :=
    ((y1_2181) -% (x1_2180)) *% ((y2_2185) -% (x2_2184)) in 
  let b_2189 : ed25519_field_element_t :=
    ((y1_2181) +% (x1_2180)) *% ((y2_2185) +% (x2_2184)) in 
  let c_2190 : ed25519_field_element_t :=
    (((t1_2183) *% (two_2179)) *% (d_c_2178)) *% (t2_2187) in 
  let d_2191 : ed25519_field_element_t :=
    ((z1_2182) *% (two_2179)) *% (z2_2186) in 
  let e_2192 : ed25519_field_element_t :=
    (b_2189) -% (a_2188) in 
  let f_2193 : ed25519_field_element_t :=
    (d_2191) -% (c_2190) in 
  let g_2194 : ed25519_field_element_t :=
    (d_2191) +% (c_2190) in 
  let h_2195 : ed25519_field_element_t :=
    (b_2189) +% (a_2188) in 
  let x3_2196 : ed25519_field_element_t :=
    (e_2192) *% (f_2193) in 
  let y3_2197 : ed25519_field_element_t :=
    (g_2194) *% (h_2195) in 
  let t3_2198 : ed25519_field_element_t :=
    (e_2192) *% (h_2195) in 
  let z3_2199 : ed25519_field_element_t :=
    (f_2193) *% (g_2194) in 
  (x3_2196, y3_2197, z3_2199, t3_2198).

Definition point_identity  : ed_point_t :=
  (nat_mod_zero , nat_mod_one , nat_mod_one , nat_mod_zero ).

Definition point_mul (s_2200 : scalar_t) (p_2201 : ed_point_t) : ed_point_t :=
  let p_2202 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    p_2201 in 
  let q_2203 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let '(p_2202, q_2203) :=
    foldi (usize 0) (usize 256) (fun i_2204 '(p_2202, q_2203) =>
      let '(q_2203) :=
        if nat_mod_bit (s_2200) (i_2204):bool then (let q_2203 :=
            point_add (q_2203) (p_2202) in 
          (q_2203)) else ((q_2203)) in 
      let p_2202 :=
        point_add (p_2202) (p_2202) in 
      (p_2202, q_2203))
    (p_2202, q_2203) in 
  q_2203.

Definition point_mul_by_cofactor (p_2205 : ed_point_t) : ed_point_t :=
  let p2_2206 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p_2205) (p_2205) in 
  let p4_2207 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p2_2206) (p2_2206) in 
  let p8_2208 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_add (p4_2207) (p4_2207) in 
  p8_2208.

Definition point_neg (p_2209 : ed_point_t) : ed_point_t :=
  let '(x_2210, y_2211, z_2212, t_2213) :=
    p_2209 in 
  ((nat_mod_zero ) -% (x_2210), y_2211, z_2212, (nat_mod_zero ) -% (t_2213)).

Definition point_eq (p_2214 : ed_point_t) (q_2215 : ed_point_t) : bool :=
  let '(x1_2216, y1_2217, z1_2218, _) :=
    p_2214 in 
  let '(x2_2219, y2_2220, z2_2221, _) :=
    q_2215 in 
  (((x1_2216) *% (z2_2221)) =.? ((x2_2219) *% (z1_2218))) && (((y1_2217) *% (
        z2_2221)) =.? ((y2_2220) *% (z1_2218))).

Definition point_normalize (q_2222 : ed_point_t) : ed_point_t :=
  let '(qx_2223, qy_2224, qz_2225, _) :=
    q_2222 in 
  let px_2226 : ed25519_field_element_t :=
    (qx_2223) *% (nat_mod_inv (qz_2225)) in 
  let py_2227 : ed25519_field_element_t :=
    (qy_2224) *% (nat_mod_inv (qz_2225)) in 
  let pz_2228 : ed25519_field_element_t :=
    nat_mod_one  in 
  let pt_2229 : ed25519_field_element_t :=
    (px_2226) *% (py_2227) in 
  (px_2226, py_2227, pz_2228, pt_2229).

Definition secret_expand
  (sk_2230 : secret_key_t)
  : (serialized_scalar_t '× serialized_scalar_t) :=
  let h_2231 : sha512_digest_t :=
    sha512 (seq_from_slice (sk_2230) (usize 0) (usize 32)) in 
  let h_d_2232 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2231)) (usize 32) (
      usize 32) in 
  let s_2233 : serialized_scalar_t :=
    array_from_slice (default : uint8) (32) (array_to_seq (h_2231)) (usize 0) (
      usize 32) in 
  let s_2233 :=
    array_upd s_2233 (usize 0) ((array_index (s_2233) (usize 0)) .& (secret (
          @repr WORDSIZE8 248) : int8)) in 
  let s_2233 :=
    array_upd s_2233 (usize 31) ((array_index (s_2233) (usize 31)) .& (secret (
          @repr WORDSIZE8 127) : int8)) in 
  let s_2233 :=
    array_upd s_2233 (usize 31) ((array_index (s_2233) (usize 31)) .| (secret (
          @repr WORDSIZE8 64) : int8)) in 
  (s_2233, h_d_2232).

Definition secret_to_public (sk_2234 : secret_key_t) : public_key_t :=
  let '(s_2235, _) :=
    secret_expand (sk_2234) in 
  let base_2236 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let ss_2237 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (s_2235)) : scalar_t in 
  let a_2238 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (ss_2237) (base_2236) in 
  compress (a_2238).

Definition check_canonical_scalar (s_2239 : serialized_scalar_t) : bool :=
  (if ((uint8_declassify ((array_index (s_2239) (usize 31)) .& (secret (
              @repr WORDSIZE8 224) : int8))) !=.? (
        @repr WORDSIZE8 0)):bool then (false) else ((nat_mod_from_byte_seq_le (
          array_to_seq (s_2239)) : big_integer_t) <.? (
        nat_mod_from_byte_seq_le (
          array_to_seq (constant_l_v)) : big_integer_t))).

