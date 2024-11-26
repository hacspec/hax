module Rust_primitives.BitVectors

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

#set-options "--fuel 0 --ifuel 1 --z3rlimit 40"

let lemma_get_bit_bounded #t x d i = admit() // see issue #423

let lemma_get_bit_bounded' #t x d = admit() // see issue #423

let pow2_minus_one_mod_lemma1 (n: nat) (m: nat {m < n})
   : Lemma (((pow2 n - 1) / pow2 m) % 2 == 1)
   = let d: pos = n - m in
     Math.Lemmas.pow2_plus m d;
     Math.Lemmas.lemma_div_plus (-1) (pow2 d) (pow2 m);
     if d > 0 then Math.Lemmas.pow2_double_mult (d-1)

let pow2_minus_one_mod_lemma2 (n: nat) (m: nat {n <= m})
  : Lemma (((pow2 n - 1) / pow2 m) % 2 == 0)
  = Math.Lemmas.pow2_le_compat m n;
    Math.Lemmas.small_div (pow2 n - 1) (pow2 m)

let bit_vec_to_int_t #t (d: num_bits t) (bv: bit_vec d) = admit ()

let bit_vec_to_int_t_lemma #t (d: num_bits t) (bv: bit_vec d) i = admit ()

let bit_vec_to_int_t_array d bv = admit () // see issue #423
let bit_vec_to_nat_array d bv = admit () // see issue #423

let get_bit_pow2_minus_one #t n nth
  = reveal_opaque (`%get_bit) (get_bit (mk_int #t (pow2 n - 1)) nth);
    if v nth < n then pow2_minus_one_mod_lemma1 n (v nth)
                 else pow2_minus_one_mod_lemma2 n (v nth)

let mask_inv_opt_in_range #t (mask: int_t t {Some? (mask_inv_opt (v mask))})
  : Lemma (range (Some?.v (mask_inv_opt (v mask))) t)
          [SMTPat (mask_inv_opt (v mask))]
  = let n = (Some?.v (mask_inv_opt (v mask))) in
    assert (pow2 n - 1 == v mask)

let get_bit_pow2_minus_one_i32 x nth
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #i32_inttype x;
    get_bit_pow2_minus_one #i32_inttype n nth

let get_bit_pow2_minus_one_i16 x nth
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #i16_inttype x;
    get_bit_pow2_minus_one #i16_inttype n nth

let get_bit_pow2_minus_one_u32 x nth
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #u32_inttype x;
    get_bit_pow2_minus_one #u32_inttype n nth

let get_bit_pow2_minus_one_u16 x nth
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #u16_inttype x;
    get_bit_pow2_minus_one #u16_inttype n nth

let get_bit_pow2_minus_one_u8 t x nth
  = let n = Some?.v (mask_inv_opt x) in
    mk_int_equiv_lemma #u8_inttype x;
    get_bit_pow2_minus_one #u8_inttype n nth
