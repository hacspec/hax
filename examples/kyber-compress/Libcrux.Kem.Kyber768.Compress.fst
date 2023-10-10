module Libcrux.Kem.Kyber768.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 35"
open FStar.Mul
open Core
open Rust_primitives

let compress_q (fe: u16) (to_bit_size: u32 {v to_bit_size > 0 /\ v to_bit_size <= 12}) : i32 =
  let two_pow_bit_size:u32 = 1ul <<. to_bit_size in
    //  assume (2 * v two_pow_bit_size == v tmp);
    //  FStar.Math.Lemmas.pow2_le_compat 12 (v to_bit_size);
    //  assert (v fe < pow2 16);
    //  assert_norm (2 * pow2 12 == pow2 13);
    //  assert (v tmp <= pow2 13);
    //  FStar.Math.Lemmas.pow2_plus 13 16;
    //  assert (v fe * v tmp < pow2 (13 + 16));
    //  assert_norm (pow2 (13 + 16) < pow2 32);
    //  assert (v fe * v tmp < pow2 32);
  let compressed:u32 = (cast fe <: u32) *. (two_pow_bit_size <<. 1ul) in
  let compressed =
    compressed /. (3329ul <<. 1ul)
  in
  let result = compressed &. (two_pow_bit_size -. 1ul) in
  assert (two_pow_bit_size == mk_int (pow2 (v to_bit_size)));
  assert (result == (compressed &. (mk_int #Lib.IntTypes.U32 (pow2 (v to_bit_size)) -. (mk_int 1)))); 
  logand_mask_lemma compressed (v to_bit_size);
  assert (result == mk_int (v compressed % pow2 (v to_bit_size))); 
  cast result <: i32


(*
let compress
      (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      (bits_per_compressed_coefficient: usize)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber768.Arithmetic.f_coefficients
        (fun coefficient ->
            compress_q (Libcrux.Kem.Kyber768.Conversions.to_unsigned_representative coefficient)
              bits_per_compressed_coefficient)
    }
  in
  re
*)

let decompress_q (fe: i32{v fe < 100 /\ v fe > -100}) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then (
      let _:Prims.unit =
        if not (to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT)
        then
          Rust_primitives.Hax.never_to_any (admit();Core.Panicking.panic "assertion failed: to_bit_size <= BITS_PER_COEFFICIENT"
              )
      in
      ())
  in
//  assert(False);
  let decompressed:u32 = (cast fe <: u32) *. cast Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: u32 in
  let decompressed:u32 = (decompressed >>. 1ul) +. (1ul >>. (cast to_bit_size <: u32)) in
  let decompressed = decompressed <<. (cast (to_bit_size +. (sz 1)) <: u32) in
  cast_mod decompressed

(*
let decompress
      (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      (bits_per_compressed_coefficient: usize)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.f_coefficients
      =
      Core.Array.impl_23__map re.Libcrux.Kem.Kyber768.Arithmetic.f_coefficients
        (fun coefficient -> decompress_q coefficient bits_per_compressed_coefficient)
    }
  in
  re
*)
