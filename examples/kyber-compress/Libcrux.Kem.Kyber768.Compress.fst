module Libcrux.Kem.Kyber768.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 35"
open FStar.Mul
open Core


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
  let compressed:u32 = (cast Lib.IntTypes.U32 fe <: u32) *. (two_pow_bit_size <<. 1ul) in
  let compressed =
    compressed /. (3329ul <<. 1ul)
  in
  let result = compressed &. two_pow_bit_size -. 1ul in
    //assert (v (two_pow_bit_size -. 1ul) == pow2 (v to_bit_size) - 1);
  logand_mask compressed (two_pow_bit_size -. 1ul) (v to_bit_size);
    //  assert (v result < pow2 (v to_bit_size));
    //  FStar.Math.Lemmas.pow2_lt_compat 31 (v to_bit_size);
  cast Lib.IntTypes.S32 result
  
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

let decompress_q (fe: i32) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then (admit();
      let _:Prims.unit =
        if not (to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= BITS_PER_COEFFICIENT"
              )
      in
      ())
  in
  let decompressed:u32 = cast Lib.IntTypes.U32 fe *. cast Lib.IntTypes.U32 Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS in
  let decompressed:u32 = (decompressed >>. 1l) +. (1ul >>. to_bit_size) in
  let decompressed = decompressed <<. to_bit_size +. 1sz in
  cast Lib.IntTypes.S32 decompressed

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
