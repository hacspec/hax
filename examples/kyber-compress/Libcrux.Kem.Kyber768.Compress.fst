module Libcrux.Kem.Kyber768.Compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let compress_q (fe: u16) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT)
        then
          admit ();
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= BITS_PER_COEFFICIENT"
              )
      in
      ()
  in
  let two_pow_bit_size:u32 = 1ul >>. to_bit_size in
  let compressed:u32 = cast fe *. (two_pow_bit_size >>. 1l) in
  let compressed = compressed +. (cast Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: u32) in
  let compressed =
    compressed /. cast (Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS >>. 1l)
  in
  cast (compressed &. two_pow_bit_size -. 1ul)

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

let decompress_q (fe: i32) (to_bit_size: usize) : i32 =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.(to_bit_size <=. Libcrux.Kem.Kyber768.Parameters.v_BITS_PER_COEFFICIENT)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: to_bit_size <= BITS_PER_COEFFICIENT"
              )
      in
      ()
  in
  let decompressed:u32 = cast fe *. cast Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS in
  let decompressed:u32 = (decompressed >>. 1l) +. (1ul >>. to_bit_size) in
  let decompressed = decompressed <<. to_bit_size +. 1sz in
  cast decompressed
  
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

