module Kyber_compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 500"
open Core
open FStar.Mul

let v_FIELD_MODULUS: i32 = 3329l

let v_UNSIGNED_FIELD_MODULUS: u32 = cast (v_FIELD_MODULUS <: i32) <: u32

let compress (coefficient_bits: u8) (fe: u16)
    : Prims.Pure u32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (v_FIELD_MODULUS <: i32) <: u16))
      (fun _ -> Prims.l_True) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  cast (compressed <: u64) <: u32

let compress_unsafe (coefficient_bits: u8) (fe: u16)
    : Prims.Pure u32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (v_FIELD_MODULUS <: i32) <: u16))
      (fun _ -> Prims.l_True) =
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 = compressed +! v_UNSIGNED_FIELD_MODULUS in
  compressed /! (v_UNSIGNED_FIELD_MODULUS <<! 1l <: u32)
