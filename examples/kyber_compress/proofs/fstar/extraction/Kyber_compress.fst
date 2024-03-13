module Kyber_compress
#set-options "--fuel 0 --ifuel 1 --z3rlimit 150"
open Core
open FStar.Mul

let v_FIELD_MODULUS: i32 = 3329l

let v_UNSIGNED_FIELD_MODULUS: u32 = cast (v_FIELD_MODULUS <: i32) <: u32

let get_n_least_significant_bits (n: u8) (value: u32)
    : Prims.Pure u32
      (requires n =. 4uy || n =. 5uy || n =. 10uy || n =. 11uy || n =. 16uy)
      (ensures
        fun result ->
          let result:u32 = result in
          result <. (Core.Num.impl__u32__pow 2ul (cast (n <: u8) <: u32) <: u32)) =
  let nth_bit:u32 = 1ul <<! n in
  let mask:u32 = nth_bit -! 1ul in
  Rust_primitives.Integers.logand_mask_lemma value (v n);
  value &. mask

let compress (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. (1l <<! coefficient_bits <: i32)) =
  let compressed:u64 = (cast (fe <: u16) <: u64) <<! coefficient_bits in
  let compressed:u64 = compressed +! 1664uL in
  let compressed:u64 = compressed *! 10321340uL in
  let compressed:u64 = compressed >>! 35l in
  let compressed:u64 = compressed &. ((1uL <<! coefficient_bits <: u64) -! 1uL <: u64) in
  let compressed:u32 = cast (compressed <: u64) <: u32 in
  Rust_primitives.Integers.logand_mask_lemma compressed (v coefficient_bits);
  cast (get_n_least_significant_bits coefficient_bits compressed <: u32) <: i32

let compress_unsafe (coefficient_bits: u8) (fe: u16)
    : Prims.Pure i32
      (requires
        (coefficient_bits =. 4uy || coefficient_bits =. 5uy || coefficient_bits =. 10uy ||
        coefficient_bits =. 11uy) &&
        fe <. (cast (v_FIELD_MODULUS <: i32) <: u16))
      (ensures
        fun result ->
          let result:i32 = result in
          result <. (1l <<! coefficient_bits <: i32)) =
  let compressed:u32 = (cast (fe <: u16) <: u32) <<! (coefficient_bits +! 1uy <: u8) in
  let compressed:u32 = compressed +! v_UNSIGNED_FIELD_MODULUS in
  let compressed:u32 = compressed /! (v_UNSIGNED_FIELD_MODULUS <<! 1l <: u32) in
  let compressed:u32 = compressed &. ((1ul <<! coefficient_bits <: u32) -! 1ul <: u32) in
  cast (get_n_least_significant_bits coefficient_bits compressed <: u32) <: i32
