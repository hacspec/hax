module Rust_primitives.BitVectors

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers

/// Number of bits carried by an integer of type `t`
type bit_num t = d: nat {d > 0 /\ d <= bits t /\ (signed t ==> d <= bits t)}

/// States that `x` is a positive integer that fits in `d` bits
type bounded #t (x:int_t t) (d:bit_num t) =
  v x >= 0 /\ v x < pow2 d

/// Integer of type `t` that carries at most `d` bits
type int_t_d t (d: bit_num t) =
  n: int_t t {bounded n d}

/// If `x` fits in `d` bits, then upper bits are zero
val lemma_get_bit_bounded #t (x:int_t t) (d:bit_num t) (i:usize):
  Lemma ((bounded x d /\ v i >= d /\ v i < bits t) ==>
         get_bit x i == 0)
        [SMTPat (get_bit #t x i); SMTPat (bounded x d)]

/// If upper bits of `x` are zero, then `x` is bounded accordingly
val lemma_get_bit_bounded' #t (x:int_t t) (d:bit_num t):
  Lemma (requires forall i. v i > d ==> get_bit x i == 0)
        (ensures bounded x d)

/// A bit vector is a partial map from indexes to bits
type bit_vec (len: nat) = i:nat {i < len} -> bit

/// Transform an array of integers to a bit vector
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let bit_vec_of_int_arr (#n: inttype) (#len: usize) 
                (arr: t_Array (int_t n) len)
                (d: bit_num n): bit_vec (v len * d)
  = fun i -> get_bit (Seq.index arr (i / d)) (sz (i % d))
#pop-options

/// Transform an array of `nat`s to a bit vector
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let bit_vec_of_nat_arr (#len: usize)
                       (arr: t_Array nat len)
                       (d: nat)
                       : bit_vec (v len * d)
  = fun i -> get_bit_nat (Seq.index arr (i / d)) (i % d)
#pop-options

/// Bit-wise semantics of `2^n-1`
val get_bit_pow2_minus_one #t
  (n: nat {pow2 n - 1 <= maxint t}) 
  (nth: usize {v nth < bits t})
  : Lemma (  get_bit (mk_int #t (pow2 n - 1)) nth
          == (if v nth < n then 1 else 0))

/// Log2 table
unfold let mask_inv_opt =
  function | 0   -> Some 0
           | 1   -> Some 1
           | 3   -> Some 2
           | 7   -> Some 3
           | 15  -> Some 4
           | 31  -> Some 5
           | 63  -> Some 6
           | 127 -> Some 7
           | 255 -> Some 8
           | 511 -> Some 9
           | 1023  -> Some  10
           | 2047  -> Some  11
           | 4095  -> Some  12
(*           | 8191  -> Some  13
           | 16383  -> Some  14
           | 32767  -> Some  15
           | 65535  -> Some  16
           | 131071  -> Some  17
           | 262143  -> Some  18
           | 524287  -> Some  19
           | 1048575  -> Some  20
           | 2097151  -> Some  21
           | 4194303  -> Some  22
           | 8388607  -> Some  23
           | 16777215  -> Some  24
           | 33554431  -> Some  25
           | 67108863  -> Some  26
           | 134217727  -> Some  27
           | 268435455  -> Some  28
           | 536870911  -> Some  29
           | 1073741823  -> Some  30
           | 2147483647  -> Some  31
           | 4294967295  -> Some  32
*)           | _   -> None


/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `i32`
val get_bit_pow2_minus_one_i32
  (x: int {x < pow2 31 /\ Some? (mask_inv_opt x)}) (nth: usize {v nth < 32})
  : Lemma ( get_bit (FStar.Int32.int_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit (FStar.Int32.int_to_t x) nth)]

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `u32`
val get_bit_pow2_minus_one_u32
  (x: int {x < pow2 32 /\ Some? (mask_inv_opt x)}) (nth: usize {v nth < 32})
  : Lemma ( get_bit (FStar.UInt32.uint_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit (FStar.UInt16.uint_to_t x) nth)]

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `u16`
val get_bit_pow2_minus_one_u16
  (x: int {x < pow2 16 /\ Some? (mask_inv_opt x)}) (nth: usize {v nth < 16})
  : Lemma ( get_bit (FStar.UInt16.uint_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit (FStar.UInt16.uint_to_t x) nth)]

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `u8`  
val get_bit_pow2_minus_one_u8
  // We use `Lib.IntTypes` (Hacl*'s library): every operation on
  // integers is polymorphic in integer types. There is a one to one
  // correspondence between F*'s machine integers (UInt16, UInt64...)
  // and `Lib.IntTypes.inttype`'s variants (U16, U32...), but for `U8`
  // and `U1`. Bits (`U1`) and `u8`s are using the same
  // representation: `U8`. Thus, sometimes F* picks the wrong
  // `inttype`. This is the reason for the refined type `t` below,
  // which appears only on this version of the specialized
  // `get_bit_pow2_minus_one` lemma.
  (t: _ {t == u8_inttype})  
  (x: int {x < pow2 8 /\ Some? (mask_inv_opt x)}) (nth: usize {v nth < 8})
  : Lemma ( get_bit #t (FStar.UInt8.uint_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit #t (FStar.UInt8.uint_to_t x) nth)]

