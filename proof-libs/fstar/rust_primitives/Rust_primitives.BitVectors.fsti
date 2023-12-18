module Rust_primitives.BitVectors

open FStar.Mul
open Rust_primitives.Arrays
open Rust_primitives.Integers


/// Number of bits carried by an integer of type `t`
type bit_num t = d: usize {v d > 0 /\ v d <= bits t}

/// Integer of type `t` that carries `d` bits
type int_t_d t (d: bit_num t) = 
  n: int_t t {forall (i: usize). (v i < bits t /\ v i >= v d) ==> get_bit n i == 0}

/// `get_bit` within an array of integers carrying `d` bits each
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let get_bit_arr (#n: inttype) (#len: usize) 
                (arr: t_Array (int_t n) len)
                (d: bit_num n)
                (nth: usize {v nth < v len * v d}): bit
  = get_bit (Seq.index arr (v (nth /! d))) (nth %! d)
#pop-options


/// `get_bit` within an array of integers carrying `d` bits each
#push-options "--fuel 0 --ifuel 1 --z3rlimit 50"
let get_bit_nat_arr (#len: usize)
                (arr: t_Array nat len)
                (d: usize)
                (nth: usize {v nth < v len * v d}): bit
                : bit
  = get_bit_nat (Seq.index arr (v (nth /! d))) (v (nth %! d))
#pop-options


/// Same as `get_bit_arr`, but inputs are `nat`s instead of `usize`s
let get_bit_arr_nat (#n: inttype) (#len: nat {len < max_usize})
                    (arr: t_Array (int_t n) (sz len))
                    (d: nat {d > 0 /\ d <= bits n})
                    (nth: nat {nth < len * d /\ nth < max_usize}): bit
  = get_bit_arr arr (mk_int d) (mk_int nth)

/// Create a bit vector given an array of integers carrying `d` bits each
let bit_vector (#n: inttype) (#len: usize)
               (arr: t_Array (int_t n) len)
               (d: bit_num n {v len * v d < max_usize})
  : t_Array bit (len *! d)
  = createi (len *! d) (get_bit_arr arr d)

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
           | _   -> None

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `i32`
val get_bit_pow2_minus_one_i32
  (x: int {Some? (mask_inv_opt x)}) (nth: usize {v nth < 32})
  : Lemma ( get_bit (FStar.Int32.int_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit (FStar.Int32.int_to_t x) nth)]

/// Specialized `get_bit_pow2_minus_one` lemmas with SMT patterns
/// targetting machine integer literals of type `u8`  
val get_bit_pow2_minus_one_u8
  (t: _ {t == u8_inttype}) (x: int {Some? (mask_inv_opt x)}) (nth: usize {v nth < 8})
  : Lemma ( get_bit #t (FStar.UInt8.uint_to_t x) nth 
        == (if v nth < Some?.v (mask_inv_opt x) then 1 else 0))
  [SMTPat (get_bit #t (FStar.UInt8.uint_to_t x) nth)]

val get_last_bit_signed_lemma (#t: inttype{signed t}) (x: int_t t)
  : Lemma (   get_bit x (mk_int (bits t - 1)) 
          == (if v x < 0 then 1 else 0))
    // [SMTPat (get_bit x (mk_int (bits t - 1)))]



