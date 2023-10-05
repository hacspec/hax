module Rust_primitives.Integers

open FStar.Mul

module LI = Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"

val pow2_values: x:nat -> Lemma
  (let p = pow2 x in
   match x with
   | 0  -> p=1
   | 1  -> p=2
   | 8  -> p=256
   | 16 -> p=65536
   | 31 -> p=2147483648
   | 32 -> p=4294967296
   | 63 -> p=9223372036854775808
   | 64 -> p=18446744073709551616
   | 2 | 3 | 4 | 5 | 6 | 7
   | 9 | 10 | 11 | 12 | 13 | 14 | 15 
   | 17 | 18 | 19 | 20 | 21 | 22 | 23
   | 24 | 25 | 26 | 27 | 28 | 29 | 30
   | 33 | 34 | 35 | 36 | 37 | 38 | 39
   | 40 | 41 | 42 | 43 | 44 | 45 | 46
   | 47 | 48 | 49 | 50 | 51 | 52 | 53
   | 54 | 55 | 56 | 57 | 58 | 59 | 60
   | 61 | 62 | 65 -> p = normalize_term (pow2 x)
   | _ -> True)
  [SMTPat (pow2 x)]

unfold
type inttype = LI.inttype
unfold
let unsigned = LI.unsigned
unfold
let signed = LI.signed
unfold
type uinttype = t:inttype{unsigned t}

unfold
let int_t t = LI.int_t t LI.PUB //LI.pub_int_t t


unfold
let bits t = LI.bits t
val usize_inttype: t:inttype{unsigned t /\ (t = LI.U32 \/ t = LI.U64)}
val isize_inttype: t:inttype{signed t /\ (t = LI.S32 \/ t = LI.S64)}

unfold
type u8 = int_t LI.U8 
unfold
type i8 = int_t LI.S8
unfold
type u16 = int_t LI.U16
unfold
type i16 = int_t LI.S16
unfold
type u32 = int_t LI.U32
unfold
type i32 = int_t LI.S32
unfold
type u64 = int_t LI.U64
unfold
type i64=  int_t LI.S64
unfold
type u128 = int_t LI.U128
unfold
type i128 = int_t LI.S128


unfold
type usize = int_t usize_inttype
unfold
type isize = int_t isize_inttype


unfold
let minint (t:LI.inttype) = LI.minint t
unfold
let maxint (t:LI.inttype) = LI.maxint t
unfold
let modulus (t:LI.inttype) = LI.modulus t

unfold
let max_usize = maxint usize_inttype

unfold
let max_isize = maxint isize_inttype

let range (n:int) (t:inttype) : bool =
  minint t <= n && n <= maxint t

unfold
type range_t (t:inttype) = x:int{range x t}

[@(strict_on_arguments [0])]
unfold
let v #t (x:int_t t) : range_t t = LI.v #t #LI.PUB x

[@(strict_on_arguments [0])]
unfold
let mk_int #t (n:range_t t) : u:int_t t{v u == n} =
  LI.mk_int #t #LI.PUB n

inline_for_extraction
let sz (n:nat{n <= max_usize}) : usize = mk_int n

val v_injective: #t:inttype -> a:int_t t -> Lemma
  (mk_int (v #t a) == a)
  [SMTPat (v #t a)]

val v_mk_int: #t:inttype -> n:range_t t -> Lemma
  (v #t (mk_int #t n) == n)
  [SMTPat (v #t (mk_int #t n))]

inline_for_extraction
val usize_to_uint32: s:usize -> u:u32{u == mk_int (v s % pow2 32)}

inline_for_extraction
val usize_to_uint64: s:usize -> u:u64{u == mk_int (v s % pow2 64)}

[@(strict_on_arguments [0])]
inline_for_extraction
let op_At_Percent_Dot x t = LI.op_At_Percent_Dot x t

// Casting a value to a signed type is implementation-defined when the value can't
// be represented in the new type; e.g. (int8_t)128UL is implementation-defined
// We rule out this case in the type of `u1`
// See 6.3.1.3 in http://www.open-std.org/jtc1/sc22/wg14/www/docs/n1548.pdf
[@(strict_on_arguments [0;2])]
inline_for_extraction
val cast: #t:inttype -> t':inttype
  -> u1:int_t t{unsigned t' \/ range (v u1) t'}
  -> u2:int_t t'{v u2 == v u1 @%. t'}

///
/// Bitwise operators for all machine integers
///


[@(strict_on_arguments [0])]
inline_for_extraction
val ones: t:inttype -> n:int_t t{
  if unsigned t then v n = pow2 (bits t) - 1
  else v n = -1}

inline_for_extraction
val zero: t:inttype -> n:int_t t{v n = 0}

[@(strict_on_arguments [0])]
inline_for_extraction
val add_mod: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val add_mod_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma
    (v (add_mod a b) == (v a + v b) @%. t)
    [SMTPat (v #t (add_mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val add: #t:inttype
  -> a:int_t t
  -> b:int_t t{range (v a + v b) t}
  -> int_t t

val add_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t{range (v a + v b) t}
  -> Lemma
    (v #t (add #t a b) == v a + v b)
    [SMTPat (v #t (add #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val incr: #t:inttype
  -> a:int_t t{v a < maxint t}
  -> int_t t

val incr_lemma: #t:inttype
  -> a:int_t t{v a < maxint t}
  -> Lemma (v (incr a) == v a + 1)
    [SMTPat (v (incr a))]

[@(strict_on_arguments [0])]
inline_for_extraction
val mul_mod: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val mul_mod_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (v (mul_mod a b) == (v a * v b) @%. t)
  [SMTPat (v #t (mul_mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val mul: #t:inttype//{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{range (v a * v b) t}
  -> int_t t

val mul_lemma: #t:inttype//{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{range (v a * v b) t}
  -> Lemma (v #t (mul #t a b) == v a * v b)
  [SMTPat (v #t (mul #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val sub_mod: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val sub_mod_lemma: #t:inttype -> a:int_t t -> b:int_t t
  -> Lemma (v (sub_mod a b) == (v a - v b) @%. t)
  [SMTPat (v #t (sub_mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val sub: #t:inttype
  -> a:int_t t
  -> b:int_t t{range (v a - v b) t}
  -> int_t t

val sub_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t{range (v a - v b) t}
  -> Lemma (v (sub a b) == v a - v b)
    [SMTPat (v #t (sub #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val decr: #t:inttype
  -> a:int_t t{minint t < v a}
  -> int_t t

val decr_lemma: #t:inttype
  -> a:int_t t{minint t < v a}
  -> Lemma (v (decr a) == v a - 1)
    [SMTPat (v #t (decr #t a))]
    
[@(strict_on_arguments [0])]
inline_for_extraction
val logxor: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val logxor_lemma: #t:inttype -> a:int_t t -> b:int_t t -> Lemma
  (a `logxor` (a `logxor` b) == b /\
   a `logxor` (b `logxor` a) == b /\
   a `logxor` (mk_int #t 0) == a)


[@(strict_on_arguments [0])]
inline_for_extraction
val logand: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val logand_zero: #t:inttype -> a:int_t t ->
  Lemma (v (a `logand` zero t) == 0)

val logand_ones: #t:inttype -> a:int_t t ->
  Lemma (v (a `logand` ones t) == v a)

val logand_mask: #t:uinttype
  -> a:int_t t
  -> b:int_t t
  -> m:pos{m < bits t} ->
  Lemma
    (requires v b == pow2 m - 1)
    (ensures v (logand #t a b) == v a % pow2 m)

[@(strict_on_arguments [0])]
inline_for_extraction
val logor: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val logor_disjoint: #t:uinttype
  -> a:int_t t
  -> b:int_t t
  -> m:nat{m < bits t}
  -> Lemma
    (requires 0 <= v a /\ v a < pow2 m /\ v b % pow2 m == 0)
    (ensures  v (a `logor` b) == v a + v b)

val logor_zero: #t: inttype -> a: int_t t ->
  Lemma (v (a `logor` zero t) == v a)

val logor_ones: #t: uinttype -> a: int_t t ->
  Lemma (v (a `logor` ones t) == pow2 (bits t) - 1)

[@(strict_on_arguments [0])]
inline_for_extraction
val lognot: #t:inttype -> int_t t -> int_t t

// Unlike HACL* we enforce the Rust type rules for the shiftval
unfold
type shiftval (t:inttype) = x:int_t t {v x >= 0 /\ v x < bits t}

// Unlike HACL* we enforce the Rust type rules for the rotval
unfold
type rotval (t:inttype) = x:int_t t {v x > 0 /\ v x < bits t}

[@(strict_on_arguments [0])]
inline_for_extraction
val shift_right_mod: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val shift_right_mod_lemma: #t:inttype
  -> a:int_t t
  -> b:shiftval t
  -> Lemma
    (v (shift_right_mod a b) == v a / pow2 (v b))
    [SMTPat (v #t (shift_right_mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val shift_right: #t:inttype
  -> int_t t
  -> shiftval t
  -> int_t t

val shift_right_lemma: #t:inttype
  -> a:int_t t
  -> b:shiftval t
  -> Lemma
    (v (shift_right a b) == v a / pow2 (v b))
    [SMTPat (v #t (shift_right #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val shift_left_mod: #t:inttype
  -> a:int_t t
  -> s:int_t t
  -> int_t t

val shift_left_mod_lemma:
    #t:inttype
  -> a:int_t t{unsigned t \/ 0 <= v a}
  -> s:shiftval t{unsigned t \/ (0 <= v a /\ v a * pow2 (v s) <= maxint t)}
  -> Lemma
    (v (shift_left_mod a s) == (v a * pow2 (v s)) @%. t)
    [SMTPat (v #t (shift_left_mod #t a s))]
    
[@(strict_on_arguments [0])]
inline_for_extraction
val shift_left: #t:inttype
  -> a:int_t t
  -> s:shiftval t
  -> Pure (int_t t)
    (requires unsigned t \/ (0 <= v a /\ v a * pow2 (v s) <= maxint t))
    (ensures  fun _ -> True)

val shift_left_lemma:
    #t:inttype
  -> a:int_t t{unsigned t \/ 0 <= v a}
  -> s:shiftval t{unsigned t \/ (0 <= v a /\ v a * pow2 (v s) <= maxint t)}
  -> Lemma
    (v (shift_left a s) == (v a * pow2 (v s)) @%. t)
    [SMTPat (v #t (shift_left #t a s))]

[@(strict_on_arguments [0])]
inline_for_extraction
val rotate_right: #t:inttype
  -> a:int_t t{unsigned t}
  -> rotval t
  -> int_t t

[@(strict_on_arguments [0])]
inline_for_extraction
val rotate_left: #t:inttype
  -> a:int_t t{unsigned t}
  -> rotval t
  -> int_t t

inline_for_extraction
let shift_right_i (#t:uinttype) (s:shiftval t{unsigned t}) (u:int_t t) : int_t t = shift_right u s

inline_for_extraction
let shift_left_i (#t:uinttype) (s:shiftval t{unsigned t}) (u:int_t t) : int_t t = shift_left u s

inline_for_extraction
let rotate_right_i (#t:uinttype) (s:rotval t{unsigned t}) (u:int_t t) : int_t t = rotate_right u s

inline_for_extraction
let rotate_left_i (#t:uinttype) (s:rotval t{unsigned t}) (u:int_t t) : int_t t = rotate_left u s


[@(strict_on_arguments [0])]
inline_for_extraction
val ct_abs: #t:inttype{signed t /\ ~(LI.S128? t)}
  -> a:int_t t{minint t < v a}
  -> b:int_t t{v b == abs (v a)}

[@(strict_on_arguments [0])]
inline_for_extraction
let mod_mask (#t:inttype) (m:shiftval t{pow2 (v m) <= maxint t}) : int_t t = LI.mod_mask #t #LI.PUB (cast LI.U32 m)


val mod_mask_lemma: #t:inttype
  -> a:int_t t -> m:shiftval t{pow2 (v m) <= maxint t}
  -> Lemma (v (a `logand` mod_mask m) == v a % pow2 (v m))
  [SMTPat (a `logand` mod_mask #t m)]

(** Casts a value between two signed types using modular reduction *)
[@(strict_on_arguments [0;2])]
inline_for_extraction
val cast_mod: #t:inttype{signed t}
  -> t':inttype{signed t'}
  -> a:int_t t
  -> b:int_t t'{v b == v a @%. t'}

///
/// Operators available for all machine integers
///

// Strict: with precondition
unfold
let (+!) #t = add #t

// Wrapping: no precondition
unfold
let (+.) #t = add_mod #t

// Strict - doesn't exist yet: no precondition but panics
unfold
let (+?) #t = add #t


unfold
let ( *! ) #t = mul #t

unfold
let ( *. ) #t = mul_mod #t

unfold
let ( -! ) #t = sub #t

unfold
let ( -. ) #t = sub_mod #t

unfold
let ( >>! ) #t = shift_right #t

unfold
let ( >>. ) #t = shift_right_mod #t

unfold
let ( <<! ) #t = shift_left #t

unfold
let ( <<. ) #t = shift_left_mod #t

unfold
let ( >>>. ) #t = rotate_right #t

unfold
let ( <<<. ) #t = rotate_left #t

unfold
let ( ^. ) #t = logxor #t

unfold
let ( |. ) #t = logor #t

unfold
let ( &. ) #t = logand #t

unfold
let ( ~. ) #t = lognot #t

///
/// Operations on public integers
///

[@(strict_on_arguments [0])]
inline_for_extraction
val div: #t:inttype
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> int_t t

val div_lemma: #t:inttype//{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (v (div a b) == FStar.Int.(v a / v b))
  [SMTPat (v #t (div #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val mod: #t:inttype//{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> int_t t

val mod_lemma: #t:inttype//{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (if signed t then
             v (mod a b) == FStar.Int.mod #(bits t) (v a) (v b)
           else
             v (mod a b) == FStar.UInt.mod #(bits t) (v a) (v b))
  [SMTPat (v #t (mod #t a b))]

[@(strict_on_arguments [0])]
inline_for_extraction
val eq: #t:inttype -> int_t t -> int_t t -> bool

inline_for_extraction
val eq_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (a `eq` b == (v a = v b))
  [SMTPat (eq #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val ne: #t:inttype -> int_t t -> int_t t -> bool

val ne_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (a `ne` b == (v a <> v b))
  [SMTPat (ne #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lt: #t:inttype -> int_t t -> int_t t -> bool

val lt_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (a `lt` b == (v a < v b))
  [SMTPat (lt #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val lte: #t:inttype -> int_t t -> int_t t -> bool

val lte_lemma: #t:inttype
  -> a:int_t t 
  -> b:int_t t
  -> Lemma (a `lte` b == (v a <= v b))
  [SMTPat (lte #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gt: #t:inttype -> int_t t -> int_t t -> bool

val gt_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (a `gt` b == (v a > v b))
  [SMTPat (gt #t a b)]

[@(strict_on_arguments [0])]
inline_for_extraction
val gte: #t:inttype -> int_t t -> int_t t -> bool

val gte_lemma: #t:inttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma (a `gte` b == (v a >= v b))
  [SMTPat (gte #t a b)]

unfold
let (/.) #t = div #t

unfold
let (%.) #t = mod #t

unfold
let (=.) #t = eq #t

unfold
let (<>.) #t = ne #t

unfold
let (<.) #t = lt #t

unfold
let (<=.) #t = lte #t

unfold
let (>.) #t = gt #t

unfold
let (>=.) #t = gte #t

