module Rust_primitives.Integers

open FStar.Mul

module LI = Lib.IntTypes

#set-options "--max_fuel 0 --max_ifuel 1 --z3rlimit 20"

noextract
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
   | 61 | 62 | 65 | 127 | 128 -> p = normalize_term (pow2 x)
   | _ -> True)
  [SMTPat (pow2 x)]

inline_for_extraction
type inttype = LI.inttype
inline_for_extraction
let unsigned = LI.unsigned
inline_for_extraction
let signed = LI.signed
inline_for_extraction
type uinttype = t:inttype{unsigned t}
inline_for_extraction
let int_t t = LI.int_t t LI.PUB

inline_for_extraction
let bits t = LI.bits t
inline_for_extraction
val usize_inttype: t:inttype{unsigned t /\ (t = LI.U32 \/ t = LI.U64)}
inline_for_extraction
val isize_inttype: t:inttype{signed t /\ (t = LI.S32 \/ t = LI.S64)}

inline_for_extraction
type u8 = int_t LI.U8 
inline_for_extraction
type i8 = int_t LI.S8
inline_for_extraction
type u16 = int_t LI.U16
inline_for_extraction
type i16 = int_t LI.S16
inline_for_extraction
type u32 = int_t LI.U32
inline_for_extraction
type i32 = int_t LI.S32
inline_for_extraction
type u64 = int_t LI.U64
inline_for_extraction
type i64=  int_t LI.S64
inline_for_extraction
type u128 = int_t LI.U128
inline_for_extraction
type i128 = int_t LI.S128
inline_for_extraction
unfold type usize = u32 // int_t usize_inttype
inline_for_extraction
unfold type isize = i32 //int_t isize_inttype

inline_for_extraction
let minint (t:LI.inttype) =
  if unsigned t then 0 else -(pow2 (bits t - 1))
inline_for_extraction
let maxint (t:LI.inttype) =
  if unsigned t then pow2 (bits t) - 1
  else pow2 (bits t - 1) - 1
inline_for_extraction
let modulus (t:LI.inttype) = pow2 (bits t)

inline_for_extraction
let max_usize = maxint LI.U32
inline_for_extraction
let max_isize = maxint LI.S32

//let range_bits (n:int) (n:bits) : bool =
//  minint t <= n && n <= maxint t

inline_for_extraction
let range (n:int) (t:inttype) : bool =
  minint t <= n && n <= maxint t
inline_for_extraction
type range_t (t:inttype) = x:int{range x t}

[@(strict_on_arguments [0])]
noextract
let v (#t:inttype) (x:int_t t) : range_t t = LI.v #t #LI.PUB x

inline_for_extraction
val mk_int (#t:inttype) (n:range_t t) : int_t t

noextract
val mk_int_lemma (#t:inttype) (n:range_t t) :
  Lemma (mk_int #t n == LI.mk_int #t #LI.PUB n)
  [SMTPat (mk_int #t n)]
  
inline_for_extraction noextract
val sz (n:range_t LI.U32) : usize

inline_for_extraction noextract
val sz_lemma (n:range_t LI.U32) :
  Lemma (sz n == mk_int n)
  [SMTPat (sz n)]

inline_for_extraction
val isz (n:range_t LI.S32) : isize

inline_for_extraction
val isz_lemma (n:range_t LI.S32) :
  Lemma (isz n == mk_int n)
  [SMTPat (isz n)]

noextract
val mk_int_v_lemma: #t:inttype -> a:int_t t -> Lemma
  (mk_int #t (v #t a) == a)
  [SMTPat (mk_int #t (v #t a))]

noextract
val v_mk_int_lemma: #t:inttype -> n:range_t t -> Lemma
  (v #t (mk_int #t n) == n)
  [SMTPat (v #t (mk_int #t n))]

(* Wrap-around modulo: wraps into [-p/2; p/2[ *)
noextract
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m

[@(strict_on_arguments [0])]
noextract
let op_At_Percent_Dot x t : range_t t =
  if unsigned t then x % modulus t
  else x @% modulus t

inline_for_extraction
val cast (#t:inttype) (#t':inttype)
         (u1:int_t t{range (v u1) t'}):
         int_t t'

noextract
val cast_lemma (#t:inttype) (#t':inttype)
    (u1:int_t t{range (v u1) t'}):
    Lemma (cast #t #t' u1 == mk_int #t' (v u1))
    [SMTPat (cast #t #t' u1)]

inline_for_extraction
val cast_mod (#t:inttype) (#t':inttype)
         (u1:int_t t) : int_t t'

noextract 
val cast_mod_lemma (#t:inttype) (#t':inttype)
    (u1:int_t t) : 
    Lemma (cast_mod #t #t' u1 == mk_int #t' (v u1 @%. t'))
    [SMTPat (cast_mod #t #t' u1)]

/// Arithmetic operations
/// 


inline_for_extraction
val add_mod (#t:uinttype) (a:int_t t) (b:int_t t) : int_t t

noextract
val add_mod_lemma: #t:uinttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma
    (add_mod a b == mk_int #t ((v a + v b) @%. t))
    [SMTPat (add_mod #t a b)]
    
inline_for_extraction
val add (#t:inttype) (a:int_t t)
        (b:int_t t{range (v a + v b) t}) : int_t t

noextract
val add_lemma: #t:uinttype
  -> a:int_t t
  -> b:int_t t{range (v a + v b) t}
  -> Lemma
    (add a b == mk_int #t (v a + v b))
    [SMTPat (add #t a b)]

inline_for_extraction
val incr (#t:inttype) (a:int_t t{v a < maxint t}) : int_t t

noextract
val incr_lemma: #t:inttype
  -> a:int_t t{v a < maxint t}
  -> Lemma (incr a == mk_int #t (v a + 1))
    [SMTPat (incr #t a)]

inline_for_extraction
val mul_mod (#t:uinttype{not (LI.U128? t)}) (a:int_t t)
            (b:int_t t) : int_t t
            
noextract
val mul_mod_lemma: #t:uinttype{not (LI.U128? t)}
  -> a:int_t t
  -> b:int_t t
  -> Lemma (mul_mod a b == mk_int #t (v a * v b @%. t))
    [SMTPat (mul_mod #t a b)]

inline_for_extraction
val mul (#t:uinttype{not (LI.U128? t)}) (a:int_t t)
        (b:int_t t{range (v a * v b) t}) : int_t t

noextract
val mul_lemma: #t:uinttype{not (LI.U128? t)}
  -> a:int_t t
  -> b:int_t t{range (v a * v b) t}
  -> Lemma (mul a b == mk_int #t (v a * v b))
    [SMTPat (mul #t a b)]
  
inline_for_extraction
val sub_mod (#t:inttype) (a:int_t t) (b:int_t t): int_t t
 
noextract
val sub_mod_lemma: #t:uinttype
  -> a:int_t t
  -> b:int_t t
  -> Lemma
    (sub_mod a b == mk_int #t ((v a - v b) @%. t))
    [SMTPat (sub_mod a b)]

inline_for_extraction
val sub (#t:inttype) (a:int_t t)
        (b:int_t t{range (v a - v b) t}) : int_t t

noextract
val sub_lemma: #t:uinttype
  -> a:int_t t
  -> b:int_t t{range (v a - v b) t}
  -> Lemma
    (sub a b ==  mk_int #t (v a - v b))
    [SMTPat (sub #t a b)]
    
inline_for_extraction
val decr (#t:inttype) (a:int_t t{minint t < v a}) : int_t t

noextract
val decr_lemma: #t:inttype
  -> a:int_t t{minint t < v a}
  -> Lemma (decr a == mk_int #t (v a - 1))
    [SMTPat (decr #t a)]


inline_for_extraction
val div (#t:inttype) (a:int_t t) (b:int_t t{v b <> 0}): int_t t

noextract
val div_lemma: #t:inttype{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (assume (unsigned t \/ range (v a / v b) t); div a b == mk_int #t (v a / v b))
    [SMTPat (div #t a b)] 

inline_for_extraction
val mod (#t:inttype) (a:int_t t) (b:int_t t{v b <> 0}) : int_t t

noextract
val mod_lemma: #t:inttype{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t t
  -> b:int_t t{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (mod a b == mk_int #t (v a % v b))

  

/// Comparison Operators
/// 

inline_for_extraction
val eq (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val eq_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (eq #t a b == (v a = v b))
  [SMTPat (eq #t a b)]

inline_for_extraction
val ne (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val ne_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (ne #t a b == (v a <> v b))
  [SMTPat (ne #t a b)]

inline_for_extraction
val lt (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val lt_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (lt #t a b == (v a < v b))
  [SMTPat (lt #t a b)]

inline_for_extraction
val lte (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val lte_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (lte #t a b == (v a <= v b))
  [SMTPat (lte #t a b)]

inline_for_extraction
val gt (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val gt_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (gt #t a b == (v a > v b))
  [SMTPat (gt #t a b)]

inline_for_extraction
val gte (#t:inttype) (a:int_t t) (b:int_t t): bool
noextract
val gte_lemma (#t:inttype) (a:int_t t) (b:int_t t):
  Lemma (gte #t a b == (v a >= v b))
  [SMTPat (gte #t a b)]

/// Bitwise Operations

inline_for_extraction
val ones (#t:inttype) : n:int_t t

noextract
val ones_lemma (#t:inttype) : Lemma
  (ones #t == (if unsigned t then mk_int #t (pow2 (bits t) - 1)
               else mk_int #t (-1)))
  [SMTPat (ones #t)]

inline_for_extraction
val zero (#t:inttype) : n:int_t t

inline_for_extraction
val zero_lemma (#t:inttype) :
  Lemma (zero #t == mk_int 0)
  [SMTPat (zero #t)]


inline_for_extraction
val lognot: #t:inttype -> int_t t -> int_t t
val lognot_lemma: #t:inttype -> a:int_t t -> Lemma
  (lognot a == LI.lognot #t #LI.PUB a /\
   lognot #t zero == ones /\
   lognot #t ones == zero /\
   lognot (lognot a) == a)
  [SMTPat (lognot #t a)]
  
inline_for_extraction
val logxor: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t
val logxor_lemma: #t:inttype -> a:int_t t -> b:int_t t -> Lemma
  (logxor a b == LI.logxor #t #LI.PUB a b /\
   a `logxor` (a `logxor` b) == b /\
   a `logxor` (b `logxor` a) == b /\
   a `logxor` zero == a /\
   a `logxor` ones == lognot a)
  [SMTPat (logxor #t a b)]
  
inline_for_extraction
val logand: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

noextract
val logand_lemma: #t:inttype -> a:int_t t -> b:int_t t ->
  Lemma (logand a b == LI.logand #t #LI.PUB a b /\
         logand a zero == zero /\
         logand a ones == a)
  [SMTPat (logand #t a b)]

noextract
val logand_mask_lemma: #t:inttype
  -> a:int_t t
  -> m:pos{m < bits t} ->
  Lemma (pow2 m < maxint t /\
         logand a (sub #t (mk_int #t (pow2 m)) (mk_int #t 1)) ==
         mk_int (v a % pow2 m))
  [SMTPat (logand #t a (sub #t (mk_int #t (pow2 m)) (mk_int #t 1)))]

inline_for_extraction
val logor: #t:inttype
  -> int_t t
  -> int_t t
  -> int_t t

val logor_lemma: #t:inttype -> a:int_t t -> b:int_t t ->
  Lemma (logor a b == LI.logor #t #LI.PUB a b /\
         logor a zero == a /\
         logor a ones == ones)
  [SMTPat (logor #t a b)]

unfold type shiftval (t:inttype) (t':inttype) =
     b:int_t t'{v b >= 0 /\ v b < bits t}
unfold type rotval (t:inttype) (t':inttype) =
     b:int_t t'{v b > 0 /\ v b < bits t}

inline_for_extraction
val shift_right (#t:inttype) (#t':inttype)
    (a:int_t t) (b:shiftval t t') : int_t t

inline_for_extraction
val shift_right_lemma (#t:inttype) (#t':inttype)
    (a:int_t t) (b:shiftval t t') :
    Lemma (LI.shift_right_lemma #t #LI.PUB a (LI.size (v b));
           shift_right #t #t' a b ==
           mk_int #t (v a / pow2 (v b)))
    [SMTPat (shift_right #t #t' a b)]
     
inline_for_extraction
val shift_left (#t:inttype) (#t':inttype)
    (a:int_t t{v a >= 0}) (b:shiftval t t') : int_t t

noextract
val shift_left_lemma: #t:inttype -> #t':inttype
  -> a:int_t t{v a >= 0} -> b:shiftval t t'
  -> Lemma
    (let x:range_t t = (v a * pow2 (v b)) @%. t in
     shift_left #t #t' a b = mk_int x) 
  [SMTPat (shift_left #t #t' a b)]

inline_for_extraction
val rotate_right: #t:uinttype -> #t':inttype
  -> a:int_t t
  -> rotval t t'
  -> int_t t

noextract
val rotate_right_lemma: #t:uinttype -> #t':inttype
  -> a:int_t t -> b:rotval t t'
  -> Lemma (v (cast b <: u32) > 0 /\ 
           rotate_right a b ==
           LI.rotate_right #t #LI.PUB a (cast b))
    [SMTPat (rotate_right #t #t' a b)]

inline_for_extraction
val rotate_left: #t:uinttype -> #t':inttype
  -> a:int_t t
  -> rotval t t'
  -> int_t t

inline_for_extraction
val rotate_left_lemma: #t:uinttype -> #t':inttype
  -> a:int_t t -> b:rotval t t'
  -> Lemma (v (cast b <: u32) > 0 /\ 
           rotate_left a b ==
           LI.rotate_left #t #LI.PUB a (cast b))
   [SMTPat (rotate_left #t #t' a b)]

inline_for_extraction
let shift_right_i (#t:inttype) (#t':inttype) (s:shiftval t t') (u:int_t t) : int_t t = shift_right u s

inline_for_extraction
let shift_left_i (#t:inttype) (#t':inttype) (s:shiftval t t') (u:int_t t{v u >= 0}) : int_t t = shift_left u s

inline_for_extraction
let rotate_right_i (#t:uinttype) (#t':inttype) (s:rotval t t') (u:int_t t) : int_t t = rotate_right u s

inline_for_extraction
let rotate_left_i (#t:uinttype) (#t':inttype) (s:rotval t t') (u:int_t t) : int_t t = rotate_left u s

inline_for_extraction
val abs_int (#t:inttype) (a:int_t t{minint t < v a}) : int_t t

noextract
val abs_int_lemma: #t:inttype{signed t /\ not (LI.S128? t)}
  -> a:int_t t{minint t < v a}
  -> Lemma (abs_int a == mk_int #t (abs (v a)))
  [SMTPat (abs_int #t a)]

///
/// Operators available for all machine integers
///

// Strict: with precondition
inline_for_extraction unfold
let (+!) #t (x: int_t t) (y: int_t t): int_t t = admit (); LI.add #t #LI.PUB x y

// Wrapping: no precondition
inline_for_extraction unfold
let (+%) #t = add #t

inline_for_extraction unfold
let (+.) #t = add #t

inline_for_extraction unfold
let ( *! ) #t (x: int_t t) (y: int_t t): int_t t = admit (); LI.mul #t #LI.PUB x y

inline_for_extraction unfold
let ( *. ) #t = mul #t

inline_for_extraction unfold
let ( -! ) #t (x: int_t t) (y: int_t t): int_t t = admit (); LI.sub #t #LI.PUB x y

inline_for_extraction unfold
let ( -% ) #t = sub_mod #t

unfold
let ( -. ) #t = sub #t

inline_for_extraction unfold
let ( >>! ) #t (x: int_t t) (y: u8): i32 = admit (); LI.shift_right #t #LI.PUB x y

inline_for_extraction unfold
let ( <<! ) #t (x: int_t t) (y: u8): i32 = admit (); LI.shift_left #t #LI.PUB x y

unfold
let ( >>>. ) #t #t' = rotate_right #t #t'

unfold
let ( <<<. ) #t #t' = rotate_left #t #t'

unfold
let ( ^. ) #t = logxor #t

unfold
let ( |. ) #t = logor #t

unfold
let ( &. ) #t = logand #t

unfold
let ( ~. ) #t = lognot #t


inline_for_extraction unfold
let ( /! ) #t (x: int_t t) (y: int_t t): int_t t = admit (); LI.div #t x y

unfold
let (%!) #t = mod #t

unfold
let (=.) = (=)

unfold
let (<>.) = (<>)

unfold
let (<.) #t = lt #t

unfold
let (<=.) #t = lte #t

unfold
let (>.) #t = gt #t

unfold
let (>=.) #t = gte #t 

