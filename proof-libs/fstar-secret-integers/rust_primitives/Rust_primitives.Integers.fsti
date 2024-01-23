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
   | 61 | 62 | 63 | 65 | 127 | 128 -> p = normalize_term (pow2 x)
   | _ -> True)
  [SMTPat (pow2 x)]

type inttype = LI.inttype
let unsigned = LI.unsigned
let signed = LI.signed
type uinttype = t:inttype{unsigned t}
let int_t_l t l = LI.int_t t l
let int_t t = int_t_l t LI.SEC
let pub_int_t t = int_t_l t LI.PUB

let meet (l1 l2:LI.secrecy_level) : LI.secrecy_level =
  match l1, l2 with
  | LI.SEC, LI.PUB -> LI.SEC
  | LI.SEC, LI.SEC -> LI.SEC
  | LI.PUB, LI.SEC -> LI.SEC
  | LI.PUB, LI.PUB -> LI.PUB

let can_flow (l1 l2:LI.secrecy_level) : bool =
  match l1, l2 with
  | LI.PUB, LI.PUB -> true
  | LI.SEC, LI.SEC -> true
  | LI.PUB, LI.SEC -> true
  | LI.SEC, LI.PUB -> false

let bits t = LI.bits t
let u8_inttype = LI.U8
let i8_inttype = LI.S8
let u16_inttype = LI.U16
let i16_inttype = LI.S16
let u32_inttype = LI.U32
let i32_inttype = LI.S32
let u64_inttype = LI.U64
let i64_inttype = LI.S64
let u128_inttype = LI.U128
let i128_inttype = LI.S128
val usize_inttype: t:inttype{unsigned t /\ (t = LI.U32 \/ t = LI.U64)}
val isize_inttype: t:inttype{signed t /\ (t = LI.S32 \/ t = LI.S64)}

type u8 = int_t LI.U8 
type i8 = int_t LI.S8
type u16 = int_t LI.U16
type i16 = int_t LI.S16
type u32 = int_t LI.U32
type i32 = int_t LI.S32
type u64 = int_t LI.U64
type i64=  int_t LI.S64
type u128 = int_t LI.U128
type i128 = int_t LI.S128

type pub_u8 = pub_int_t LI.U8 
type pub_i8 = pub_int_t LI.S8
type pub_u16 = pub_int_t LI.U16
type pub_i16 = pub_int_t LI.S16
type pub_u32 = pub_int_t LI.U32
type pub_i32 = pub_int_t LI.S32
type pub_u64 = pub_int_t LI.U64
type pub_i64=  pub_int_t LI.S64
type pub_u128 = pub_int_t LI.U128
type pub_i128 = pub_int_t LI.S128

type usize = pub_int_t usize_inttype
type isize = pub_int_t isize_inttype

let minint (t:LI.inttype) =
  if unsigned t then 0 else -(pow2 (bits t - 1))
let maxint (t:LI.inttype) =
  if unsigned t then pow2 (bits t) - 1
  else pow2 (bits t - 1) - 1
let modulus (t:LI.inttype) = pow2 (bits t)

let max_usize = maxint usize_inttype
let max_isize = maxint isize_inttype

//let range_bits (n:int) (n:bits) : bool =
//  minint t <= n && n <= maxint t

let range (n:int) (t:inttype) : bool =
  minint t <= n && n <= maxint t
type range_t (t:inttype) = x:int{range x t}

[@(strict_on_arguments [0])]
let v (#t:inttype) (#l) (x:int_t_l t l) : range_t t = LI.v #t #l x

[@(strict_on_arguments [0])]
val mk_int_l (#t:inttype) (#l:LI.secrecy_level) (n:range_t t) : int_t_l t l

[@(strict_on_arguments [0])]
let mk_int (#t:inttype) (n:range_t t) : int_t t = mk_int_l n

[@(strict_on_arguments [0])]
let mk_pub_int (#t:inttype) (n:range_t t) : pub_int_t t = mk_int_l n

[@(strict_on_arguments [0])]
val mk_int_equiv_lemma #t (n:range_t t) :
    Lemma (
    match t with
    | LI.U8 -> mk_int_l #u8_inttype n == UInt8.uint_to_t n   
    | LI.S8 -> mk_int_l #i8_inttype n == Int8.int_to_t n   
    | LI.U16 -> mk_int_l #u16_inttype n == UInt16.uint_to_t n   
    | LI.S16 -> mk_int_l #i16_inttype n == Int16.int_to_t n   
    | LI.U32 -> mk_int_l #u32_inttype n == UInt32.uint_to_t n   
    | LI.S32 -> mk_int_l #i32_inttype n == Int32.int_to_t n   
    | LI.U64 -> mk_int_l #u64_inttype n == UInt64.uint_to_t n   
    | LI.S64 -> mk_int_l #i64_inttype n == Int64.int_to_t n   
    | LI.U128 -> mk_int_l #u128_inttype n == UInt128.uint_to_t n   
    | LI.S128 -> mk_int_l #i128_inttype n == Int128.int_to_t n  
    | _ -> True)

let sz (n:range_t usize_inttype) : usize = mk_int_l n
let isz (n:range_t isize_inttype) : isize = mk_int_l n

val mk_int_v_lemma: #t:inttype -> #l:LI.secrecy_level -> a:int_t_l t l -> Lemma
  (mk_int_l #t (v #t #l a) == a)
  [SMTPat (mk_int_l #t #l (v #t #l a))]

val v_mk_int_lemma: #t:inttype -> #l:LI.secrecy_level -> n:range_t t -> Lemma
  (v #t #l (mk_int_l #t #l n) == n)
  [SMTPat (v #t #l (mk_int_l #t #l n))]

(* Wrap-around modulo: wraps into [-p/2; p/2[ *)
let op_At_Percent (v:int) (p:int{p>0/\ p%2=0}) : Tot int =
  let m = v % p in if m >= p/2 then m - p else m 

[@(strict_on_arguments [0])]
let op_At_Percent_Dot x t : range_t t =
  if unsigned t then x % modulus t
  else x @% modulus t

let cast (#t:inttype) (#t':inttype) (#l:LI.secrecy_level)
    (u1:int_t_l t l{range (v u1) t'}) =
    mk_int_l #t' #l (v u1)
let cast_mod (#t:inttype) (#t':inttype) (#l:LI.secrecy_level)
    (u1:int_t_l t l) = 
    mk_int_l #t' #l (v u1 @%. t')

let classify #t #l (#l':LI.secrecy_level{can_flow l l'})
    (a:int_t_l t l)    
    : int_t_l t l' =
    match l,l' with
    | LI.PUB, LI.SEC -> LI.secret #t a
    | LI.PUB, LI.PUB -> a
    | LI.SEC, LI.SEC -> a

(* NOTE: Use with extreme care, and clearly document each use case *)
val declassify #t #l #l'
    (a:int_t_l t l)    
    : int_t_l t l'


/// Arithmetic operations
/// 
let add_mod (#t:inttype) 
            (#l #l':LI.secrecy_level) 
            (a:int_t_l t l) (b:int_t_l t l') =
    mk_int_l #t #(meet l l') ((v a + v b) @%. t)

val add_mod_equiv_lemma: #t:uinttype 
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'
  -> Lemma
    (add_mod a b == LI.add_mod #_ #(meet l l') (classify a) (classify b))

let add (#t:inttype) (#l #l':LI.secrecy_level) (a:int_t_l t l)
        (b:int_t_l t l'{range (v a + v b) t}) =
    mk_int_l #t #(meet l l') (v a + v b)

val add_equiv_lemma: #t:uinttype -> #l:LI.secrecy_level -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'{range (v a + v b) t}
  -> Lemma
    (add a b == LI.add #t #(meet l l') (classify a) (classify b))

let incr (#t:inttype) (#l:LI.secrecy_level) (a:int_t_l t l{v a < maxint t}) =
    mk_int_l #t #l (v a + 1)

val incr_equiv_lemma: #t:inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l{v a < maxint t}
  -> Lemma (incr a == LI.incr a)

let mul_mod (#t:inttype) (#l #l':LI.secrecy_level)
            (a:int_t_l t l)
            (b:int_t_l t l') =
            mk_int_l #t #(meet l l') (v a * v b @%. t)

val mul_mod_equiv_lemma: #t:uinttype{not (LI.U128? t)}
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'
  -> Lemma (mul_mod a b == LI.mul_mod #t #(meet l l') (classify a) (classify b))

let mul (#t:inttype) (#l #l':LI.secrecy_level)
        (a:int_t_l t l)
        (b:int_t_l t l'{range (v a * v b) t}) =
        mk_int_l #t #(meet l l') (v a * v b)

val mul_equiv_lemma: #t:uinttype{not (LI.U128? t)} 
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'{range (v a * v b) t}
  -> Lemma (mul a b == LI.mul #t #(meet l l') (classify a) (classify b))

let sub_mod (#t:inttype) (#l #l':LI.secrecy_level)
  (a:int_t_l t l) (b:int_t_l t l') =
    mk_int_l #t #(meet l l') ((v a - v b) @%. t)

val sub_mod_equiv_lemma: #t:uinttype
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'
  -> Lemma
    (sub_mod a b == LI.sub_mod #_ #(meet l l') (classify a) (classify b))

let sub (#t:inttype) (#l #l':LI.secrecy_level)
        (a:int_t_l t l)
        (b:int_t_l t l'{range (v a - v b) t}) =
    mk_int_l #t #(meet l l') (v a - v b) 

val sub_equiv_lemma: #t:uinttype
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l'{range (v a - v b) t}
  -> Lemma
    (sub a b == LI.sub #t #(meet l l') (classify a) (classify b))

let decr (#t:inttype) (#l:LI.secrecy_level) (a:int_t_l t l{minint t < v a}) =
    mk_int_l #t #l (v a - 1)

val decr_equiv_lemma: #t:inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l{minint t < v a}
  -> Lemma (decr a == LI.decr  a)

let div (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB{v b <> 0}) =
  assume(unsigned t \/ range (v a / v b) t);
  mk_int_l #t #LI.PUB (v a / v b)
  
val div_equiv_lemma: #t:inttype{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t_l t LI.PUB
  -> b:int_t_l t LI.PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (div a b == LI.div a b)

let mod (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB{v b <> 0}) =
  mk_int_l #t #LI.PUB (v a % v b)


val mod_equiv_lemma: #t:inttype{~(LI.U128? t) /\ ~(LI.S128? t)}
  -> a:int_t_l t LI.PUB
  -> b:int_t_l t LI.PUB{v b <> 0 /\ (unsigned t \/ range FStar.Int.(v a / v b) t)}
  -> Lemma (mod a b == LI.mod a b)
  

/// Comparison Operators
/// 
let eq (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v a = v b
let ne (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v b <> v b
let lt (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v a < v b
let lte (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v a <= v b
let gt (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v a > v b
let gte (#t:inttype) (a:int_t_l t LI.PUB) (b:int_t_l t LI.PUB) = v a >= v b


/// Bitwise Operations


let ones (#t:inttype) (#l:LI.secrecy_level) : n:int_t_l t l =
  if unsigned t then mk_int_l #t #l (pow2 (bits t) - 1)
  else mk_int_l #t #l (-1)

let zero (#t:inttype) (#l:LI.secrecy_level) : n:int_t_l t l =
  mk_int_l #t #l 0

val lognot: #t:inttype -> #l:LI.secrecy_level -> int_t_l t l -> int_t_l t l
val lognot_lemma: #t:inttype -> #l:LI.secrecy_level -> a:int_t_l t l -> Lemma
  (lognot a == LI.lognot  a /\
   lognot #t #l zero == ones /\
   lognot #t #l ones == zero /\
   lognot (lognot a) == a /\
   (signed t ==> v (lognot a) = -1 - v a) /\
   (unsigned t ==> v (lognot a)  = pow2 (bits t) - 1 - v a)
   )

val logxor: #t:inttype 
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> int_t_l t l
  -> int_t_l t l'
  -> int_t_l t (meet l l')
  
val logxor_lemma: #t:inttype 
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l 
  -> b:int_t_l t l' -> Lemma
  (logxor a b == LI.logxor #t #(meet l l') (classify a) (classify b) /\
   a `logxor` a == zero #t #l /\
   (a `logxor` b == zero #t #(meet l l') ==> v b == v a) /\
   v (a `logxor` (a `logxor` b)) == v b /\
   v (a `logxor` (b `logxor` a)) == v b /\
   zero #t #l' `logxor` a == classify a /\
   a `logxor` zero #t #l' == classify a /\
   v (ones #t #l' `logxor` a) == v (lognot a) /\
   v (a `logxor` ones #t #l') == v (lognot a))
    
val logand: #t:inttype -> #l:LI.secrecy_level -> #l':LI.secrecy_level
  -> int_t_l t l
  -> int_t_l t l'
  -> int_t_l t (meet l l')

val logand_lemma: #t:inttype -> #l:LI.secrecy_level -> #l':LI.secrecy_level -> a:int_t_l t l -> b:int_t_l t l' ->
  Lemma (logand a b == LI.logand #t #(meet l l') (classify a) (classify b) /\
         v (logand a (zero #t #l')) == v (zero #t #l') /\
         v (logand (zero #t #l') a) == v (zero #t #l') /\
         v (logand a (ones #t #l')) == v a /\
         v (logand (ones #t #l') a) == v a /\
         (v a >= 0 ==> (v (logand a b) >= 0) /\ (v (logand a b) <= v a)) /\
         (v b >= 0 ==> (v (logand a b) >= 0) /\ (v (logand a b) <= v b)))

val logand_mask_lemma: #t:inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l
  -> m:nat{m < bits t} ->
  Lemma (pow2 m < maxint t /\
         logand a (sub #t (mk_int_l #t #l (pow2 m)) (mk_int_l #t #l 1)) ==
         mk_int_l #t #l (v a % pow2 m))
  [SMTPat (logand #t a (sub #t (mk_int_l #t #l (pow2 m)) (mk_int_l #t #l 1)))]

val logor: #t:inttype -> #l:LI.secrecy_level -> #l':LI.secrecy_level
  -> int_t_l t l
  -> int_t_l t l'
  -> int_t_l t (meet l l')

val logor_lemma: #t:inttype
  -> #l:LI.secrecy_level
  -> #l':LI.secrecy_level
  -> a:int_t_l t l
  -> b:int_t_l t l' ->
  Lemma (logor a b == LI.logor #t #(meet l l') (classify a) (classify b) /\
         v (logor a (zero #t #l')) == v a /\
         v (logor a (ones #t #l')) == v (ones #t #l') /\
         v (logor (zero #t #l') a) == v a /\
         v (logor (ones #t #l') a) == v (ones #t #l') /\
         ((v a >= 0 /\ v b >= 0) ==> (v (logor a b) >= v a /\ v (logor a b) >= v b)))

unfold type shiftval (t:inttype) (t':inttype) =
     b:int_t_l t' LI.PUB{v b >= 0 /\ v b < bits t}
unfold type rotval (t:inttype) (t':inttype) =
     b:int_t_l t' LI.PUB{v b > 0 /\ v b < bits t}

let shift_right (#t:inttype) (#t':inttype) (#l:LI.secrecy_level)
    (a:int_t_l t l) (b:shiftval t t') =
    LI.shift_right_lemma  a (LI.size (v b));
    mk_int_l #t #l (v a / pow2 (v b))

val shift_right_equiv_lemma: #t:inttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l -> b:shiftval t t'
  -> Lemma
    (v ((cast #t' #u32_inttype b <: LI.size_t)) < bits t /\
     shift_right #t #t' a b ==
     LI.shift_right a (cast #t' #u32_inttype b <: LI.size_t))
     
let shift_left (#t:inttype) (#t':inttype) (#l:LI.secrecy_level)
    (a:int_t_l t l) (b:shiftval t t') =
    let x:range_t t = (v a * pow2 (v b)) @%. t in
    mk_int_l #t #l x

val shift_left_equiv_lemma: #t:inttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l -> b:shiftval t t'
  -> Lemma
    ((v a >= 0 /\ range (v a * pow2 (v b)) t) ==>
     (v (cast #_ #u32_inttype b) < bits t /\
      shift_left #t #t' a b ==
      LI.shift_left  a (cast b)))

val rotate_right: #t:uinttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l
  -> rotval t t'
  -> int_t_l t l

val rotate_right_equiv_lemma: #t:uinttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l -> b:rotval t t'
  -> Lemma (v (cast #_ #u32_inttype b) > 0 /\ 
           rotate_right a b ==
           LI.rotate_right  a (cast b))
  
val rotate_left: #t:uinttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l
  -> rotval t t'
  -> int_t_l t l

val rotate_left_equiv_lemma: #t:uinttype -> #t':inttype -> #l:LI.secrecy_level
  -> a:int_t_l t l -> b:rotval t t'
  -> Lemma (v (cast #_ #u32_inttype b) > 0 /\ 
           rotate_left a b ==
           LI.rotate_left  a (cast b))

let shift_right_i (#t:inttype) (#t':inttype) (#l:LI.secrecy_level) (s:shiftval t t') (u:int_t_l t l) : int_t_l t l = shift_right u s

let shift_left_i (#t:inttype) (#t':inttype) (#l:LI.secrecy_level) (s:shiftval t t') (u:int_t_l t l{v u >= 0}) : int_t_l t l = shift_left u s

let rotate_right_i (#t:uinttype) (#t':inttype) (#l:LI.secrecy_level) (s:rotval t t') (u:int_t_l t l) : int_t_l t l = rotate_right u s

let rotate_left_i (#t:uinttype) (#t':inttype) (#l:LI.secrecy_level) (s:rotval t t') (u:int_t_l t l) : int_t_l t l = rotate_left u s

let abs_int (#t:inttype) (#l:LI.secrecy_level) (a:int_t_l t l{minint t < v a}) =
    mk_int_l #t #l (abs (v a))

val abs_int_equiv_lemma: #t:inttype{signed t /\ not (LI.S128? t)} 
  -> #l:LI.secrecy_level
  -> a:int_t_l t l{minint t < v a}
  -> Lemma (abs_int a == LI.ct_abs  a)

let neg (#t:inttype{signed t}) (#l:LI.secrecy_level) (a:int_t_l t l{range (0 - v a) t}) =
    mk_int_l #t #l (0 - (v a))

val neg_equiv_lemma: #t:inttype{signed t /\ not (LI.S128? t)} -> #l:LI.secrecy_level
  -> a:int_t_l t l{range (0 - v a) t}
  -> Lemma (neg a == sub (mk_int_l #t #l 0) a /\
          (lognot a == sub (neg a) (mk_int_l #t #l 1)))


///
/// Operators available for all machine integers
///

// Strict: with precondition
unfold
let (+!) #t #l #l' = add #t #l #l'

// Wrapping: no precondition
unfold
let (+.) #t #l #l' = add_mod #t #l #l'

unfold
let ( *! ) #t #l #l' = mul #t #l #l'

unfold
let ( *. ) #t #l #l' = mul_mod #t #l #l'

unfold
let ( -! ) #t #l #l' = sub #t #l #l'

unfold
let ( -. ) #t #l #l' = sub_mod #t #l #l'

unfold
let ( >>! ) #t #t' #l = shift_right #t #t' #l

unfold
let ( <<! ) #t #t' #l = shift_left #t #t' #l

unfold
let ( >>>. ) #t #t' #l = rotate_right #t #t' #l

unfold
let ( <<<. ) #t #t' #l = rotate_left #t #t' #l

unfold
let ( ^. ) #t #l #l' = logxor #t #l #l'

unfold
let ( |. ) #t #l #l' = logor #t #l #l'

unfold
let ( &. ) #t #l #l' = logand #t #l #l'

unfold
let ( ~. ) #t #l = lognot #t #l

unfold
let (/!) #t = div #t

unfold
let (%!) #t = mod #t

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


type bit = n: nat {n < 2}

/// Mathematical `get_bit` definition on `nat`s
let get_bit_nat (x: nat) (nth: nat): bit
  = (x / pow2 nth) % 2

/// `get_bit` definition for machine integer of any size and signedness
[@"opaque_to_smt"]
let get_bit (#t: inttype) (#l:LI.secrecy_level)
            (x: int_t_l t l) (nth: usize {v nth < bits t}): bit
  = if v x >= 0 then get_bit_nat (v x) (v nth)
               else // two's complement
                    get_bit_nat (pow2 (bits t) + v x) (v nth)

unfold let bit_and (x y: bit): bit = match x, y with | (1, 1) -> 1 | _ -> 0
unfold let bit_or  (x y: bit): bit = (x + y) % 2

/// Bit-wise semantics for `&.`
val get_bit_and #t #l (x y: int_t_l t l) (i: usize {v i < bits t})
  : Lemma (get_bit (x &. y) i == get_bit x i `bit_and` get_bit y i)
          [SMTPat (get_bit (x &. y) i)]

/// Bit-wise semantics for `|.`
val get_bit_or #t #l (x y: int_t_l t l) (i: usize {v i < bits t})
  : Lemma (get_bit (x |. y) i == get_bit x i `bit_or` get_bit y i)
          [SMTPat (get_bit (x |. y) i)]

/// Bit-wise semantics for `<<!`
val get_bit_shl #t #u #l (x: int_t_l t l) (y: int_t_l u LI.PUB) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t)
          (ensures get_bit (x <<! y) i 
                == (if v i < v y then 0 else get_bit x (mk_int_l (v i - v y))))
    [SMTPat (get_bit (x <<! y) i)]

/// Bit-wise semantics for `>>!`
val get_bit_shr #t #u #l (x: int_t_l t l) (y: int_t_l u LI.PUB) (i: usize {v i < bits t})
  : Lemma (requires v y >= 0 /\ v y < bits t)
          (ensures get_bit (x >>! y) i 
                == (if v i < bits t - v y
                    then get_bit x (mk_int_l (v i + v y))
                    else if signed t
                         then get_bit x (mk_int_l (bits t - 1))
                         else 0))
    [SMTPat (get_bit (x >>! y) i)]

// TODO: check for neg numbers
/// Bit-wise semantics of integer casts
val get_bit_cast #t #u #l
  (x: int_t_l t l) (nth: usize)
  : Lemma (requires v nth < bits u /\ v nth < bits t)
          (ensures get_bit (cast_mod #t #u x) nth == get_bit x nth)
          [SMTPat (get_bit (cast_mod #t #u x) nth)]

val get_bit_cast_extend #t #u #l
  (x: int_t_l t l) (nth: usize)
  : Lemma (requires bits t < bits u /\ v nth >= bits t /\ v nth < bits u)
          (ensures get_bit (cast_mod #t #u x) nth == 0)
          [SMTPat (get_bit (cast_mod #t #u x) nth)]

