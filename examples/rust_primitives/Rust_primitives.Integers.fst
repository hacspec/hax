module Rust_primitives.Integers

#set-options "--z3rlimit 50 --fuel 0 --ifuel 0"


let pow2_values x = 
   let p = pow2 x in
   assert_norm (p == normalize_term (pow2 x))

let usize_inttype = LI.U32
let isize_inttype = LI.S32

let v_injective #t a = LI.v_injective #t #LI.PUB a
let v_mk_int #t n = LI.v_mk_int #t #LI.PUB n

let usize_to_uint32 x = x
let usize_to_uint64 x = Int.Cast.uint32_to_uint64 x
let size_to_uint64 x = Int.Cast.uint32_to_uint64 x

[@(strict_on_arguments [0;2])]
let cast #t t' u = LI.cast #t #LI.PUB t' LI.PUB u

[@(strict_on_arguments [0])]
let ones t = LI.ones t LI.PUB

let zero t = mk_int 0

[@(strict_on_arguments [0])]
let add_mod #t a b = mk_int((v a + v b) @%. t)
let add_mod_lemma #t a b = ()

[@(strict_on_arguments [0])]
let add #t a b = LI.add #t #LI.PUB a b
let add_lemma #t a b = ()

[@(strict_on_arguments [0])]
let incr #t a = LI.incr #t #LI.PUB a
let incr_lemma #t a = LI.incr_lemma a

[@(strict_on_arguments [0])]
let mul_mod #t a b = mk_int(v a * v b @%. t)
let mul_mod_lemma #t a b = ()

[@(strict_on_arguments [0])]
let mul #t a b = mk_int(v a * v b)
let mul_lemma #t a b = ()

[@(strict_on_arguments [0])]
let sub_mod #t a b = mk_int(v a - v b @%. t)
let sub_mod_lemma #t a b = ()

[@(strict_on_arguments [0])]
let sub #t a b = LI.sub #t #LI.PUB a b
let sub_lemma #t a b = ()

[@(strict_on_arguments [0])]
let decr #t a = LI.decr #t #LI.PUB a
let decr_lemma #t a = LI.decr_lemma a


[@(strict_on_arguments [0])]
let logxor #t a b = LI.logxor #t #LI.PUB a b

let logxor_lemma #t a b = LI.logxor_lemma a b

[@(strict_on_arguments [0])]
let logand #t a b = LI.logand #t #LI.PUB a b

let logand_zero #t a = LI.logand_zeros a

let logand_ones #t a = LI.logand_ones a

let logand_mask #t a b m = LI.logand_mask #t #LI.PUB a b m


[@(strict_on_arguments [0])]
let logor #t a b = LI.logor #t #LI.PUB a b

let logor_disjoint #t a b m = LI.logor_disjoint a b m

let logor_zero #t a = LI.logor_zeros a

let logor_ones #t a = LI.logor_ones a

[@(strict_on_arguments [0])]
let lognot #t a = LI.lognot #t #LI.PUB a

[@(strict_on_arguments [0])]
let shift_right_mod #t a b =
  if v b >= 0 && v b < bits t then LI.shift_right #t #LI.PUB a (cast LI.U32 b)
  else a

let shift_right_mod_lemma #t a b =
  if v b >= 0 && v b < bits t then () else ()

[@(strict_on_arguments [0])]
let shift_right #t a b = LI.shift_right a (cast LI.U32 b)

let shift_right_lemma #t a b = LI.shift_right_lemma a (cast LI.U32 b)

[@(strict_on_arguments [0])]
let shift_left_mod #t a b =
  admit(); LI.shift_left #t #LI.PUB a (cast LI.U32 b)

let shift_left_mod_lemma #t a b = LI.shift_left_lemma a (cast LI.U32 b)

[@(strict_on_arguments [0])]
let shift_left #t a b = LI.shift_left a (cast LI.U32 b)

let shift_left_lemma #t a b = ()

let rotate_right #t a b = LI.rotate_right a (cast LI.U32 b)

let rotate_left #t a b = LI.rotate_left a (cast LI.U32 b)

[@(strict_on_arguments [0])]
let ct_abs #t a = LI.ct_abs a

#push-options "--z3rlimit 100"
let mod_mask_lemma #t a m = admit(); LI.mod_mask_lemma a (cast LI.U32 m)
#pop-options

let cast_mod #t t' a = LI.cast_mod #t #LI.PUB t' LI.PUB a

[@(strict_on_arguments [0])]
let div #t x y =
  match t with
  | LI.U128 | LI.S128 -> mk_int (v x / v y)
  | _ -> LI.div x y

let div_lemma #t x y =
  match t with
  | LI.U128 | LI.S128 -> admit()
  | _ -> ()


let mod #t x y =
  match t with
  | LI.U128 | LI.S128 -> mk_int (v x % v y)
  | _ -> LI.mod x y

let mod_lemma #t a b =
  match t with
  | LI.U128 | LI.S128 -> admit()
  | _ -> ()

let eq #t x y = LI.eq x y
let eq_lemma #t x y = ()

let ne #t x y = LI.ne x y
let ne_lemma #t x y = ()

let lt #t x y = LI.lt x y
let lt_lemma #t x y = ()

let lte #t x y = LI.lte x y
let lte_lemma #t x y = ()

let gt #t x y = LI.gt x y
let gt_lemma #t x y = ()

let gte #t x y = LI.gte x y
let gte_lemma #t x y = ()

