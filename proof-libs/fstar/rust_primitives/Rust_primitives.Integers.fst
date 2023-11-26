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

let mk_int #t a = admit()
let mk_int_lemma #t a = admit()

let sz n = LI.size n
let sz_lemma n = admit()

let isz n = LI.i32 n
let isz_lemma n  = admit()

let mk_int_v_lemma #t a = ()
let v_mk_int_lemma #t a = ()

let cast #t #t' a = LI.cast #t #LI.PUB t' LI.PUB a
let cast_lemma #t #t' a = admit()

let cast_mod #t #t' a = LI.cast_mod #t #LI.PUB t' LI.PUB a
let cast_mod_lemma #t #t' a = admit()

let add_mod #t a b = LI.add_mod a b
let add_mod_lemma #t a b = LI.add_mod_lemma #t #LI.PUB a b

let add #t a b = LI.add a b
let add_lemma #t a b = LI.add_lemma #t #LI.PUB a b

let incr #t a = LI.incr a
let incr_lemma #t a = LI.incr_lemma #t #LI.PUB a

let mul_mod #t a b = LI.mul_mod a b
let mul_mod_lemma #t a b = LI.mul_mod_lemma #t #LI.PUB a b

let mul #t a b = LI.mul a b
let mul_lemma #t a b = LI.mul_lemma #t #LI.PUB a b

let sub_mod #t a b = LI.sub_mod a b
let sub_mod_lemma #t a b = LI.sub_mod_lemma #t #LI.PUB a b

let sub #t a b = LI.sub a b
let sub_lemma #t a b = LI.sub_lemma #t #LI.PUB a b

let decr #t a = LI.decr a
let decr_lemma #t a = LI.decr_lemma #t #LI.PUB a

let div #t a b = LI.div a b
let div_lemma #t a b = admit(); LI.div_lemma #t a b

let mod #t a b = LI.mod a b
let mod_lemma #t a b = admit(); LI.mod_lemma #t a b

let eq #t a b = LI.eq a b
let eq_lemma #t a b = admit()

let ne #t a b = LI.ne a b
let ne_lemma #t a b = admit()

let lt #t a b = LI.lt a b
let lt_lemma #t a b = admit()

let lte #t a b = LI.lte a b
let lte_lemma #t a b = admit()

let gt #t a b = LI.gt a b
let gt_lemma #t a b = admit()

let gte #t a b = LI.gte a b
let gte_lemma #t a b = admit()

let ones #t = admit() //LI.ones t LI.PUB
let ones_lemma #t = admit()

let zero #t = admit() //LI.zeros t LI.PUB
let zero_lemma #t = admit()

let lognot #t a = LI.lognot #t #LI.PUB a
let lognot_lemma #t a = admit()

let logxor #t a b = LI.logxor #t #LI.PUB a b
let logxor_lemma #t a b = admit()

let logand #t a b = LI.logand #t #LI.PUB a b
let logand_lemma #t a b = admit()
let logand_mask_lemma #t a b = admit()

let logor #t a b = LI.logor #t #LI.PUB a b
let logor_lemma #t a b = admit()

let shift_right #t a b = LI.shift_right a b
let shift_right_lemma #t a b = admit()

let shift_left #t a b = LI.shift_left a b
let shift_left_lemma #t a b = admit()

let rotate_right #t a b = LI.rotate_right #t #LI.PUB a (cast b)
let rotate_right_lemma #t a b = ()
let rotate_left #t a b = LI.rotate_left #t #LI.PUB a (cast b)
let rotate_left_lemma #t a b = ()

let abs_int #t a = LI.ct_abs a
let abs_int_lemma #t a = admit()
