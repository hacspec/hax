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

let mk_int #t a = LI.mk_int #t #LI.PUB a
let mk_int_equiv_lemma #_ = admit () // see issue #423
let mk_int_v_lemma #t a = ()
let v_mk_int_lemma #t a = ()
let add_mod_equiv_lemma #t a b = LI.add_mod_lemma #t #LI.PUB a b
let add_equiv_lemma #t a b = LI.add_lemma #t #LI.PUB a b
let incr_equiv_lemma #t a = LI.incr_lemma #t #LI.PUB a

let mul_mod_equiv_lemma #t a b = LI.mul_mod_lemma #t #LI.PUB a b
let mul_equiv_lemma #t a b = LI.mul_lemma #t #LI.PUB a b
let sub_mod_equiv_lemma #t a b = LI.sub_mod_lemma #t #LI.PUB a b
let sub_equiv_lemma #t a b = LI.sub_lemma #t #LI.PUB a b
let decr_equiv_lemma #t a = LI.decr_lemma #t #LI.PUB a

let div_equiv_lemma #t a b = admit(); LI.div_lemma #t a b // see issue #423
let mod_equiv_lemma #t a b = admit(); LI.mod_lemma #t a b // see issue #423

let lognot #t a = LI.lognot #t #LI.PUB a
let lognot_lemma #t a = admit() // see issue #423

let logxor #t a b = LI.logxor #t #LI.PUB a b
let logxor_lemma #t a b = admit() // see issue #423

let logand #t a b = LI.logand #t #LI.PUB a b
let logand_lemma #t a b = admit() // see issue #423
let logand_mask_lemma #t a b = admit() // see issue #423

let logor #t a b = LI.logor #t #LI.PUB a b
let logor_lemma #t a b = admit() // see issue #423

let shift_right_equiv_lemma #t a b = admit() // see issue #423
let shift_left_equiv_lemma #t a b = admit() // see issue #423

let rotate_right #t a b = LI.rotate_right #t #LI.PUB a (cast b)
let rotate_right_equiv_lemma #t a b = ()
let rotate_left #t a b = LI.rotate_left #t #LI.PUB a (cast b)
let rotate_left_equiv_lemma #t a b = ()

let abs_int_equiv_lemma #t a = admit() // see issue #423

let neg_equiv_lemma #_ _ = ()

let get_bit_and _x _y _i = admit () // see issue #423
let get_bit_or _x _y _i = admit () // see issue #423
let get_bit_shl _x _y _i = admit () // see issue #423
let get_bit_shr _x _y _i = admit () // see issue #423

let get_bit_cast #t #u x nth
  = reveal_opaque (`%get_bit) (get_bit x nth);
    reveal_opaque (`%get_bit) (get_bit (cast_mod #t #u x <: int_t u) nth);
    admit () // see issue #423

let get_bit_cast_extend #t #u x nth
  = admit () // see issue #423
