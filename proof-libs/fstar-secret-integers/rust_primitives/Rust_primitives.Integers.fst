module Rust_primitives.Integers

#set-options "--z3rlimit 100 --fuel 0 --ifuel 1"


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

let mk_int_l #t #l a = LI.mk_int #t #l a
let mk_int_equiv_lemma #_ = admit ()
let mk_int_v_lemma #t a = ()
let v_mk_int_lemma #t a = ()

let add_mod_equiv_lemma #t #l #l' a b =
  LI.add_mod_lemma #_ #(meet l l') (classify a) (classify b)
  
let add_equiv_lemma #t #l #l' a b =
  LI.add_lemma #_ #(meet l l') (classify a) (classify b)
  
let incr_equiv_lemma #t #l a = LI.incr_lemma #t #l a

let mul_mod_equiv_lemma #t #l #l' a b =
  LI.mul_mod_lemma #_ #(meet l l') (classify a) (classify b)

let mul_equiv_lemma #t #l #l' a b =
  LI.mul_lemma #_ #(meet l l') (classify a) (classify b)

let sub_mod_equiv_lemma #t #l #l' a b =
  LI.sub_mod_lemma #_ #(meet l l') (classify a) (classify b)

let sub_equiv_lemma #t #l #l' a b =
  LI.sub_lemma #_ #(meet l l') (classify a) (classify b)

let decr_equiv_lemma #t a = LI.decr_lemma #t  a

let div_equiv_lemma #t a b = admit(); LI.div_lemma #t a b
let mod_equiv_lemma #t a b = admit(); LI.mod_lemma #t a b

let lognot #t a = LI.lognot #t a
let lognot_lemma #t a = admit()

let logxor #t #l1 #l2 a b = LI.logxor #t #(meet l1 l2) (classify a) (classify b)
let logxor_lemma #t a b = admit()

let logand #t #l1 #l2 a b = LI.logand #t #(meet l1 l2) (classify a) (classify b)
let logand_lemma #t a b = admit()
let logand_mask_lemma #t a b = admit()

let logor #t #l1 #l2 a b = LI.logor #t #(meet l1 l2) (classify a) (classify b)
let logor_lemma #t a b = admit()

let shift_right_equiv_lemma #t a b = admit()
let shift_left_equiv_lemma #t a b = admit()

let rotate_right #t a b = LI.rotate_right #t  a (cast b)
let rotate_right_equiv_lemma #t a b = ()
let rotate_left #t a b = LI.rotate_left #t  a (cast b)
let rotate_left_equiv_lemma #t a b = ()

let abs_int_equiv_lemma #t a = admit()

let neg_equiv_lemma #_ _ = admit()

let get_bit_and _x _y _i = admit ()
let get_bit_or _x _y _i = admit ()
let get_bit_shl _x _y _i = admit ()
let get_bit_shr _x _y _i = admit ()

let get_bit_cast #t #u #l x nth
  = reveal_opaque (`%get_bit) (get_bit x nth);
    reveal_opaque (`%get_bit) (get_bit (cast_mod #t #u x <: int_t_l u l) nth);
    admit ()

let get_bit_cast_extend #t #u x nth
  = admit ()
