(set-option :auto_config false)
(set-option :smt.mbqi false)
(set-option :smt.case_split 3)
(set-option :smt.qi.eager_threshold 100.0)
(set-option :smt.delay_units true)
(set-option :smt.arith.solver 2)
(set-option :smt.arith.nl false)
(set-option :pi.enabled false)
(set-option :rewriter.sort_disjunctions false)

;; Prelude

;; AIR prelude
(declare-sort %%Function%% 0)

(declare-sort FuelId 0)
(declare-sort Fuel 0)
(declare-const zero Fuel)
(declare-fun succ (Fuel) Fuel)
(declare-fun fuel_bool (FuelId) Bool)
(declare-fun fuel_bool_default (FuelId) Bool)
(declare-const fuel_defaults Bool)
(assert
 (=>
  fuel_defaults
  (forall ((id FuelId)) (!
    (= (fuel_bool id) (fuel_bool_default id))
    :pattern ((fuel_bool id))
    :qid prelude_fuel_defaults
    :skolemid skolem_prelude_fuel_defaults
))))
(declare-datatypes ((fndef 0)) (((fndef_singleton))))
(declare-sort Poly 0)
(declare-sort Height 0)
(declare-fun I (Int) Poly)
(declare-fun B (Bool) Poly)
(declare-fun F (fndef) Poly)
(declare-fun %I (Poly) Int)
(declare-fun %B (Poly) Bool)
(declare-fun %F (Poly) fndef)

(declare-sort Type 0)
(declare-const BOOL Type)
(declare-const INT Type)
(declare-const NAT Type)
(declare-const CHAR Type)
(declare-fun UINT (Int) Type)
(declare-fun SINT (Int) Type)
(declare-fun CONST_INT (Int) Type)

;c this means "decoration"
(declare-sort Dcr 0)
(declare-const $ Dcr) ;c nil, i.e. no decoration
(declare-fun REF (Dcr) Dcr)
(declare-fun MUT_REF (Dcr) Dcr)
(declare-fun BOX (Dcr Type Dcr) Dcr)
(declare-fun RC (Dcr Type Dcr) Dcr)
(declare-fun ARC (Dcr Type Dcr) Dcr)
(declare-fun GHOST (Dcr) Dcr)
(declare-fun TRACKED (Dcr) Dcr)
(declare-fun NEVER (Dcr) Dcr)
(declare-fun CONST_PTR (Dcr) Dcr)
(declare-fun ARRAY (Dcr Type Dcr Type) Type)
(declare-fun SLICE (Dcr Type) Type)

(declare-const STRSLICE Type)
(declare-const ALLOCATOR_GLOBAL Type)
(declare-fun PTR (Dcr Type) Type)
(declare-fun has_type (Poly Type) Bool)
(declare-fun as_type (Poly Type) Poly)
(declare-fun mk_fun (%%Function%%) %%Function%%)
(declare-fun const_int (Type) Int)

(assert
 (forall ((i Int)) (!
   (= i (const_int (CONST_INT i)))
   :pattern ((CONST_INT i))
   :qid prelude_type_id_const_int
   :skolemid skolem_prelude_type_id_const_int
)))

(assert
 (forall ((b Bool)) (!
   (has_type (B b) BOOL)
   :pattern ((has_type (B b) BOOL))
   :qid prelude_has_type_bool
   :skolemid skolem_prelude_has_type_bool
)))

(assert
 (forall ((x Poly) (t Type)) (!
   (and
    (has_type (as_type x t) t)
    (=>
     (has_type x t)
     (= x (as_type x t))
   ))
   :pattern ((as_type x t))
   :qid prelude_as_type
   :skolemid skolem_prelude_as_type
)))

(assert
 (forall ((x %%Function%%)) (!
   (= (mk_fun x) x)
   :pattern ((mk_fun x))
   :qid prelude_mk_fun
   :skolemid skolem_prelude_mk_fun
)))

(assert
 (forall ((x Bool)) (!
   (= x (%B (B x)))
   :pattern ((B x))
   :qid prelude_unbox_box_bool
   :skolemid skolem_prelude_unbox_box_bool
)))

(assert
 (forall ((x Int)) (!
   (= x (%I (I x)))
   :pattern ((I x))
   :qid prelude_unbox_box_int
   :skolemid skolem_prelude_unbox_box_int
)))

(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x BOOL)
    (= x (B (%B x)))
   )
   :pattern ((has_type x BOOL))
   :qid prelude_box_unbox_bool
   :skolemid skolem_prelude_box_unbox_bool
)))

(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x INT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x INT))
   :qid prelude_box_unbox_int
   :skolemid skolem_prelude_box_unbox_int
)))

(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (= x (I (%I x)))
   )
   :pattern ((has_type x NAT))
   :qid prelude_box_unbox_nat
   :skolemid skolem_prelude_box_unbox_nat
)))

(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_box_unbox_uint
   :skolemid skolem_prelude_box_unbox_uint
)))

(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (= x (I (%I x)))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_box_unbox_sint
   :skolemid skolem_prelude_box_unbox_sint
)))

(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x CHAR)
    (= x (I (%I x)))
   )
   :pattern ((has_type x CHAR))
   :qid prelude_box_unbox_char
   :skolemid skolem_prelude_box_unbox_char
)))

(declare-fun ext_eq (Bool Type Poly Poly) Bool)
(assert
 (forall ((deep Bool) (t Type) (x Poly) (y Poly)) (!
   (= (= x y) (ext_eq deep t x y))
   :pattern ((ext_eq deep t x y))
   :qid prelude_ext_eq
   :skolemid skolem_prelude_ext_eq
)))
(declare-const SZ Int)
(assert
 (or
  (= SZ 32)
  (= SZ 64)
))
(declare-fun uHi (Int) Int)
(declare-fun iLo (Int) Int)
(declare-fun iHi (Int) Int)
(assert
 (= (uHi 8) 256)
)
(assert
 (= (uHi 16) 65536)
)
(assert
 (= (uHi 32) 4294967296)
)
(assert
 (= (uHi 64) 18446744073709551616)
)
(assert
 (= (uHi 128) (+ 1 340282366920938463463374607431768211455))
)
(assert
 (= (iLo 8) (- 128))
)
(assert
 (= (iLo 16) (- 32768))
)
(assert
 (= (iLo 32) (- 2147483648))
)
(assert
 (= (iLo 64) (- 9223372036854775808))
)
(assert
 (= (iLo 128) (- 170141183460469231731687303715884105728))
)
(assert
 (= (iHi 8) 128)
)
(assert
 (= (iHi 16) 32768)
)
(assert
 (= (iHi 32) 2147483648)
)
(assert
 (= (iHi 64) 9223372036854775808)
)
(assert
 (= (iHi 128) 170141183460469231731687303715884105728)
)
(declare-fun nClip (Int) Int)
(declare-fun uClip (Int Int) Int)
(declare-fun iClip (Int Int) Int)
(declare-fun charClip (Int) Int)
(assert
 (forall ((i Int)) (!
   (and
    (<= 0 (nClip i))
    (=>
     (<= 0 i)
     (= i (nClip i))
   ))
   :pattern ((nClip i))
   :qid prelude_nat_clip
   :skolemid skolem_prelude_nat_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= 0 (uClip bits i))
    (< (uClip bits i) (uHi bits))
    (=>
     (and
      (<= 0 i)
      (< i (uHi bits))
     )
     (= i (uClip bits i))
   ))
   :pattern ((uClip bits i))
   :qid prelude_u_clip
   :skolemid skolem_prelude_u_clip
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (and
    (<= (iLo bits) (iClip bits i))
    (< (iClip bits i) (iHi bits))
    (=>
     (and
      (<= (iLo bits) i)
      (< i (iHi bits))
     )
     (= i (iClip bits i))
   ))
   :pattern ((iClip bits i))
   :qid prelude_i_clip
   :skolemid skolem_prelude_i_clip
)))
(assert
 (forall ((i Int)) (!
   (and
    (or
     (and
      (<= 0 (charClip i))
      (<= (charClip i) 55295)
     )
     (and
      (<= 57344 (charClip i))
      (<= (charClip i) 1114111)
    ))
    (=>
     (or
      (and
       (<= 0 i)
       (<= i 55295)
      )
      (and
       (<= 57344 i)
       (<= i 1114111)
     ))
     (= i (charClip i))
   ))
   :pattern ((charClip i))
   :qid prelude_char_clip
   :skolemid skolem_prelude_char_clip
)))
(declare-fun uInv (Int Int) Bool)
(declare-fun iInv (Int Int) Bool)
(declare-fun charInv (Int) Bool)
(assert
 (forall ((bits Int) (i Int)) (!
   (= (uInv bits i) (and
     (<= 0 i)
     (< i (uHi bits))
   ))
   :pattern ((uInv bits i))
   :qid prelude_u_inv
   :skolemid skolem_prelude_u_inv
)))
(assert
 (forall ((bits Int) (i Int)) (!
   (= (iInv bits i) (and
     (<= (iLo bits) i)
     (< i (iHi bits))
   ))
   :pattern ((iInv bits i))
   :qid prelude_i_inv
   :skolemid skolem_prelude_i_inv
)))
(assert
 (forall ((i Int)) (!
   (= (charInv i) (or
     (and
      (<= 0 i)
      (<= i 55295)
     )
     (and
      (<= 57344 i)
      (<= i 1114111)
   )))
   :pattern ((charInv i))
   :qid prelude_char_inv
   :skolemid skolem_prelude_char_inv
)))
(assert
 (forall ((x Int)) (!
   (has_type (I x) INT)
   :pattern ((has_type (I x) INT))
   :qid prelude_has_type_int
   :skolemid skolem_prelude_has_type_int
)))
(assert
 (forall ((x Int)) (!
   (=>
    (<= 0 x)
    (has_type (I x) NAT)
   )
   :pattern ((has_type (I x) NAT))
   :qid prelude_has_type_nat
   :skolemid skolem_prelude_has_type_nat
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (uInv bits x)
    (has_type (I x) (UINT bits))
   )
   :pattern ((has_type (I x) (UINT bits)))
   :qid prelude_has_type_uint
   :skolemid skolem_prelude_has_type_uint
)))
(assert
 (forall ((bits Int) (x Int)) (!
   (=>
    (iInv bits x)
    (has_type (I x) (SINT bits))
   )
   :pattern ((has_type (I x) (SINT bits)))
   :qid prelude_has_type_sint
   :skolemid skolem_prelude_has_type_sint
)))
(assert
 (forall ((x Int)) (!
   (=>
    (charInv x)
    (has_type (I x) CHAR)
   )
   :pattern ((has_type (I x) CHAR))
   :qid prelude_has_type_char
   :skolemid skolem_prelude_has_type_char
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x NAT)
    (<= 0 (%I x))
   )
   :pattern ((has_type x NAT))
   :qid prelude_unbox_int
   :skolemid skolem_prelude_unbox_int
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (UINT bits))
    (uInv bits (%I x))
   )
   :pattern ((has_type x (UINT bits)))
   :qid prelude_unbox_uint
   :skolemid skolem_prelude_unbox_uint
)))
(assert
 (forall ((bits Int) (x Poly)) (!
   (=>
    (has_type x (SINT bits))
    (iInv bits (%I x))
   )
   :pattern ((has_type x (SINT bits)))
   :qid prelude_unbox_sint
   :skolemid skolem_prelude_unbox_sint
)))
(declare-fun Add (Int Int) Int)
(declare-fun Sub (Int Int) Int)
(declare-fun Mul (Int Int) Int)
(declare-fun EucDiv (Int Int) Int)
(declare-fun EucMod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (= (Add x y) (+ x y))
   :pattern ((Add x y))
   :qid prelude_add
   :skolemid skolem_prelude_add
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Sub x y) (- x y))
   :pattern ((Sub x y))
   :qid prelude_sub
   :skolemid skolem_prelude_sub
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (Mul x y) (* x y))
   :pattern ((Mul x y))
   :qid prelude_mul
   :skolemid skolem_prelude_mul
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucDiv x y) (div x y))
   :pattern ((EucDiv x y))
   :qid prelude_eucdiv
   :skolemid skolem_prelude_eucdiv
)))
(assert
 (forall ((x Int) (y Int)) (!
   (= (EucMod x y) (mod x y))
   :pattern ((EucMod x y))
   :qid prelude_eucmod
   :skolemid skolem_prelude_eucmod
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (<= 0 y)
    )
    (<= 0 (Mul x y))
   )
   :pattern ((Mul x y))
   :qid prelude_mul_nats
   :skolemid skolem_prelude_mul_nats
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucDiv x y))
     (<= (EucDiv x y) x)
   ))
   :pattern ((EucDiv x y))
   :qid prelude_div_unsigned_in_bounds
   :skolemid skolem_prelude_div_unsigned_in_bounds
)))
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (and
     (<= 0 x)
     (< 0 y)
    )
    (and
     (<= 0 (EucMod x y))
     (< (EucMod x y) y)
   ))
   :pattern ((EucMod x y))
   :qid prelude_mod_unsigned_in_bounds
   :skolemid skolem_prelude_mod_unsigned_in_bounds
)))
(declare-fun bitxor (Poly Poly) Int)
(declare-fun bitand (Poly Poly) Int)
(declare-fun bitor (Poly Poly) Int)
(declare-fun bitshr (Poly Poly) Int)
(declare-fun bitshl (Poly Poly) Int)
(declare-fun bitnot (Poly) Int)
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitxor x y))
   )
   :pattern ((uClip bits (bitxor x y)))
   :qid prelude_bit_xor_u_inv
   :skolemid skolem_prelude_bit_xor_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitxor x y))
   )
   :pattern ((iClip bits (bitxor x y)))
   :qid prelude_bit_xor_i_inv
   :skolemid skolem_prelude_bit_xor_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitor x y))
   )
   :pattern ((uClip bits (bitor x y)))
   :qid prelude_bit_or_u_inv
   :skolemid skolem_prelude_bit_or_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitor x y))
   )
   :pattern ((iClip bits (bitor x y)))
   :qid prelude_bit_or_i_inv
   :skolemid skolem_prelude_bit_or_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (uInv bits (%I y))
    )
    (uInv bits (bitand x y))
   )
   :pattern ((uClip bits (bitand x y)))
   :qid prelude_bit_and_u_inv
   :skolemid skolem_prelude_bit_and_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (iInv bits (%I y))
    )
    (iInv bits (bitand x y))
   )
   :pattern ((iClip bits (bitand x y)))
   :qid prelude_bit_and_i_inv
   :skolemid skolem_prelude_bit_and_i_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (uInv bits (%I x))
     (<= 0 (%I y))
    )
    (uInv bits (bitshr x y))
   )
   :pattern ((uClip bits (bitshr x y)))
   :qid prelude_bit_shr_u_inv
   :skolemid skolem_prelude_bit_shr_u_inv
)))
(assert
 (forall ((x Poly) (y Poly) (bits Int)) (!
   (=>
    (and
     (iInv bits (%I x))
     (<= 0 (%I y))
    )
    (iInv bits (bitshr x y))
   )
   :pattern ((iClip bits (bitshr x y)))
   :qid prelude_bit_shr_i_inv
   :skolemid skolem_prelude_bit_shr_i_inv
)))
(declare-fun singular_mod (Int Int) Int)
(assert
 (forall ((x Int) (y Int)) (!
   (=>
    (not (= y 0))
    (= (EucMod x y) (singular_mod x y))
   )
   :pattern ((singular_mod x y))
   :qid prelude_singularmod
   :skolemid skolem_prelude_singularmod
)))
(declare-fun closure_req (Type Dcr Type Poly Poly) Bool)
(declare-fun closure_ens (Type Dcr Type Poly Poly Poly) Bool)
(declare-fun height (Poly) Height)
(declare-fun height_lt (Height Height) Bool)
(declare-fun fun_from_recursive_field (Poly) Poly)
(declare-fun check_decrease_int (Int Int Bool) Bool)
(assert
 (forall ((cur Int) (prev Int) (otherwise Bool)) (!
   (= (check_decrease_int cur prev otherwise) (or
     (and
      (<= 0 cur)
      (< cur prev)
     )
     (and
      (= cur prev)
      otherwise
   )))
   :pattern ((check_decrease_int cur prev otherwise))
   :qid prelude_check_decrease_int
   :skolemid skolem_prelude_check_decrease_int
)))
(declare-fun check_decrease_height (Poly Poly Bool) Bool)
(assert
 (forall ((cur Poly) (prev Poly) (otherwise Bool)) (!
   (= (check_decrease_height cur prev otherwise) (or
     (height_lt (height cur) (height prev))
     (and
      (= (height cur) (height prev))
      otherwise
   )))
   :pattern ((check_decrease_height cur prev otherwise))
   :qid prelude_check_decrease_height
   :skolemid skolem_prelude_check_decrease_height
)))
(assert
 (forall ((x Height) (y Height)) (!
   (= (height_lt x y) (and
     ((_ partial-order 0) x y)
     (not (= x y))
   ))
   :pattern ((height_lt x y))
   :qid prelude_height_lt
   :skolemid skolem_prelude_height_lt
)))

;; MODULE 'root module'

;; Fuel
(declare-const fuel%vstd!std_specs.result.impl&%0.is_Ok. FuelId)
(declare-const fuel%vstd!std_specs.result.impl&%0.get_Ok_0. FuelId)
(declare-const fuel%lib_verus!impl&%2.arrow_verification_id. FuelId)
(declare-const fuel%lib_verus!impl&%2.arrow_WaitToApply_verification_id. FuelId)
(declare-const fuel%vstd!array.group_array_axioms. FuelId)
(declare-const fuel%vstd!map.group_map_axioms. FuelId)
(declare-const fuel%vstd!multiset.group_multiset_axioms. FuelId)
(declare-const fuel%vstd!raw_ptr.group_raw_ptr_axioms. FuelId)
(declare-const fuel%vstd!seq.group_seq_axioms. FuelId)
(declare-const fuel%vstd!seq_lib.group_seq_lib_default. FuelId)
(declare-const fuel%vstd!set.group_set_axioms. FuelId)
(declare-const fuel%vstd!set_lib.group_set_lib_axioms. FuelId)
(declare-const fuel%vstd!slice.group_slice_axioms. FuelId)
(declare-const fuel%vstd!string.group_string_axioms. FuelId)
(declare-const fuel%vstd!std_specs.bits.group_bits_axioms. FuelId)
(declare-const fuel%vstd!std_specs.control_flow.group_control_flow_axioms. FuelId)
(declare-const fuel%vstd!std_specs.range.group_range_axioms. FuelId)
(declare-const fuel%vstd!std_specs.vec.group_vec_axioms. FuelId)
(declare-const fuel%vstd!group_vstd_default. FuelId)
(assert
 (distinct fuel%vstd!std_specs.result.impl&%0.is_Ok. fuel%vstd!std_specs.result.impl&%0.get_Ok_0.
  fuel%lib_verus!impl&%2.arrow_verification_id. fuel%lib_verus!impl&%2.arrow_WaitToApply_verification_id.
  fuel%vstd!array.group_array_axioms. fuel%vstd!map.group_map_axioms. fuel%vstd!multiset.group_multiset_axioms.
  fuel%vstd!raw_ptr.group_raw_ptr_axioms. fuel%vstd!seq.group_seq_axioms. fuel%vstd!seq_lib.group_seq_lib_default.
  fuel%vstd!set.group_set_axioms. fuel%vstd!set_lib.group_set_lib_axioms. fuel%vstd!slice.group_slice_axioms.
  fuel%vstd!string.group_string_axioms. fuel%vstd!std_specs.bits.group_bits_axioms.
  fuel%vstd!std_specs.control_flow.group_control_flow_axioms. fuel%vstd!std_specs.range.group_range_axioms.
  fuel%vstd!std_specs.vec.group_vec_axioms. fuel%vstd!group_vstd_default.
))
(assert
 (fuel_bool_default fuel%vstd!group_vstd_default.)
)
(assert
 (=>
  (fuel_bool_default fuel%vstd!group_vstd_default.)
  (and
   (fuel_bool_default fuel%vstd!seq.group_seq_axioms.)
   (fuel_bool_default fuel%vstd!seq_lib.group_seq_lib_default.)
   (fuel_bool_default fuel%vstd!map.group_map_axioms.)
   (fuel_bool_default fuel%vstd!set.group_set_axioms.)
   (fuel_bool_default fuel%vstd!set_lib.group_set_lib_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.bits.group_bits_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.control_flow.group_control_flow_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.vec.group_vec_axioms.)
   (fuel_bool_default fuel%vstd!slice.group_slice_axioms.)
   (fuel_bool_default fuel%vstd!array.group_array_axioms.)
   (fuel_bool_default fuel%vstd!multiset.group_multiset_axioms.)
   (fuel_bool_default fuel%vstd!string.group_string_axioms.)
   (fuel_bool_default fuel%vstd!std_specs.range.group_range_axioms.)
   (fuel_bool_default fuel%vstd!raw_ptr.group_raw_ptr_axioms.)
)))

;; Datatypes
(declare-datatypes
  ( (core!result.Result. 0)
    (lib_verus!Error. 0)
    (lib_verus!State. 0)
    (lib_verus!ProtocolLibrary. 0)
    (lib_verus!UnverifiedMessage. 0)
    (lib_verus!VerifiedMessage. 0)
    (tuple%0. 0))
  ( ( (core!result.Result./Ok (core!result.Result./Ok/?0 Poly))
      (core!result.Result./Err (core!result.Result./Err/?0 Poly)))
    ( (lib_verus!Error./AuthenticationFailed)
      (lib_verus!Error./MessageTooOld)
      (lib_verus!Error./NotAcceptingNew)
      (lib_verus!Error./NotReadyToApply)
      (lib_verus!Error./UnexpectedVerifiedMsg))
    ( (lib_verus!State./Idle)
      (lib_verus!State./WaitToApply
        (lib_verus!State./WaitToApply/?verification_id Int)))
    ( (lib_verus!ProtocolLibrary./ProtocolLibrary
        (lib_verus!ProtocolLibrary./ProtocolLibrary/?state lib_verus!State.)
        (lib_verus!ProtocolLibrary./ProtocolLibrary/?value Int)
        (lib_verus!ProtocolLibrary./ProtocolLibrary/?last_changed Int)
        (lib_verus!ProtocolLibrary./ProtocolLibrary/?msg_ctr Int)))
    ( (lib_verus!UnverifiedMessage./UnverifiedMessage
        (lib_verus!UnverifiedMessage./UnverifiedMessage/?sender Int)
        (lib_verus!UnverifiedMessage./UnverifiedMessage/?authenticator Int)
        (lib_verus!UnverifiedMessage./UnverifiedMessage/?timestamp Int)
        (lib_verus!UnverifiedMessage./UnverifiedMessage/?value Int)))
    ( (lib_verus!VerifiedMessage./VerifiedMessage
        (lib_verus!VerifiedMessage./VerifiedMessage/?sender Int)
        (lib_verus!VerifiedMessage./VerifiedMessage/?timestamp Int)
        (lib_verus!VerifiedMessage./VerifiedMessage/?value Int)
        (lib_verus!VerifiedMessage./VerifiedMessage/?verification_id Int)))
    ((tuple%0./tuple%0))))

(declare-fun core!result.Result./Ok/0 (core!result.Result.) Poly)
(declare-fun core!result.Result./Err/0 (core!result.Result.) Poly)
(declare-fun lib_verus!State./WaitToApply/verification_id (lib_verus!State.) Int)
(declare-fun lib_verus!ProtocolLibrary./ProtocolLibrary/state
  (lib_verus!ProtocolLibrary.) lib_verus!State.)
(declare-fun lib_verus!ProtocolLibrary./ProtocolLibrary/value
  (lib_verus!ProtocolLibrary.) Int)
(declare-fun lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed
  (lib_verus!ProtocolLibrary.) Int)
  (declare-fun lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr
  (lib_verus!ProtocolLibrary.) Int)
(declare-fun lib_verus!UnverifiedMessage./UnverifiedMessage/sender
  (lib_verus!UnverifiedMessage.) Int)
(declare-fun lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator
  (lib_verus!UnverifiedMessage.) Int)
(declare-fun lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp
  (lib_verus!UnverifiedMessage.) Int)
(declare-fun lib_verus!UnverifiedMessage./UnverifiedMessage/value
  (lib_verus!UnverifiedMessage.) Int)
(declare-fun lib_verus!VerifiedMessage./VerifiedMessage/sende
  (lib_verus!VerifiedMessage.) Int)
(declare-fun lib_verus!VerifiedMessage./VerifiedMessage/timestam
  (lib_verus!VerifiedMessage.) Int)
(declare-fun lib_verus!VerifiedMessage./VerifiedMessage/valu
  (lib_verus!VerifiedMessage.) Int)
(declare-fun lib_verus!VerifiedMessage./VerifiedMessage/verification_i
  (lib_verus!VerifiedMessage.) Int)

(declare-fun TYPE%core!result.Result. (Dcr Type Dcr Type) Type)
(declare-const TYPE%lib_verus!Error. Type)
(declare-const TYPE%lib_verus!State. Type)
(declare-const TYPE%lib_verus!ProtocolLibrary. Type)
(declare-const TYPE%lib_verus!UnverifiedMessage. Type)
(declare-const TYPE%lib_verus!VerifiedMessage. Type)
(declare-const TYPE%tuple%0. Type)

(declare-fun Poly%core!result.Result. (core!result.Result.) Poly)
(declare-fun %Poly%core!result.Result. (Poly) core!result.Result.)
(declare-fun Poly%lib_verus!Error. (lib_verus!Error.) Poly)
(declare-fun %Poly%lib_verus!Error. (Poly) lib_verus!Error.)
(declare-fun Poly%lib_verus!State. (lib_verus!State.) Poly)
(declare-fun %Poly%lib_verus!State. (Poly) lib_verus!State.)
(declare-fun Poly%lib_verus!ProtocolLibrary. (lib_verus!ProtocolLibrary.) Poly)
(declare-fun %Poly%lib_verus!ProtocolLibrary. (Poly) lib_verus!ProtocolLibrary.)
(declare-fun Poly%lib_verus!UnverifiedMessage. (lib_verus!UnverifiedMessage.) Poly)
(declare-fun %Poly%lib_verus!UnverifiedMessage. (Poly) lib_verus!UnverifiedMessage.)
(declare-fun Poly%lib_verus!VerifiedMessage. (lib_verus!VerifiedMessage.) Poly)
(declare-fun %Poly%lib_verus!VerifiedMessage. (Poly) lib_verus!VerifiedMessage.)
(declare-fun Poly%tuple%0. (tuple%0.) Poly)
(declare-fun %Poly%tuple%0. (Poly) tuple%0.)

(assert
 (forall ((x core!result.Result.)) (!
   (= x (%Poly%core!result.Result. (Poly%core!result.Result. x)))
   :pattern ((Poly%core!result.Result. x))
   :qid internal_core__result__Result_box_axiom_definition
   :skolemid skolem_internal_core__result__Result_box_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!result.Result. T&. T& E&. E&))
    (= x (Poly%core!result.Result. (%Poly%core!result.Result. x)))
   )
   :pattern ((has_type x (TYPE%core!result.Result. T&. T& E&. E&)))
   :qid internal_core__result__Result_unbox_axiom_definition
   :skolemid skolem_internal_core__result__Result_unbox_axiom_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (_0! Poly)) (!
   (=>
    (has_type _0! T&)
    (has_type (Poly%core!result.Result. (core!result.Result./Ok _0!)) (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :pattern ((has_type (Poly%core!result.Result. (core!result.Result./Ok _0!)) (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :qid internal_core!result.Result./Ok_constructor_definition
   :skolemid skolem_internal_core!result.Result./Ok_constructor_definition
)))
(assert
 (forall ((x core!result.Result.)) (!
   (= (core!result.Result./Ok/0 x) (core!result.Result./Ok/?0 x))
   :pattern ((core!result.Result./Ok/0 x))
   :qid internal_core!result.Result./Ok/0_accessor_definition
   :skolemid skolem_internal_core!result.Result./Ok/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!result.Result. T&. T& E&. E&))
    (has_type (core!result.Result./Ok/0 (%Poly%core!result.Result. x)) T&)
   )
   :pattern ((core!result.Result./Ok/0 (%Poly%core!result.Result. x)) (has_type x (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :qid internal_core!result.Result./Ok/0_invariant_definition
   :skolemid skolem_internal_core!result.Result./Ok/0_invariant_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (_0! Poly)) (!
   (=>
    (has_type _0! E&)
    (has_type (Poly%core!result.Result. (core!result.Result./Err _0!)) (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :pattern ((has_type (Poly%core!result.Result. (core!result.Result./Err _0!)) (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :qid internal_core!result.Result./Err_constructor_definition
   :skolemid skolem_internal_core!result.Result./Err_constructor_definition
)))
(assert
 (forall ((x core!result.Result.)) (!
   (= (core!result.Result./Err/0 x) (core!result.Result./Err/?0 x))
   :pattern ((core!result.Result./Err/0 x))
   :qid internal_core!result.Result./Err/0_accessor_definition
   :skolemid skolem_internal_core!result.Result./Err/0_accessor_definition
)))
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (x Poly)) (!
   (=>
    (has_type x (TYPE%core!result.Result. T&. T& E&. E&))
    (has_type (core!result.Result./Err/0 (%Poly%core!result.Result. x)) E&)
   )
   :pattern ((core!result.Result./Err/0 (%Poly%core!result.Result. x)) (has_type x (TYPE%core!result.Result.
      T&. T& E&. E&
   )))
   :qid internal_core!result.Result./Err/0_invariant_definition
   :skolemid skolem_internal_core!result.Result./Err/0_invariant_definition
)))
(assert
 (forall ((x core!result.Result.)) (!
   (=>
    (is-core!result.Result./Ok x)
    (height_lt (height (core!result.Result./Ok/0 x)) (height (Poly%core!result.Result. x)))
   )
   :pattern ((height (core!result.Result./Ok/0 x)))
   :qid prelude_datatype_height_core!result.Result./Ok/0
   :skolemid skolem_prelude_datatype_height_core!result.Result./Ok/0
)))
(assert
 (forall ((x core!result.Result.)) (!
   (=>
    (is-core!result.Result./Err x)
    (height_lt (height (core!result.Result./Err/0 x)) (height (Poly%core!result.Result.
       x
   ))))
   :pattern ((height (core!result.Result./Err/0 x)))
   :qid prelude_datatype_height_core!result.Result./Err/0
   :skolemid skolem_prelude_datatype_height_core!result.Result./Err/0
)))
(assert
 (forall ((x lib_verus!Error.)) (!
   (= x (%Poly%lib_verus!Error. (Poly%lib_verus!Error. x)))
   :pattern ((Poly%lib_verus!Error. x))
   :qid internal_lib_verus__Error_box_axiom_definition
   :skolemid skolem_internal_lib_verus__Error_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!Error.)
    (= x (Poly%lib_verus!Error. (%Poly%lib_verus!Error. x)))
   )
   :pattern ((has_type x TYPE%lib_verus!Error.))
   :qid internal_lib_verus__Error_unbox_axiom_definition
   :skolemid skolem_internal_lib_verus__Error_unbox_axiom_definition
)))
(assert
 (forall ((x lib_verus!Error.)) (!
   (has_type (Poly%lib_verus!Error. x) TYPE%lib_verus!Error.)
   :pattern ((has_type (Poly%lib_verus!Error. x) TYPE%lib_verus!Error.))
   :qid internal_lib_verus__Error_has_type_always_definition
   :skolemid skolem_internal_lib_verus__Error_has_type_always_definition
)))
(assert
 (forall ((x lib_verus!State.)) (!
   (= x (%Poly%lib_verus!State. (Poly%lib_verus!State. x)))
   :pattern ((Poly%lib_verus!State. x))
   :qid internal_lib_verus__State_box_axiom_definition
   :skolemid skolem_internal_lib_verus__State_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!State.)
    (= x (Poly%lib_verus!State. (%Poly%lib_verus!State. x)))
   )
   :pattern ((has_type x TYPE%lib_verus!State.))
   :qid internal_lib_verus__State_unbox_axiom_definition
   :skolemid skolem_internal_lib_verus__State_unbox_axiom_definition
)))
(assert
 (has_type (Poly%lib_verus!State. lib_verus!State./Idle) TYPE%lib_verus!State.)
)
(assert
 (forall ((_verification_id! Int)) (!
   (=>
    (uInv SZ _verification_id!)
    (has_type (Poly%lib_verus!State. (lib_verus!State./WaitToApply _verification_id!))
     TYPE%lib_verus!State.
   ))
   :pattern ((has_type (Poly%lib_verus!State. (lib_verus!State./WaitToApply _verification_id!))
     TYPE%lib_verus!State.
   ))
   :qid internal_lib_verus!State./WaitToApply_constructor_definition
   :skolemid skolem_internal_lib_verus!State./WaitToApply_constructor_definition
)))
(assert
 (forall ((x lib_verus!State.)) (!
   (= (lib_verus!State./WaitToApply/verification_id x) (lib_verus!State./WaitToApply/?verification_id
     x
   ))
   :pattern ((lib_verus!State./WaitToApply/verification_id x))
   :qid internal_lib_verus!State./WaitToApply/verification_id_accessor_definition
   :skolemid skolem_internal_lib_verus!State./WaitToApply/verification_id_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!State.)
    (uInv SZ (lib_verus!State./WaitToApply/verification_id (%Poly%lib_verus!State. x)))
   )
   :pattern ((lib_verus!State./WaitToApply/verification_id (%Poly%lib_verus!State. x))
    (has_type x TYPE%lib_verus!State.)
   )
   :qid internal_lib_verus!State./WaitToApply/verification_id_invariant_definition
   :skolemid skolem_internal_lib_verus!State./WaitToApply/verification_id_invariant_definition
)))
(assert
 (forall ((x lib_verus!ProtocolLibrary.)) (!
   (= x (%Poly%lib_verus!ProtocolLibrary. (Poly%lib_verus!ProtocolLibrary. x)))
   :pattern ((Poly%lib_verus!ProtocolLibrary. x))
   :qid internal_lib_verus__ProtocolLibrary_box_axiom_definition
   :skolemid skolem_internal_lib_verus__ProtocolLibrary_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!ProtocolLibrary.)
    (= x (Poly%lib_verus!ProtocolLibrary. (%Poly%lib_verus!ProtocolLibrary. x)))
   )
   :pattern ((has_type x TYPE%lib_verus!ProtocolLibrary.))
   :qid internal_lib_verus__ProtocolLibrary_unbox_axiom_definition
   :skolemid skolem_internal_lib_verus__ProtocolLibrary_unbox_axiom_definition
)))
(assert
 (forall ((_state! lib_verus!State.) (_value! Int) (_last_changed! Int) (_msg_ctr! Int))
  (!
   (=>
    (and
     (has_type (Poly%lib_verus!State. _state!) TYPE%lib_verus!State.)
     (uInv SZ _value!)
     (uInv SZ _last_changed!)
     (uInv SZ _msg_ctr!)
    )
    (has_type (Poly%lib_verus!ProtocolLibrary. (lib_verus!ProtocolLibrary./ProtocolLibrary
       _state! _value! _last_changed! _msg_ctr!
      )
     ) TYPE%lib_verus!ProtocolLibrary.
   ))
   :pattern ((has_type (Poly%lib_verus!ProtocolLibrary. (lib_verus!ProtocolLibrary./ProtocolLibrary
       _state! _value! _last_changed! _msg_ctr!
      )
     ) TYPE%lib_verus!ProtocolLibrary.
   ))
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary_constructor_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary_constructor_definition
)))
(assert
 (forall ((x lib_verus!ProtocolLibrary.)) (!
   (= (lib_verus!ProtocolLibrary./ProtocolLibrary/state x) (lib_verus!ProtocolLibrary./ProtocolLibrary/?state
     x
   ))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/state x))
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/state_accessor_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/state_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!ProtocolLibrary.)
    (has_type (Poly%lib_verus!State. (lib_verus!ProtocolLibrary./ProtocolLibrary/state (
        %Poly%lib_verus!ProtocolLibrary. x
      ))
     ) TYPE%lib_verus!State.
   ))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/state (%Poly%lib_verus!ProtocolLibrary.
      x
     )
    ) (has_type x TYPE%lib_verus!ProtocolLibrary.)
   )
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/state_invariant_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/state_invariant_definition
)))
(assert
 (forall ((x lib_verus!ProtocolLibrary.)) (!
   (= (lib_verus!ProtocolLibrary./ProtocolLibrary/value x) (lib_verus!ProtocolLibrary./ProtocolLibrary/?value
     x
   ))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/value x))
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/value_accessor_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/value_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!ProtocolLibrary.)
    (uInv SZ (lib_verus!ProtocolLibrary./ProtocolLibrary/value (%Poly%lib_verus!ProtocolLibrary.
       x
   ))))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/value (%Poly%lib_verus!ProtocolLibrary.
      x
     )
    ) (has_type x TYPE%lib_verus!ProtocolLibrary.)
   )
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/value_invariant_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/value_invariant_definition
)))
(assert
 (forall ((x lib_verus!ProtocolLibrary.)) (!
   (= (lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed x) (lib_verus!ProtocolLibrary./ProtocolLibrary/?last_changed
     x
   ))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed x))
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed_accessor_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!ProtocolLibrary.)
    (uInv SZ (lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed (%Poly%lib_verus!ProtocolLibrary.
       x
   ))))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed (%Poly%lib_verus!ProtocolLibrary.
      x
     )
    ) (has_type x TYPE%lib_verus!ProtocolLibrary.)
   )
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed_invariant_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/last_changed_invariant_definition
)))
(assert
 (forall ((x lib_verus!ProtocolLibrary.)) (!
   (= (lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr x) (lib_verus!ProtocolLibrary./ProtocolLibrary/?msg_ctr
     x
   ))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr x))
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr_accessor_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!ProtocolLibrary.)
    (uInv SZ (lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr (%Poly%lib_verus!ProtocolLibrary.
       x
   ))))
   :pattern ((lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr (%Poly%lib_verus!ProtocolLibrary.
      x
     )
    ) (has_type x TYPE%lib_verus!ProtocolLibrary.)
   )
   :qid internal_lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr_invariant_definition
   :skolemid skolem_internal_lib_verus!ProtocolLibrary./ProtocolLibrary/msg_ctr_invariant_definition
)))
(assert
 (forall ((x lib_verus!UnverifiedMessage.)) (!
   (= x (%Poly%lib_verus!UnverifiedMessage. (Poly%lib_verus!UnverifiedMessage. x)))
   :pattern ((Poly%lib_verus!UnverifiedMessage. x))
   :qid internal_lib_verus__UnverifiedMessage_box_axiom_definition
   :skolemid skolem_internal_lib_verus__UnverifiedMessage_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!UnverifiedMessage.)
    (= x (Poly%lib_verus!UnverifiedMessage. (%Poly%lib_verus!UnverifiedMessage. x)))
   )
   :pattern ((has_type x TYPE%lib_verus!UnverifiedMessage.))
   :qid internal_lib_verus__UnverifiedMessage_unbox_axiom_definition
   :skolemid skolem_internal_lib_verus__UnverifiedMessage_unbox_axiom_definition
)))
(assert
 (forall ((_sender! Int) (_authenticator! Int) (_timestamp! Int) (_value! Int)) (!
   (=>
    (and
     (uInv SZ _sender!)
     (uInv SZ _authenticator!)
     (uInv SZ _timestamp!)
     (uInv SZ _value!)
    )
    (has_type (Poly%lib_verus!UnverifiedMessage. (lib_verus!UnverifiedMessage./UnverifiedMessage
       _sender! _authenticator! _timestamp! _value!
      )
     ) TYPE%lib_verus!UnverifiedMessage.
   ))
   :pattern ((has_type (Poly%lib_verus!UnverifiedMessage. (lib_verus!UnverifiedMessage./UnverifiedMessage
       _sender! _authenticator! _timestamp! _value!
      )
     ) TYPE%lib_verus!UnverifiedMessage.
   ))
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage_constructor_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage_constructor_definition
)))
(assert
 (forall ((x lib_verus!UnverifiedMessage.)) (!
   (= (lib_verus!UnverifiedMessage./UnverifiedMessage/sender x) (lib_verus!UnverifiedMessage./UnverifiedMessage/?sender
     x
   ))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/sender x))
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/sender_accessor_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/sender_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!UnverifiedMessage.)
    (uInv SZ (lib_verus!UnverifiedMessage./UnverifiedMessage/sender (%Poly%lib_verus!UnverifiedMessage.
       x
   ))))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/sender (%Poly%lib_verus!UnverifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!UnverifiedMessage.)
   )
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/sender_invariant_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/sender_invariant_definition
)))
(assert
 (forall ((x lib_verus!UnverifiedMessage.)) (!
   (= (lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator x) (lib_verus!UnverifiedMessage./UnverifiedMessage/?authenticator
     x
   ))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator x))
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator_accessor_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!UnverifiedMessage.)
    (uInv SZ (lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator (%Poly%lib_verus!UnverifiedMessage.
       x
   ))))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator (%Poly%lib_verus!UnverifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!UnverifiedMessage.)
   )
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator_invariant_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/authenticator_invariant_definition
)))
(assert
 (forall ((x lib_verus!UnverifiedMessage.)) (!
   (= (lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp x) (lib_verus!UnverifiedMessage./UnverifiedMessage/?timestamp
     x
   ))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp x))
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp_accessor_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!UnverifiedMessage.)
    (uInv SZ (lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp (%Poly%lib_verus!UnverifiedMessage.
       x
   ))))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp (%Poly%lib_verus!UnverifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!UnverifiedMessage.)
   )
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp_invariant_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/timestamp_invariant_definition
)))
(assert
 (forall ((x lib_verus!UnverifiedMessage.)) (!
   (= (lib_verus!UnverifiedMessage./UnverifiedMessage/value x) (lib_verus!UnverifiedMessage./UnverifiedMessage/?value
     x
   ))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/value x))
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/value_accessor_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/value_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!UnverifiedMessage.)
    (uInv SZ (lib_verus!UnverifiedMessage./UnverifiedMessage/value (%Poly%lib_verus!UnverifiedMessage.
       x
   ))))
   :pattern ((lib_verus!UnverifiedMessage./UnverifiedMessage/value (%Poly%lib_verus!UnverifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!UnverifiedMessage.)
   )
   :qid internal_lib_verus!UnverifiedMessage./UnverifiedMessage/value_invariant_definition
   :skolemid skolem_internal_lib_verus!UnverifiedMessage./UnverifiedMessage/value_invariant_definition
)))
(assert
 (forall ((x lib_verus!VerifiedMessage.)) (!
   (= x (%Poly%lib_verus!VerifiedMessage. (Poly%lib_verus!VerifiedMessage. x)))
   :pattern ((Poly%lib_verus!VerifiedMessage. x))
   :qid internal_lib_verus__VerifiedMessage_box_axiom_definition
   :skolemid skolem_internal_lib_verus__VerifiedMessage_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!VerifiedMessage.)
    (= x (Poly%lib_verus!VerifiedMessage. (%Poly%lib_verus!VerifiedMessage. x)))
   )
   :pattern ((has_type x TYPE%lib_verus!VerifiedMessage.))
   :qid internal_lib_verus__VerifiedMessage_unbox_axiom_definition
   :skolemid skolem_internal_lib_verus__VerifiedMessage_unbox_axiom_definition
)))
(assert
 (forall ((_sender! Int) (_timestamp! Int) (_value! Int) (_verification_id! Int)) (
   !
   (=>
    (and
     (uInv SZ _sender!)
     (uInv SZ _timestamp!)
     (uInv SZ _value!)
     (uInv SZ _verification_id!)
    )
    (has_type (Poly%lib_verus!VerifiedMessage. (lib_verus!VerifiedMessage./VerifiedMessage
       _sender! _timestamp! _value! _verification_id!
      )
     ) TYPE%lib_verus!VerifiedMessage.
   ))
   :pattern ((has_type (Poly%lib_verus!VerifiedMessage. (lib_verus!VerifiedMessage./VerifiedMessage
       _sender! _timestamp! _value! _verification_id!
      )
     ) TYPE%lib_verus!VerifiedMessage.
   ))
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage_constructor_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage_constructor_definition
)))
(assert
 (forall ((x lib_verus!VerifiedMessage.)) (!
   (= (lib_verus!VerifiedMessage./VerifiedMessage/sender x) (lib_verus!VerifiedMessage./VerifiedMessage/?sender
     x
   ))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/sender x))
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/sender_accessor_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/sender_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!VerifiedMessage.)
    (uInv SZ (lib_verus!VerifiedMessage./VerifiedMessage/sender (%Poly%lib_verus!VerifiedMessage.
       x
   ))))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/sender (%Poly%lib_verus!VerifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!VerifiedMessage.)
   )
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/sender_invariant_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/sender_invariant_definition
)))
(assert
 (forall ((x lib_verus!VerifiedMessage.)) (!
   (= (lib_verus!VerifiedMessage./VerifiedMessage/timestamp x) (lib_verus!VerifiedMessage./VerifiedMessage/?timestamp
     x
   ))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/timestamp x))
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/timestamp_accessor_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/timestamp_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!VerifiedMessage.)
    (uInv SZ (lib_verus!VerifiedMessage./VerifiedMessage/timestamp (%Poly%lib_verus!VerifiedMessage.
       x
   ))))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/timestamp (%Poly%lib_verus!VerifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!VerifiedMessage.)
   )
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/timestamp_invariant_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/timestamp_invariant_definition
)))
(assert
 (forall ((x lib_verus!VerifiedMessage.)) (!
   (= (lib_verus!VerifiedMessage./VerifiedMessage/value x) (lib_verus!VerifiedMessage./VerifiedMessage/?value
     x
   ))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/value x))
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/value_accessor_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/value_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!VerifiedMessage.)
    (uInv SZ (lib_verus!VerifiedMessage./VerifiedMessage/value (%Poly%lib_verus!VerifiedMessage.
       x
   ))))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/value (%Poly%lib_verus!VerifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!VerifiedMessage.)
   )
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/value_invariant_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/value_invariant_definition
)))
(assert
 (forall ((x lib_verus!VerifiedMessage.)) (!
   (= (lib_verus!VerifiedMessage./VerifiedMessage/verification_id x) (lib_verus!VerifiedMessage./VerifiedMessage/?verification_id
     x
   ))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/verification_id x))
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/verification_id_accessor_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/verification_id_accessor_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%lib_verus!VerifiedMessage.)
    (uInv SZ (lib_verus!VerifiedMessage./VerifiedMessage/verification_id (%Poly%lib_verus!VerifiedMessage.
       x
   ))))
   :pattern ((lib_verus!VerifiedMessage./VerifiedMessage/verification_id (%Poly%lib_verus!VerifiedMessage.
      x
     )
    ) (has_type x TYPE%lib_verus!VerifiedMessage.)
   )
   :qid internal_lib_verus!VerifiedMessage./VerifiedMessage/verification_id_invariant_definition
   :skolemid skolem_internal_lib_verus!VerifiedMessage./VerifiedMessage/verification_id_invariant_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (= x (%Poly%tuple%0. (Poly%tuple%0. x)))
   :pattern ((Poly%tuple%0. x))
   :qid internal_crate__tuple__0_box_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_box_axiom_definition
)))
(assert
 (forall ((x Poly)) (!
   (=>
    (has_type x TYPE%tuple%0.)
    (= x (Poly%tuple%0. (%Poly%tuple%0. x)))
   )
   :pattern ((has_type x TYPE%tuple%0.))
   :qid internal_crate__tuple__0_unbox_axiom_definition
   :skolemid skolem_internal_crate__tuple__0_unbox_axiom_definition
)))
(assert
 (forall ((x tuple%0.)) (!
   (has_type (Poly%tuple%0. x) TYPE%tuple%0.)
   :pattern ((has_type (Poly%tuple%0. x) TYPE%tuple%0.))
   :qid internal_crate__tuple__0_has_type_always_definition
   :skolemid skolem_internal_crate__tuple__0_has_type_always_definition
)))

;; Traits
(declare-fun tr_bound%core!fmt.Debug. (Dcr Type) Bool)
(declare-fun tr_bound%vstd!std_specs.result.ResultAdditionalSpecFns. (Dcr Type Dcr
  Type Dcr Type
 ) Bool
)
(assert
 (forall ((Self%&. Dcr) (Self%& Type)) (!
   true
   :pattern ((tr_bound%core!fmt.Debug. Self%&. Self%&))
   :qid internal_core__fmt__Debug_trait_type_bounds_definition
   :skolemid skolem_internal_core__fmt__Debug_trait_type_bounds_definition
)))
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (E&. Dcr) (E& Type)) (!
   true
   :pattern ((tr_bound%vstd!std_specs.result.ResultAdditionalSpecFns. Self%&. Self%& T&.
     T& E&. E&
   ))
   :qid internal_vstd__std_specs__result__ResultAdditionalSpecFns_trait_type_bounds_definition
   :skolemid skolem_internal_vstd__std_specs__result__ResultAdditionalSpecFns_trait_type_bounds_definition
)))

;; Function-Decl vstd::std_specs::result::ResultAdditionalSpecFns::is_Ok
(declare-fun vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.? (Dcr Type Dcr Type
  Dcr Type Poly
 ) Poly
)
(declare-fun vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok%default%.? (Dcr Type
  Dcr Type Dcr Type Poly
 ) Poly
)

;; Function-Decl vstd::std_specs::result::ResultAdditionalSpecFns::get_Ok_0
(declare-fun vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.? (Dcr Type Dcr
  Type Dcr Type Poly
 ) Poly
)
(declare-fun vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0%default%.? (Dcr
  Type Dcr Type Dcr Type Poly
 ) Poly
)

;; Function-Decl lib_verus::State::arrow_verification_id
(declare-fun lib_verus!impl&%2.arrow_verification_id.? (Poly) Int)

;; Function-Decl lib_verus::State::arrow_WaitToApply_verification_id
(declare-fun lib_verus!impl&%2.arrow_WaitToApply_verification_id.? (Poly) Int)

;; Function-Axioms vstd::std_specs::result::ResultAdditionalSpecFns::is_Ok
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (self!
    Poly
   )
  ) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.? Self%&. Self%& T&.
      T& E&. E& self!
     ) BOOL
   ))
   :pattern ((vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.? Self%&. Self%& T&.
     T& E&. E& self!
   ))
   :qid internal_vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::result::ResultAdditionalSpecFns::get_Ok_0
(assert
 (forall ((Self%&. Dcr) (Self%& Type) (T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (self!
    Poly
   )
  ) (!
   (=>
    (has_type self! Self%&)
    (has_type (vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.? Self%&. Self%&
      T&. T& E&. E& self!
     ) T&
   ))
   :pattern ((vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.? Self%&. Self%&
     T&. T& E&. E& self!
   ))
   :qid internal_vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.?_pre_post_definition
   :skolemid skolem_internal_vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.?_pre_post_definition
)))

;; Function-Axioms vstd::std_specs::result::impl&%0::is_Ok
(assert
 (fuel_bool_default fuel%vstd!std_specs.result.impl&%0.is_Ok.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.result.impl&%0.is_Ok.)
  (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (self! Poly)) (!
    (= (vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.? $ (TYPE%core!result.Result.
       T&. T& E&. E&
      ) T&. T& E&. E& self!
     ) (B (is-core!result.Result./Ok (%Poly%core!result.Result. self!)))
    )
    :pattern ((vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.? $ (TYPE%core!result.Result.
       T&. T& E&. E&
      ) T&. T& E&. E& self!
    ))
    :qid internal_vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.?_definition
    :skolemid skolem_internal_vstd!std_specs.result.ResultAdditionalSpecFns.is_Ok.?_definition
))))

;; Function-Axioms vstd::std_specs::result::impl&%0::get_Ok_0
(assert
 (fuel_bool_default fuel%vstd!std_specs.result.impl&%0.get_Ok_0.)
)
(assert
 (=>
  (fuel_bool fuel%vstd!std_specs.result.impl&%0.get_Ok_0.)
  (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (self! Poly)) (!
    (= (vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.? $ (TYPE%core!result.Result.
       T&. T& E&. E&
      ) T&. T& E&. E& self!
     ) (core!result.Result./Ok/0 (%Poly%core!result.Result. self!))
    )
    :pattern ((vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.? $ (TYPE%core!result.Result.
       T&. T& E&. E&
      ) T&. T& E&. E& self!
    ))
    :qid internal_vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.?_definition
    :skolemid skolem_internal_vstd!std_specs.result.ResultAdditionalSpecFns.get_Ok_0.?_definition
))))

;; Function-Specs core::result::impl&%0::unwrap
(declare-fun req%core!result.impl&%0.unwrap. (Dcr Type Dcr Type core!result.Result.)
 Bool
)
(declare-const %%global_location_label%%0 Bool)
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (result! core!result.Result.)) (!
   (= (req%core!result.impl&%0.unwrap. T&. T& E&. E& result!) (=>
     %%global_location_label%%0
     (is-core!result.Result./Ok result!)
   ))
   :pattern ((req%core!result.impl&%0.unwrap. T&. T& E&. E& result!))
   :qid internal_req__core!result.impl&__0.unwrap._definition
   :skolemid skolem_internal_req__core!result.impl&__0.unwrap._definition
)))
(declare-fun ens%core!result.impl&%0.unwrap. (Dcr Type Dcr Type core!result.Result.
  Poly
 ) Bool
)
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type) (result! core!result.Result.) (t! Poly))
  (!
   (= (ens%core!result.impl&%0.unwrap. T&. T& E&. E& result! t!) (and
     (has_type t! T&)
     (= t! (core!result.Result./Ok/0 (%Poly%core!result.Result. (Poly%core!result.Result.
         result!
   ))))))
   :pattern ((ens%core!result.impl&%0.unwrap. T&. T& E&. E& result! t!))
   :qid internal_ens__core!result.impl&__0.unwrap._definition
   :skolemid skolem_internal_ens__core!result.impl&__0.unwrap._definition
)))

;; Function-Axioms lib_verus::State::arrow_verification_id
(assert
 (fuel_bool_default fuel%lib_verus!impl&%2.arrow_verification_id.)
)
(assert
 (=>
  (fuel_bool fuel%lib_verus!impl&%2.arrow_verification_id.)
  (forall ((self! Poly)) (!
    (= (lib_verus!impl&%2.arrow_verification_id.? self!) (lib_verus!State./WaitToApply/verification_id
      (%Poly%lib_verus!State. self!)
    ))
    :pattern ((lib_verus!impl&%2.arrow_verification_id.? self!))
    :qid internal_lib_verus!impl&__2.arrow_verification_id.?_definition
    :skolemid skolem_internal_lib_verus!impl&__2.arrow_verification_id.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib_verus!State.)
    (uInv SZ (lib_verus!impl&%2.arrow_verification_id.? self!))
   )
   :pattern ((lib_verus!impl&%2.arrow_verification_id.? self!))
   :qid internal_lib_verus!impl&__2.arrow_verification_id.?_pre_post_definition
   :skolemid skolem_internal_lib_verus!impl&__2.arrow_verification_id.?_pre_post_definition
)))

;; Function-Axioms lib_verus::State::arrow_WaitToApply_verification_id
(assert
 (fuel_bool_default fuel%lib_verus!impl&%2.arrow_WaitToApply_verification_id.)
)
(assert
 (=>
  (fuel_bool fuel%lib_verus!impl&%2.arrow_WaitToApply_verification_id.)
  (forall ((self! Poly)) (!
    (= (lib_verus!impl&%2.arrow_WaitToApply_verification_id.? self!) (lib_verus!State./WaitToApply/verification_id
      (%Poly%lib_verus!State. self!)
    ))
    :pattern ((lib_verus!impl&%2.arrow_WaitToApply_verification_id.? self!))
    :qid internal_lib_verus!impl&__2.arrow_WaitToApply_verification_id.?_definition
    :skolemid skolem_internal_lib_verus!impl&__2.arrow_WaitToApply_verification_id.?_definition
))))
(assert
 (forall ((self! Poly)) (!
   (=>
    (has_type self! TYPE%lib_verus!State.)
    (uInv SZ (lib_verus!impl&%2.arrow_WaitToApply_verification_id.? self!))
   )
   :pattern ((lib_verus!impl&%2.arrow_WaitToApply_verification_id.? self!))
   :qid internal_lib_verus!impl&__2.arrow_WaitToApply_verification_id.?_pre_post_definition
   :skolemid skolem_internal_lib_verus!impl&__2.arrow_WaitToApply_verification_id.?_pre_post_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type)) (!
   (tr_bound%vstd!std_specs.result.ResultAdditionalSpecFns. $ (TYPE%core!result.Result.
     T&. T& E&. E&
    ) T&. T& E&. E&
   )
   :pattern ((tr_bound%vstd!std_specs.result.ResultAdditionalSpecFns. $ (TYPE%core!result.Result.
      T&. T& E&. E&
     ) T&. T& E&. E&
   ))
   :qid internal_vstd__std_specs__result__impl&__0_trait_impl_definition
   :skolemid skolem_internal_vstd__std_specs__result__impl&__0_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type) (E&. Dcr) (E& Type)) (!
   (=>
    (and
     (tr_bound%core!fmt.Debug. T&. T&)
     (tr_bound%core!fmt.Debug. E&. E&)
    )
    (tr_bound%core!fmt.Debug. $ (TYPE%core!result.Result. T&. T& E&. E&))
   )
   :pattern ((tr_bound%core!fmt.Debug. $ (TYPE%core!result.Result. T&. T& E&. E&)))
   :qid internal_core__result__impl&__35_trait_impl_definition
   :skolemid skolem_internal_core__result__impl&__35_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ (UINT SZ))
)

;; Trait-Impl-Axiom
(assert
 (forall ((T&. Dcr) (T& Type)) (!
   (=>
    (tr_bound%core!fmt.Debug. T&. T&)
    (tr_bound%core!fmt.Debug. (REF T&.) T&)
   )
   :pattern ((tr_bound%core!fmt.Debug. (REF T&.) T&))
   :qid internal_core__fmt__impl&__53_trait_impl_definition
   :skolemid skolem_internal_core__fmt__impl&__53_trait_impl_definition
)))

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ BOOL)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%tuple%0.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%lib_verus!Error.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%lib_verus!State.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%lib_verus!ProtocolLibrary.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%lib_verus!UnverifiedMessage.)
)

;; Trait-Impl-Axiom
(assert
 (tr_bound%core!fmt.Debug. $ TYPE%lib_verus!VerifiedMessage.)
)

;; Function-Specs lib_verus::ProtocolLibrary::default
(declare-fun ens%lib_verus!impl&%4.default. (Int lib_verus!ProtocolLibrary.) Bool)

;c This enforces that has_type will return TYPE%...ProtocolLibrary
(assert
  (forall ((no%param Int) (%return! lib_verus!ProtocolLibrary.))
  (! (= 
      (ens%lib_verus!impl&%4.default. no%param %return!)
      (has_type
        (Poly%lib_verus!ProtocolLibrary. return!)
        TYPE%lib_verus!ProtocolLibrary.))

   :pattern ((ens%lib_verus!impl&%4.default. no%param %return!))
   :qid internal_ens__lib_verus!impl&__4.default._definition
   :skolemid skolem_internal_ens__lib_verus!impl&__4.default._definition
)))

;; include smtqueries/Function-Def_ProtocolLibrary_default.smt2
;; include smtqueries/Function-Def_UnverifiedMessage_authenticate.smt2

;; include smtqueries/Function-Recommends_UnverifiedMessage_authenticate.smt2

;; Function-Specs lib_verus::ProtocolLibrary::validate
(declare-fun ens%lib_verus!impl&%8.validate. (lib_verus!ProtocolLibrary. lib_verus!ProtocolLibrary.
  lib_verus!UnverifiedMessage. core!result.Result.
 ) Bool
)
(assert
 (forall ((pre%self! lib_verus!ProtocolLibrary.) (self! lib_verus!ProtocolLibrary.)
   (msg! lib_verus!UnverifiedMessage.) (%return! core!result.Result.)
  ) (!
   (= (ens%lib_verus!impl&%8.validate. pre%self! self! msg! %return!) (and
     (has_type (Poly%core!result.Result. %return!) (TYPE%core!result.Result. $ TYPE%lib_verus!VerifiedMessage.
       $ TYPE%lib_verus!Error.
     ))
     (has_type (Poly%lib_verus!ProtocolLibrary. self!) TYPE%lib_verus!ProtocolLibrary.)
   ))
   :pattern ((ens%lib_verus!impl&%8.validate. pre%self! self! msg! %return!))
   :qid internal_ens__lib_verus!impl&__8.validate._definition
   :skolemid skolem_internal_ens__lib_verus!impl&__8.validate._definition
)))

;; include smtqueries/Function-Def_ProtocolLibrary_validate.smt2
;; include smtqueries/Function-Recommends_ProtocolLibrary_validate.smt2


;; Function-Specs lib_verus::ProtocolLibrary::apply
(declare-fun ens%lib_verus!impl&%8.apply. (lib_verus!ProtocolLibrary. lib_verus!ProtocolLibrary.
  lib_verus!VerifiedMessage. core!result.Result.
 ) Bool
)
(assert
 (forall ((pre%self! lib_verus!ProtocolLibrary.) (self! lib_verus!ProtocolLibrary.)
   (msg! lib_verus!VerifiedMessage.) (%return! core!result.Result.)
  ) (!
   (= (ens%lib_verus!impl&%8.apply. pre%self! self! msg! %return!) (and
     (has_type (Poly%core!result.Result. %return!) (TYPE%core!result.Result. $ TYPE%tuple%0.
       $ TYPE%lib_verus!Error.
     ))
     (has_type (Poly%lib_verus!ProtocolLibrary. self!) TYPE%lib_verus!ProtocolLibrary.)
   ))
   :pattern ((ens%lib_verus!impl&%8.apply. pre%self! self! msg! %return!))
   :qid internal_ens__lib_verus!impl&__8.apply._definition
   :skolemid skolem_internal_ens__lib_verus!impl&__8.apply._definition
)))


;; include smtqueries/Function-Def_ProtocolLibrary_apply.smt2

;; Function-Specs lib_verus::ProtocolLibrary::abort
(declare-fun ens%lib_verus!impl&%8.abort. (lib_verus!ProtocolLibrary. lib_verus!ProtocolLibrary.
  core!result.Result.
 ) Bool
)
(assert
 (forall ((pre%self! lib_verus!ProtocolLibrary.) (self! lib_verus!ProtocolLibrary.)
   (%return! core!result.Result.)
  ) (!
   (= (ens%lib_verus!impl&%8.abort. pre%self! self! %return!) (and
     (has_type (Poly%core!result.Result. %return!) (TYPE%core!result.Result. $ TYPE%tuple%0.
       $ TYPE%lib_verus!Error.
     ))
     (has_type (Poly%lib_verus!ProtocolLibrary. self!) TYPE%lib_verus!ProtocolLibrary.)
   ))
   :pattern ((ens%lib_verus!impl&%8.abort. pre%self! self! %return!))
   :qid internal_ens__lib_verus!impl&__8.abort._definition
   :skolemid skolem_internal_ens__lib_verus!impl&__8.abort._definition
)))

;; include smtqueries/Function-Def_ProtocolLibrary_abort.smt2
;; include smtqueries/Function-Def_send.smt2
;; include smtqueries/Function-Def_main.smt2
;; include smtqueries/Function-Recommends_main.smt2
