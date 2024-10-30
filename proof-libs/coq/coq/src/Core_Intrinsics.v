(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import String.

From Core Require Import Core_Primitive.
Export Core_Primitive.

From Core Require Import Core_Int.
Export Core_Int.

From Core Require Import Core_Coerce.
Export Core_Coerce.

(* NotImplementedYet *)

Definition unchecked_add_u128 (x : t_u128) (y : t_u128) : t_u128 :=
  Build_t_u128 (Build_t_U128 (impl_6__add (t_Abstraction_f_lift (t_u128_0 x)) (t_Abstraction_f_lift (t_u128_0 y)))).

Definition unchecked_add_u16 (x : t_u16) (y : t_u16) : t_u16 :=
  Build_t_u16 (Build_t_U16 (impl_6__add (t_Abstraction_f_lift (t_u16_0 x)) (t_Abstraction_f_lift (t_u16_0 y)))).

Definition unchecked_add_u32 (x : t_u32) (y : t_u32) : t_u32 :=
  Build_t_u32 (Build_t_U32 (impl_6__add (t_Abstraction_f_lift (t_u32_0 x)) (t_Abstraction_f_lift (t_u32_0 y)))).

Definition unchecked_add_u64 (x : t_u64) (y : t_u64) : t_u64 :=
  Build_t_u64 (Build_t_U64 (impl_6__add (t_Abstraction_f_lift (t_u64_0 x)) (t_Abstraction_f_lift (t_u64_0 y)))).

Definition unchecked_add_u8 (x : t_u8) (y : t_u8) : t_u8 :=
  Build_t_u8 (Build_t_U8 (impl_6__add (t_Abstraction_f_lift (t_u8_0 x)) (t_Abstraction_f_lift (t_u8_0 y)))).

Definition unchecked_add_usize (x : t_usize) (y : t_usize) : t_usize :=
  Build_t_usize (Build_t_U64 (impl_6__add (t_Abstraction_f_lift (t_usize_0 x)) (t_Abstraction_f_lift (t_usize_0 y)))).

Definition add_with_overflow_u128 (x : t_u128) (y : t_u128) : (t_u128*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_u128_0 x)) (t_Abstraction_f_lift (t_u128_0 y)) in
  let res : t_U128 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_u128 (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction := t_Abstraction_462669591) (res)) (overflow)).

Definition add_with_overflow_u16 (x : t_u16) (y : t_u16) : (t_u16*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_u16_0 x)) (t_Abstraction_f_lift (t_u16_0 y)) in
  let res : t_U16 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_u16 (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction:=t_Abstraction_134234872) (res)) (overflow)).

Definition add_with_overflow_u32 (x : t_u32) (y : t_u32) : (t_u32*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_u32_0 x)) (t_Abstraction_f_lift (t_u32_0 y)) in
  let res : t_U32 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_u32 (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction:=t_Abstraction_699270934) (res)) (overflow)).

Definition add_with_overflow_u64 (x : t_u64) (y : t_u64) : (t_u64*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_u64_0 x)) (t_Abstraction_f_lift (t_u64_0 y)) in
  let res : t_U64 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_u64 (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction:=t_Abstraction_374630185) (res)) (overflow)).

Definition add_with_overflow_u8 (x : t_u8) (y : t_u8) : (t_u8*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_u8_0 x)) (t_Abstraction_f_lift (t_u8_0 y)) in
  let res : t_U8 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_u8 (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction := t_Abstraction_566214702) (res)) (overflow)).

Definition add_with_overflow_usize (x : t_usize) (y : t_usize) : (t_usize*bool) :=
  let overflow := impl_6__add (t_Abstraction_f_lift (t_usize_0 x)) (t_Abstraction_f_lift (t_usize_0 y)) in
  let res : t_U64 := t_Concretization_f_concretize (t_Clone_f_clone (overflow)) in
  (Build_t_usize (t_Clone_f_clone (res)),t_PartialOrd_f_lt (t_Abstraction_f_lift (t_Abstraction := t_Abstraction_374630185) (res)) (overflow)).

Definition wrapping_add_u128 (a : t_u128) (b : t_u128) : t_u128 :=
  Build_t_u128 (t_Add_f_add (t_u128_0 a) (t_u128_0 b)).

Definition wrapping_add_u16 (a : t_u16) (b : t_u16) : t_u16 :=
  Build_t_u16 (t_Add_f_add (t_u16_0 a) (t_u16_0 b)).

Definition wrapping_add_u32 (a : t_u32) (b : t_u32) : t_u32 :=
  Build_t_u32 (t_Add_f_add (t_u32_0 a) (t_u32_0 b)).

Definition wrapping_add_u64 (a : t_u64) (b : t_u64) : t_u64 :=
  Build_t_u64 (t_Add_f_add (t_u64_0 a) (t_u64_0 b)).

Definition wrapping_add_u8 (a : t_u8) (b : t_u8) : t_u8 :=
  Build_t_u8 (t_Add_f_add (t_u8_0 a) (t_u8_0 b)).

Definition wrapping_add_usize (a : t_usize) (b : t_usize) : t_usize :=
  Build_t_usize (t_Add_f_add (t_usize_0 a) (t_usize_0 b)).

Definition wrapping_mul_u128 (a : t_u128) (b : t_u128) : t_u128 :=
  Build_t_u128 (t_Mul_f_mul (t_u128_0 a) (t_u128_0 b)).

Definition wrapping_mul_u16 (a : t_u16) (b : t_u16) : t_u16 :=
  Build_t_u16 (t_Mul_f_mul (t_u16_0 a) (t_u16_0 b)).

Definition wrapping_mul_u32 (a : t_u32) (b : t_u32) : t_u32 :=
  Build_t_u32 (t_Mul_f_mul (t_u32_0 a) (t_u32_0 b)).

Definition wrapping_mul_u64 (a : t_u64) (b : t_u64) : t_u64 :=
  Build_t_u64 (t_Mul_f_mul (t_u64_0 a) (t_u64_0 b)).

Definition wrapping_mul_u8 (a : t_u8) (b : t_u8) : t_u8 :=
  Build_t_u8 (t_Mul_f_mul (t_u8_0 a) (t_u8_0 b)).

Definition wrapping_mul_usize (a : t_usize) (b : t_usize) : t_usize :=
  Build_t_usize (t_Mul_f_mul (t_usize_0 a) (t_usize_0 b)).

Definition wrapping_sub_u128 (a : t_u128) (b : t_u128) : t_u128 :=
  Build_t_u128 (t_Sub_f_sub (t_u128_0 a) (t_u128_0 b)).

Definition wrapping_sub_u16 (a : t_u16) (b : t_u16) : t_u16 :=
  Build_t_u16 (t_Sub_f_sub (t_u16_0 a) (t_u16_0 b)).

Definition wrapping_sub_u32 (a : t_u32) (b : t_u32) : t_u32 :=
  Build_t_u32 (t_Sub_f_sub (t_u32_0 a) (t_u32_0 b)).

Definition wrapping_sub_u64 (a : t_u64) (b : t_u64) : t_u64 :=
  Build_t_u64 (t_Sub_f_sub (t_u64_0 a) (t_u64_0 b)).

Definition wrapping_sub_u8 (a : t_u8) (b : t_u8) : t_u8 :=
  Build_t_u8 (t_Sub_f_sub (t_u8_0 a) (t_u8_0 b)).

Definition wrapping_sub_usize (a : t_usize) (b : t_usize) : t_usize :=
  Build_t_usize (t_Sub_f_sub (t_usize_0 a) (t_usize_0 b)).
