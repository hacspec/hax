(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import String.


From Core Require Import Core_Coerce (t_Abstraction).
Export Core_Coerce (t_Abstraction).

From Core Require Import Core_Coerce (t_Concretization).
Export Core_Coerce (t_Concretization).


From Core Require Import Core_Base_Int_Number_conversion.
Export Core_Base_Int_Number_conversion.

From Core Require Import Core_Base_Seq.
Export Core_Base_Seq.

From Core Require Import Core_Int.
Export Core_Int.


From Core Require Import Core_Cmp.
Export Core_Cmp.

From Core Require Import Core_Clone.
Export Core_Clone.


From Core Require Import Core_Primitive.
Export Core_Primitive.

Instance t_Clone_427868774 `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} : t_Clone (t_Array (v_T) (v_N)) :=
  {
    t_Clone_f_clone := fun (self : t_Array (v_T) (v_N)) =>
      Build_t_Array (t_Clone_f_clone (t_Array_f_v self));
  }.

Instance t_PartialEq_670168337 `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} `{t_PartialEq v_T v_T} : t_PartialEq (t_Array (v_T) (v_N)) (t_Array (v_T) (v_N)) :=
  {
    t_PartialEq_f_eq := fun (self : t_Array (v_T) (v_N)) (other : t_Array (v_T) (v_N)) =>
      t_PartialEq_f_eq (t_Clone_f_clone (t_Array_f_v self)) (t_Array_f_v other);
    t_PartialEq_f_ne := fun (self : t_Array (v_T) (v_N)) (other : t_Array (v_T) (v_N)) =>
      negb (t_PartialEq_f_eq (t_Clone_f_clone (t_Array_f_v self)) (t_Array_f_v other));
  }.

Definition impl_2__reverse `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} (self : t_Array (v_T) (v_N)) : t_Array (v_T) (v_N) :=
  Build_t_Array (impl_2__rev (t_Array_f_v self)).

Lemma lt_usize_implies_hax_int (x : t_usize) (y : t_usize) :
  t_PartialOrd_f_lt (x) (y) = true ->
  t_PartialOrd_f_lt (t_From_f_from (x)) (t_From_f_from (y)) = true.
Proof. Admitted.

Lemma lift_usize_equality (x : t_HaxInt) (y : t_usize) :
  t_PartialEq_f_eq (x) (t_From_f_from  y) = true ->
  t_PartialEq_f_eq (t_From_f_from (x)) (y) = true.
Proof. Admitted.

Program Definition impl_2__index `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} (self : t_Array (v_T) (v_N)) (i : t_usize) `{andb (t_PartialEq_f_eq (impl_2__len (t_Array_f_v self)) (t_From_f_from (v_N))) (t_PartialOrd_f_lt (i) (v_N)) = true} : v_T :=
    impl_2__get_index (H1 := _) (t_Array_f_v self) (t_From_f_from (i)).
Admit Obligations.

Definition impl_2__new `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} (x : v_T) : t_Array (v_T) (v_N) :=
  Build_t_Array (impl_2__repeat (t_From_f_from (v_N)) (x)).

Program Definition impl_2__set_index `{v_T : Type} `{v_N : t_usize} `{t_Sized v_T} `{t_Clone v_T} (self : t_Array (v_T) (v_N)) (i : t_usize) (t : v_T) `{andb (t_PartialEq_f_eq (impl_2__len (t_Array_f_v self)) (t_From_f_from (v_N))) (t_PartialOrd_f_lt (i) (v_N)) = true} : t_Array (v_T) (v_N) :=
  Build_t_Array (impl_2__set_index (H1 := _) (t_Array_f_v self) (t_From_f_from (i)) (t)).
Admit Obligations.
