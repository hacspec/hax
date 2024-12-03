(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* From Core Require Import Core. *)

(* TODO: Replace this dummy lib with core lib *)
Class t_Sized (T : Type) := { }.
Definition t_u8 := Z.
Definition t_u16 := Z.
Definition t_u32 := Z.
Definition t_u64 := Z.
Definition t_u128 := Z.
Definition t_usize := Z.
Definition t_i8 := Z.
Definition t_i16 := Z.
Definition t_i32 := Z.
Definition t_i64 := Z.
Definition t_i128 := Z.
Definition t_isize := Z.
Definition t_Array T (x : t_usize) := list T.
Definition t_String := string.
Definition ToString_f_to_string (x : string) := x.
Instance Sized_any : forall {t_A}, t_Sized t_A := {}.
Class t_Clone (T : Type) := { Clone_f_clone : T -> T }.
Instance Clone_any : forall {t_A}, t_Clone t_A := {Clone_f_clone := fun x => x}.
Definition t_Slice (T : Type) := list T.
Definition unsize {T : Type} : list T -> t_Slice T := id.
Definition t_PartialEq_f_eq x y := x =? y.
Definition t_Rem_f_rem (x y : Z) := x mod y.
Definition assert (b : bool) (* `{H_assert : b = true} *) : unit := tt.
Inductive globality := | t_Global.
Definition t_Vec T (_ : globality) : Type := list T.
Definition impl_1__append {T} l1 l2 : list T * list T := (app l1 l2, l2).
Definition impl_1__len {A} (l : list A) := Z.of_nat (List.length l).
Definition impl__new {A} (_ : Datatypes.unit) : list A := nil.
Definition impl__with_capacity {A} (_ : Z)  : list A := nil.
Definition impl_1__push {A} l (x : A) := cons x l.
Class t_From (A B : Type) := { From_f_from : B -> A }.
Definition impl__to_vec {T} (x : t_Slice T) : t_Vec T t_Global := x.
Class t_Into (A B : Type) := { Into_f_into : A -> B }.
Instance t_Into_from_t_From {A B : Type} `{H : t_From B A} : t_Into A B := { Into_f_into x := @From_f_from B A H x }.
Definition from_elem {A} (x : A) (l : Z) := repeat x (Z.to_nat l).
Definition t_Option := option.
Definition impl__map {A B} (x : t_Option A) (f : A -> B) : t_Option B := match x with | Some x => Some (f x) | None => None end.
Definition t_Add_f_add x y := x + y.
Class Cast A B := { cast : A -> B }.
Instance cast_t_u8_t_u32 : Cast t_u8 t_u32 := {| cast x := x |}.
(* / dummy lib *)

From Core Require Import Core (t_num).
Export Core (t_num).



From Core Require Import Core_Primitive (t_u8).
Export Core_Primitive (t_u8).

From Core Require Import Core_Primitive (t_u16).
Export Core_Primitive (t_u16).

From Core Require Import Core_Primitive (t_u32).
Export Core_Primitive (t_u32).

From Core Require Import Core_Primitive (t_u64).
Export Core_Primitive (t_u64).

From Core Require Import Core_Primitive (t_u128).
Export Core_Primitive (t_u128).

From Core Require Import Core_Primitive (t_usize).
Export Core_Primitive (t_usize).

(* NotImplementedYet *)

Class t_Step (v_Self : Type) `{t_Sized (v_Self)} `{t_Clone (v_Self)} `{t_PartialOrd (v_Self) (v_Self)} : Type :=
  {
    Step_f_steps_between : v_Self -> v_Self -> t_Option ((t_usize));
    Step_f_forward_checked : v_Self -> t_usize -> t_Option ((v_Self));
  }.
Arguments t_Step (_) {_} {_} {_}.

Class t_RangeIteratorImpl (v_Self : Type) : Type :=
  {
    RangeIteratorImpl_f_Item : Type;
    _ :: `{t_Sized (RangeIteratorImpl_f_Item)};
    RangeIteratorImpl_f_spec_next : v_Self -> (v_Self*t_Option ((RangeIteratorImpl_f_Item)));
  }.
Arguments t_RangeIteratorImpl (_).

Instance t_RangeIteratorImpl_158276838 `{v_A : Type} `{t_Sized (v_A)} `{t_Step (v_A)} : t_RangeIteratorImpl ((t_Range ((v_A)))) :=
  {
    RangeIteratorImpl_impl_f_Item := v_A;
    RangeIteratorImpl_impl_f_spec_next := fun  (self : t_Range ((v_A)))=>
      let hax_temp_output := never_to_any (panic_fmt (impl_2__new_v1 (["not yet implemented: specification needed"%string]) (impl_1__none (tt)))) in
      (self,hax_temp_output);
  }.

Instance t_Iterator_416192239 `{v_A : Type} `{t_Sized (v_A)} `{t_Step (v_A)} : t_Iterator ((t_Range ((v_A)))) :=
  {
    Iterator_impl_1_f_Item := v_A;
    Iterator_impl_1_f_next := fun  (self : t_Range ((v_A)))=>
      let hax_temp_output := never_to_any (panic_fmt (impl_2__new_v1 (["not yet implemented: specification needed"%string]) (impl_1__none (tt)))) in
      (self,hax_temp_output);
    Iterator_impl_1_f_size_hint := fun  (self : t_Range ((v_A)))=>
      if
        PartialOrd_f_lt (Range_f_start self) (Range_f_end self)
      then
        let hint := Step_f_steps_between (Range_f_start self) (Range_f_end self) in
        (0,Option_Some (0))
      else
        (0,Option_Some (0));
  }.

Instance t_Step_890486371 : t_Step ((t_u8)) :=
  {
    Step_impl_2_f_steps_between := fun  (start : t_u8) (v_end : t_u8)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        Option_Some (Into_f_into (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_2_f_forward_checked := fun  (start : t_u8) (n : t_usize)=>
      match TryFrom_f_try_from (n) with
      | Result_Ok (n) =>
        impl_6__checked_add (start) (n)
      | Result_Err (_) =>
        Option_None
      end;
  }.

Instance t_Step_800843805 : t_Step ((t_u16)) :=
  {
    Step_impl_3_f_steps_between := fun  (start : t_u16) (v_end : t_u16)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        Option_Some (Into_f_into (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_3_f_forward_checked := fun  (start : t_u16) (n : t_usize)=>
      match TryFrom_f_try_from (n) with
      | Result_Ok (n) =>
        impl_7__checked_add (start) (n)
      | Result_Err (_) =>
        Option_None
      end;
  }.

Instance t_Step_230073379 : t_Step ((t_u32)) :=
  {
    Step_impl_4_f_steps_between := fun  (start : t_u32) (v_end : t_u32)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        Option_Some (Into_f_into (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_4_f_forward_checked := fun  (start : t_u32) (n : t_usize)=>
      match TryFrom_f_try_from (n) with
      | Result_Ok (n) =>
        impl_8__checked_add (start) (n)
      | Result_Err (_) =>
        Option_None
      end;
  }.

Instance t_Step_851062726 : t_Step ((t_u64)) :=
  {
    Step_impl_5_f_steps_between := fun  (start : t_u64) (v_end : t_u64)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        Option_Some (Into_f_into (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_5_f_forward_checked := fun  (start : t_u64) (n : t_usize)=>
      match TryFrom_f_try_from (n) with
      | Result_Ok (n) =>
        impl_9__checked_add (start) (n)
      | Result_Err (_) =>
        Option_None
      end;
  }.

Instance t_Step_679763039 : t_Step ((t_u128)) :=
  {
    Step_impl_7_f_steps_between := fun  (start : t_u128) (v_end : t_u128)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        impl__ok (TryFrom_f_try_from (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_7_f_forward_checked := fun  (start : t_u128) (n : t_usize)=>
      Option_None;
  }.

Instance t_Step_999413546 : t_Step ((t_usize)) :=
  {
    Step_impl_6_f_steps_between := fun  (start : t_usize) (v_end : t_usize)=>
      if
        PartialOrd_f_le (start) (v_end)
      then
        Option_Some (Into_f_into (Sub_f_sub (Clone_f_clone (v_end)) (Clone_f_clone (start))))
      else
        Option_None;
    Step_impl_6_f_forward_checked := fun  (start : t_usize) (n : t_usize)=>
      match TryFrom_f_try_from (n) with
      | Result_Ok (n) =>
        impl_11__checked_add (start) (n)
      | Result_Err (_) =>
        Option_None
      end;
  }.