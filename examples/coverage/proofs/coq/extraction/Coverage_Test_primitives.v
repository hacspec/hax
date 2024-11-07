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

From Core Require Import Core.

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
Instance Clone_any : forall {t_A}, t_Clone t_A := {t_Clone_f_clone := fun x => x}.

Definition test '(_ : unit) : unit :=
  let _ : bool := false in
  let _ : bool := true in
  let _ : t_u8 := 12 in
  let _ : t_u16 := 123 in
  let _ : t_u32 := 1234 in
  let _ : t_u64 := 12345 in
  let _ : t_u128 := 123456 in
  let _ : t_usize := 32 in
  let _ : t_i8 := -12 in
  let _ : t_i16 := 123 in
  let _ : t_i32 := -1234 in
  let _ : t_i64 := 12345 in
  let _ : t_i128 := 123456 in
  let _ : t_isize := -32 in
  let _ : float := 1.2%float in
  let _ : float := (-1.23)%float in
  let _ : ascii := "c"%char in
  let _ : string := "hello world"%string in
  tt.
