Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
Global Set Warnings "-notation-overridden,-ambiguous-paths".

Require Import Lia.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Sumbool.

From mathcomp Require Import fintype.

From Crypt Require Import choice_type Package Prelude.
Import PackageNotation.
From extructures Require Import ord fset fmap.

From mathcomp Require Import ssrZ word.
From Crypt Require Import jasmin_word.

From Coq Require Import ZArith List.
Import List.ListNotations.

(*** StdLib type classes *)

Declare Scope hacspec_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

Import choice.Choice.Exports.

Create HintDb hacspec_hints.

Module Add.
  Class t_Add A B := {
      f_Output : choice_type ;
      f_add_loc : {fset Location} ;
      f_add : forall {L1 L2 I1 I2}, both L1 I1 A -> both L2 I2 B -> both (L1 :|: L2 :|: f_add_loc) (I1 :|: I2) f_Output
    }.
  Coercion f_Output : t_Add >-> choice_type.
  Hint Unfold f_Output : hacspec_hints.
  Hint Transparent f_Output : hacspec_hints.
  Infix ".+" := f_add (at level 77).
End Add.
Import Add. Export Add.

Module Sub.
  Class t_Sub A B := {
      f_Output : choice_type ;
      f_sub_loc : {fset Location} ;
      f_sub : forall {L1 L2 I1 I2}, both L1 I1 A -> both L2 I2 B -> both (L1 :|: L2 :|: f_sub_loc) (I1 :|: I2) f_Output
    }.
  Coercion f_Output : t_Sub >-> choice_type.
  Hint Unfold f_Output : hacspec_hints.
  Hint Transparent f_Output : hacspec_hints.
  Infix ".-" := f_sub (at level 77).
End Sub.
Import Sub. Export Sub.

Module Mul.
  Class t_Mul A B := {
      f_Output : choice_type ;
      f_mul_loc : {fset Location} ;
      f_mul : forall {L1 L2 I1 I2}, both L1 I1 A -> both L2 I2 B -> both (L1 :|: L2 :|: f_mul_loc) (I1 :|: I2) f_Output
    }.
  Coercion f_Output : t_Mul >-> choice_type.
  Hint Unfold f_Output : hacspec_hints.
  Hint Transparent f_Output : hacspec_hints.
  Infix ".*" := f_mul (at level 77).
End Mul.
Import Mul. Export Mul.

Module Xor.
Class t_Xor A B := {
    f_Output :> choice_type ;
    f_xor_loc : {fset Location} ;
    f_xor : forall {L1 L2 I1 I2}, both L1 I1 A -> both L2 I2 B -> both (L1 :|: L2 :|: f_xor_loc) (I1 :|: I2) f_Output
  }.
  Coercion f_Output : t_Xor >-> choice_type.
  Hint Unfold f_Output : hacspec_hints.
  Hint Transparent f_Output : hacspec_hints.
  Infix ".^" := f_xor (at level 77).
End Xor.
Import Xor. Export Xor.
