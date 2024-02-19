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
From Jasmin Require Import word.

From Coq Require Import ZArith List.
Import List.ListNotations.

Import choice.Choice.Exports.

(********************************************************)
(*   Implementation of all Hacspec library functions    *)
(* for Both types.                                      *)
(********************************************************)

Declare Scope hacspec_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

(*** Notation *)

Section TodoSection3.
Definition nat_mod_from_byte_seq_be {A n} (x : seq A) : both (nat_mod n) := ret_both (nat_mod_from_byte_seq_be x).

End TodoSection3.

Definition neqb {A : choice_type} `{EqDec A} : both A -> both A -> both 'bool := lift2_both (fun x y => negb (eqb x y) : 'bool).
Definition eqb {A : choice_type} `{EqDec A} : both A -> both A -> both 'bool := lift2_both (fun x y => eqb x y : 'bool).

Definition ltb {A : choice_type} `{Comparable A} : both A -> both A -> both 'bool := lift2_both (fun x y => ltb x y : 'bool).
Definition leb {A : choice_type} `{Comparable A} : both A -> both A -> both 'bool := lift2_both (fun x y => leb x y : 'bool).
Definition gtb {A : choice_type} `{Comparable A} : both A -> both A -> both 'bool := lift2_both (fun x y => gtb x y : 'bool).
Definition geb {A : choice_type} `{Comparable A} : both A -> both A -> both 'bool := lift2_both (fun x y => geb x y : 'bool).

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := neqb (at level 40) : hacspec_scope.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.
