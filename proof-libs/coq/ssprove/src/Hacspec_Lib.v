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

From Hacspec Require Import Hacspec_Lib_Integers. Export Hacspec_Lib_Integers.
From Hacspec Require Import Hacspec_Lib_Loops. Export Hacspec_Lib_Loops.
From Hacspec Require Import Hacspec_Lib_Seq. Export Hacspec_Lib_Seq.
From Hacspec Require Import Hacspec_Lib_Natmod. Export Hacspec_Lib_Natmod.
From Hacspec Require Import Hacspec_Lib_Coercions. Export Hacspec_Lib_Coercions.
From Hacspec Require Import Hacspec_Lib_Eq. Export Hacspec_Lib_Eq.
From Hacspec Require Import Hacspec_Lib_Monad. Export Hacspec_Lib_Monad.
From Hacspec Require Import Hacspec_Lib_Ltac. Export Hacspec_Lib_Ltac.
From Hacspec Require Import Hacspec_Lib_Controlflow. Export Hacspec_Lib_Controlflow.
From Hacspec Require Import Hacspec_Lib_Notation. Export Hacspec_Lib_Notation.
From Hacspec Require Import Hacspec_Lib_TODO. Export Hacspec_Lib_TODO.
From Hacspec Require Import ConCertLib. Export ConCertLib.

(*** Result *)

Definition Ok {L I} {a b : choice_type} : both L I a -> both L I (result b a) := lift1_both Ok.
Definition Err  {L I} {a b : choice_type} : both L I b -> both L I (result b a) := lift1_both Err.

(* Arguments Ok {_ _}. *)
(* Arguments Err {_ _}. *)

Infix "&&" := andb : bool_scope.
Infix "||" := orb : bool_scope.

Definition u32_word_t := nseq_ uint8 4.
Definition u128_word_t := nseq_ uint8 16.

