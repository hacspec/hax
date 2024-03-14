Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
Global Set Warnings "-notation-overridden,-ambiguous-paths".

(********************************************************)
(*   Implementation of all Hacspec library functions    *)
(* for Both types.                                      *)
(********************************************************)

Declare Scope hacspec_scope.

From Hacspec Require Import ChoiceEquality. Export ChoiceEquality.
From Hacspec Require Import LocationUtility. Export LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable. Export Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre. Export Hacspec_Lib_Pre.

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
