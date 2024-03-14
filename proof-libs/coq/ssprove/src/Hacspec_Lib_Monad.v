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

(*** Monad / Bind *)

Definition result_unwrap {a b} (x : result b a) : both (a) :=
  ret_both (result_unwrap x).
Definition result_unwrap_safe {a b} (x : result b a) `{match x with inl _ => True | inr _ => False end} : both (a) :=
  ret_both (result_unwrap_safe x (H := H)).

Module choice_typeMonad.

  Class BindCode :=
    {
      mnd :> choice_typeMonad.CEMonad ;
      monad_bind_both {A B : choice_type} (x : both (choice_typeMonad.M (CEMonad := mnd) A)) (f : both A -> both (choice_typeMonad.M (CEMonad := mnd) B)) : both (choice_typeMonad.M (CEMonad := mnd) B) ;
    }.

  #[global] Program Instance result_bind_code C : BindCode :=
    {|
      mnd := (@choice_typeMonad.result_monad C) ;
      monad_bind_both _ _ x f := bind_both x (fun x => match x with
                                                    | inl s => f (solve_lift ret_both s)
                                                    | inr s => solve_lift ret_both (Err s)
                                                    end)
    |}.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  #[global] Program Instance option_bind_code : BindCode :=
    {| mnd := choice_typeMonad.option_monad;
      monad_bind_both A B x f :=
      bind_both x (fun t_x =>
       match t_x with
       | Some s => f (solve_lift ret_both s)
       | None => solve_lift ret_both (@None B : option B)
       end) |}.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.
End choice_typeMonad.
