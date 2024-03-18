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

Definition result_unwrap {a b} (x : result b a) : both (fset []) ([interface]) (a) :=
  ret_both (result_unwrap x).
Definition result_unwrap_safe {a b} (x : result b a) `{match x with inl _ => True | inr _ => False end} : both (fset []) ([interface]) (a) :=
  ret_both (result_unwrap_safe x (H := H)).

Module choice_typeMonad.

  Class BindCode :=
    {
      mnd :> choice_typeMonad.CEMonad ;
      (* bind_code {L : {fset Location}} {I} {A B : choice_type} (x : code L I (choice_typeMonad.M A)) (f : A -> code L I (choice_typeMonad.M B)) : code L I (choice_typeMonad.M B) ; *)
      monad_bind_both {L0 L1 : {fset Location}} {I0 I1} {A B : choice_type} (x : both L0 I0 (choice_typeMonad.M (CEMonad := mnd) A)) (f : both L0 I0 A -> both L1 I1 (choice_typeMonad.M (CEMonad := mnd) B)) `{fsubset_loc : is_true (fsubset L0 L1)} `{fsubset_opsig : is_true (fsubset I0 I1)} : both L1 I1 (choice_typeMonad.M (CEMonad := mnd) B) ;
    }.


  (* Definition both_to_code {L I A} : both L I A -> code L I A := *)
  (*   fun x => {| prog := is_state x ; prog_valid := is_valid_code (both_prog_valid x) |}. *)

  (* Program Definition monad_bind_both `{BindCode} [L : {fset Location}] {I} {A B : choice_type} (x : both L I (choice_typeMonad.M A)) (f : both L I A -> both L I (choice_typeMonad.M B)) : both L I (choice_typeMonad.M B) := *)
  (*   {| *)
  (*     both_prog := *)
  (*     {| *)
  (*       is_pure := @choice_typeMonad.bind mnd A B (is_pure x) (fun x => is_pure (f (solve_lift (ret_both x)))) ; *)
  (*       is_state := prog (bind_code (both_to_code x) (fun a => both_to_code (f (solve_lift ret_both a)))) ; *)
  (*     |} ; *)
  (*     both_prog_valid := {| *)
  (*                         is_valid_code := prog_valid _ ; *)
  (*                         is_valid_both := _ ; *)
  (*                       |}; *)
  (*   |}. *)
  (* Solve All Obligations with (intros ; (fset_equality || solve_in_fset)). *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   destruct x. *)
  (*   simpl. *)
  (*   unfold both_to_code. *)
  (*   simpl. *)

  (*   unfold choice_typeMonad.bind. *)
  (*   destruct is_valid_both. *)
  (*   epose choice_typeMonad.monad_law1. *)
  (*   epose choice_typeMonad.monad_law2. *)
  (*   epose choice_typeMonad.monad_law3. *)

  (*   simpl. *)


  (*   simpl. *)


  (*   rewrite choice_typeMonad.monad_law1. *)

  (*   rewrite bind_ret. *)

  (*   apply both_valid_ret. *)
  (*   simpl. *)
  (*   apply  *)
  (*   eapply bind_both. *)
  (*   apply x. *)
  (*   intros. *)
  (*   refine (f _). *)
  (*   epose (choice_typeMonad.bind X (fun a => f _)). *)
  (*   refine (solve_lift ret_both (choice_typeMonad.bind X (fun a' => f))). *)

  (*   intros. *)
  (*   refine (). *)

  (*   epose (bind_code (is_state x) f). *)
  (*   eapply s. *)
  (*   apply x. *)
  (*   apply f. *)
  (*   apply x. *)

  (* Class BindBoth (M : choice_type -> choice_type) `{mnd : @choice_typeMonad.CEMonad M} `{H_bind_code : @BindCode M mnd} := *)
  (*    { *)
  (*      code_eq : forall [L : {fset Location}] {I} {A B : choice_type} (x : both L I (M A)) (f : A -> both L I (M B)), ⊢ ⦃ true_precond ⦄ *)
  (*                    bind_code x (fun x0 : A => f x0) *)
  (*                    ≈ *)
  (*                    ret (y m(M) ⇠ x ;; f y) *)
  (*                    ⦃ pre_to_post_ret true_precond ((y m(M) ⇠ x ;; f y)) ⦄ ; *)
  (*      bind_both [L : {fset Location}] {I} {A B : choice_type} (x : both L I (M A)) (f : A -> both L I (M B))  := *)
  (*      {| *)
  (*        is_state := bind_code x f ; *)
  (*        is_pure := y m(M) ⇠ x ;; f y ; *)
  (*        code_eq_proof_statement := code_eq x f *)
  (*      |} *)
  (*   }. *)

  (* Theorem bind_both_proj_code : forall  `{H_bind_code : BindCode} `{@BindBoth M mnd H_bind_code} {L : {fset Location}}  {I}  {A B : choice_type} (x : both L I (M A)) (y : code L I (M A)) (f : A -> both L I (M B)) (g : A -> code L I (M B)), *)
  (*     (prog (is_state x) = prog y) -> *)
  (*     (forall v, prog (is_state (f v)) = prog (g v)) -> *)
  (*     is_state (choice_typeMonad.bind_both x f) = choice_typeMonad.bind_code  (BindCode := H_bind_code) y g. *)
  (*   intros. *)
  (*   unfold bind_both. *)
  (*   unfold is_state at 1, lift_scope, is_state at 1. *)
  (*   f_equal. *)
  (*   apply code_ext. apply H0. *)
  (*   apply Coq.Logic.FunctionalExtensionality.functional_extensionality. intros. *)
  (*   apply code_ext. apply H1. *)
  (* Qed. *)

  #[global] Program Instance result_bind_code C : BindCode :=
    {|
      mnd := (@choice_typeMonad.result_monad C) ;
      monad_bind_both _ _ _ _ _ _ x f _ _ := bind_both x (fun x => match x with
                                                        | inl s => f (solve_lift ret_both s)
                                                        | inr s => solve_lift ret_both (Err s)
                                                        end)
    |}.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  (* #[global] Program Instance result_bind_both C : BindBoth (result C). *)
  (* Next Obligation. *)
  (*   intros. *)

  (*   pattern_both_fresh. *)
  (*   subst H. *)
  (*   apply (@r_bind_trans_both) with (b := x) (C := result C B). *)
  (*   intros ; subst H0 H1 ; hnf. *)

  (*   destruct (is_pure x). *)
  (*   - exact (code_eq_proof_statement (f s)). *)
  (*   - now apply r_ret. *)
  (* Qed. *)

  #[global] Program Instance option_bind_code : BindCode :=
    {| mnd := choice_typeMonad.option_monad;
      monad_bind_both _ _ _ _ A B x f _ _ :=
      bind_both x (fun t_x =>
       match t_x with
       | Some s => f (solve_lift ret_both s)
       | None => solve_lift ret_both (@None B : option B)
       end) |}.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  (* #[global] Program Instance option_bind_both : BindBoth (option). *)
  (* Next Obligation. *)
  (*   intros. *)

  (*   pattern_both_fresh. *)
  (*   subst H. *)
  (*   apply (@r_bind_trans_both) with (b := x) (C := option B). *)
  (*   intros ; subst H0 H1 ; hnf. *)

  (*   destruct (is_pure x). *)
  (*   - exact (code_eq_proof_statement (f s)). *)
  (*   - now apply r_ret. *)
  (* Qed. *)

End choice_typeMonad.

(* Notation "'bind_exception' t' x ':=' y 'in' z" := ( *)
(*   choice_typeMonad.bind_code (BindCode := t) *)
(*                              (A := _) (B := _) (L := _) *)
(*                              (y) (fun x => z)) (at level 99). *)
(* Notation Result t := (@choice_typeMonad.result_monad t). *)

(* Definition run (x : Exception A B) : Result A B. *)

(* Definition run (x : result B A). *)
