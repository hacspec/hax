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

Ltac pattern_foldi_both Hx Hf Hg :=
  match goal with
    | [ |- context [ ⊢ ⦃ _ ⦄ bind _ (foldi _ _ _ ?fb) ≈ ?os ⦃ _ ⦄ ] ] =>
        let H := fresh in
        set (H := os)
        ; set (Hx := Hacspec_Lib_Pre.foldi _ _ _ _) in H
        ; pattern Hx in H
        ; subst H
        ; set (Hf := fb)
        ; match goal with
          | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
              set (Hg := gb)
          end
  | [ |- context [ ⊢ ⦃ _ ⦄ prog (foldi _ _ _ ?fb) ≈ ?os ⦃ _ ⦄ ] ] =>
        let H := fresh in
        set (H := os)
        ; set (Hx := Hacspec_Lib_Pre.foldi _ _ _ _) in H
        ; pattern Hx in H
        ; subst H
        ; set (Hf := fb)
        ; match goal with
          | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
              set (Hg := gb)
          end
    end.

Ltac pattern_foldi_both_fresh :=
  let Hx := fresh in
  let Hf := fresh in
  let Hg := fresh in
  pattern_foldi_both Hx Hf Hg.

Theorem r_bind_trans_as_both : forall {B C : choice_type} {L I} (f : choice.Choice.sort B -> raw_code C) (g : B -> raw_code C) (state : code L I (B))
    (pure : B),
  forall (P : precond) (Q : postcond _ _),
    (⊢ ⦃ true_precond ⦄
        state ≈ lift_to_code (L := L) (I := I) (pure)
    ⦃ pre_to_post_ret true_precond (pure) ⦄) ->
    (⊢ ⦃ true_precond ⦄ f (pure)  ≈ g pure ⦃ Q ⦄) ->
    (⊢ ⦃ P ⦄ temp ← state ;; f temp ≈ g (pure) ⦃ Q ⦄).
Proof.
  intros.
  eapply r_bind_trans with (P_mid := true_precond).

  eapply rpre_weaken_rule.
  apply H.

  reflexivity.

  intros.
  apply H0.
Qed.

Ltac progress_step_code :=
  match_foldi_both
  || (match_bind_trans_both)
  || match goal with
    | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (getr ?l ?a)) ≈ _ ⦃ _ ⦄ ]] =>
        apply better_r_put_get_lhs
    end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; (putr ?l ?y ?a)) ≈ _ ⦃ _ ⦄ ]] =>
      apply (r_transL (#put l := y ;; a )) ;
      [ apply contract_put | ]
  end
  ||
  match goal with
  | [ |- context [ ⊢ ⦃ _ ⦄ (#put ?l := ?x ;; ?a) ≈ ?b ⦃ _ ⦄ ]] =>
      apply (better_r_put_lhs l x a b)
  end
  ||
  (unfold lift_to_code ; apply r_ret)
  ||
  (rewrite bind_assoc)
    with
    match_foldi_both :=
    let Hx := fresh in
    let Hf := fresh in
    let Hg := fresh in
    pattern_foldi_both Hx Hf Hg
    ; try (apply (@r_bind_trans_as_both) with (f := Hf) (g := Hg))
    ; intros ; subst Hf ; subst Hg ; subst Hx ; hnf
    (* ; [apply foldi_as_both ; [ try (cbn ; Lia.lia) | intros ; unfold lift_to_code ; unfold prog ] | step_code] *)
    with
    step_code :=
      repeat (clear_bind || progress_step_code) ; try easy
        with
        clear_bind :=
        (unfold lift_to_code ;
         match goal with
         | [ |- context [ bind ?y (fun x => ret (_)) ] ] =>
             let H := fresh in
             set (H := y)

             ; rewrite bind_ret
             ; subst H
         | [ |- context [ bind ?y (fun x => ret _) ] ] =>
             let H := fresh in
             set (H := y)

             ; rewrite bind_ret
             ; subst H
         end)
        ||
        (repeat (rewrite bind_assoc)
        ; match goal with
          | [ |- context [ bind (ret (?y)) (fun x => _) ] ] =>
              let H := fresh in
              set (H := y)

              ; rewrite bind_rewrite
              ; subst H
          | [ |- context [ bind (ret ?y) (fun x => _) ] ] =>
              let H := fresh in
              set (H := y)
              ; rewrite bind_rewrite
              ; subst H
          end).

Ltac init_both_proof b_state b_pure :=
  intros ;
  unfold lift_to_code ;
  cbv delta [b_state] ;
  cbn beta ;
  let H := fresh in
  match goal with
  | [ |- context [(prog {code ?x})] ] =>
      set (H := x)
  end ;
  unfold prog ;
  cbv delta [b_pure] ;
  subst H ;
  cbn beta.

Ltac f_equal_fun_ext :=
  repeat (apply f_equal ; try (apply Coq.Logic.FunctionalExtensionality.functional_extensionality ; intros)).

Ltac ssprove_valid_step :=
  (progress
     (
       cbv zeta
       || unfold prog
       || (match goal with | [ |- context[ @bind ?A ?B (ret ?x) ?f ]] => rewrite bind_rewrite end)
       || match goal with
         | [ |- context[match ?x with | true => _ | false => _ end] ] =>
             destruct x
         end
       || match goal with
         | [ |- context[match ?x with | tt => _ end] ] =>
             destruct x
         end
       || match goal with
         | [ |- context[match ?x with | inl _ => _ | inr _ => _ end] ] =>
             destruct x
         end
       || (match goal with | [ |- context[bind (bind ?v ?k1) ?k2] ] => rewrite bind_assoc end)
       || (apply valid_bind ; [apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid | intros])
       || (apply valid_bind ; [valid_program | intros])
       || (apply valid_bind ; [repeat ssprove_valid_step | intros])
       || (apply valid_opr ; [ (* ssprove_valid_opsig *) | intros ] )
       ||  match goal with
         | [ |- context [ putr _ _ _ ] ] => (apply valid_putr ; [ (* ssprove_valid_location *) | ])

         end

       || match goal with
         | [ |- context [ getr _ _ ] ] => (apply valid_getr ; [ (* ssprove_valid_location *) | intros])
         end
       || (match goal with
          | [ |- context [ValidCode (fset ?ys) _ (@prog _ _ _ (@foldi _ ?lo ?hi (fset ?xs) _ ?f ?v))] ] =>
              simpl (* !! TODO !! *)
              (* eapply (valid_subset_fset xs ys) ; [ | apply foldi ] *)
              (* ; loc_incl_compute *)
          end)
       || apply valid_ret
       || (hnf in * ; destruct_choice_type_prod)
  )).


Ltac ssprove_valid'_2 :=
  repeat ssprove_valid_step
  ; ssprove_valid_program
  (* ; try ssprove_valid_location *).

Ltac ssprove_valid_package :=
  (repeat apply valid_package_cons ; [ apply valid_empty_package | .. | try (rewrite <- fset0E ; setoid_rewrite @imfset0 ; rewrite in_fset0 ; reflexivity) ] ; intros ; progress unfold prog).

Ltac solve_zero :=
  match goal with
  | [ |- context [ (_ <= _)%Z ] ] =>
      cbn ;
      match goal with
      | [ |- context [ (0 <= toword ?x)%Z ] ] =>
          let H := fresh in
          let H_zero := fresh in
          let H_succ := fresh in
          set (H := x)
          ; destruct_uint_size_as_nat_named H H_zero H_succ
          ; [ reflexivity | cbn in H_succ ; cbn ; try rewrite H_succ ; Lia.lia ]
      end
  end.

Ltac solve_in_mem :=
  normalize_fset ;
  repeat (rewrite (@in_fsetU loc_ordType) ; rewrite (is_true_split_or_)) ; try rewrite <- !fset1E ; try rewrite (ssrbool.introT (fset1P _ _) eq_refl) ; repeat (reflexivity || (left ; reflexivity) || right).

Ltac solve_ssprove_obligations :=
  repeat (
      intros ; autounfold ; normalize_fset ;
      (now solve_in_mem) (* TODO: add match goal *)
      || (now fset_equality) (* TODO: add match goal *)
      || (now solve_in_fset) (* TODO: add match goal *)
      || (ssprove_valid'_2)
      || ((now (* try *) (Tactics.program_simpl; fail)))).

Ltac solve_fsubset_trans :=
  now (solve_match || (refine (fsubset_trans _ _) ; [ | eassumption ] ; solve_ssprove_obligations)).

Ltac solve_foldi_fsubset_trans :=
  normalize_fset ;
  repeat (rewrite is_true_split_and || rewrite fsubUset) ;
  repeat (try rewrite andb_true_intro ; split) ;
  repeat (solve_fsubset_trans || apply fsubsetU ; rewrite is_true_split_or ; ((left ; solve_fsubset_trans) || right)).
