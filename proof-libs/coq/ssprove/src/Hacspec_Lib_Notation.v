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

(*** Notation *)

Section TodoSection3.
Definition nat_mod_from_byte_seq_be {A n} (x : seq A) : both (fset []) ([interface]) (nat_mod n) := ret_both (nat_mod_from_byte_seq_be x).

End TodoSection3.

Definition neqb {A : choice_type} `{EqDec A} {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => negb (eqb x y) : 'bool).
Definition eqb {A : choice_type} `{EqDec A}  {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => eqb x y : 'bool).

Definition ltb {A : choice_type} `{Comparable A} {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => ltb x y : 'bool).
Definition leb {A : choice_type} `{Comparable A} {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => leb x y : 'bool).
Definition gtb {A : choice_type} `{Comparable A} {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => gtb x y : 'bool).
Definition geb {A : choice_type} `{Comparable A} {L1 L2 I1 I2} : both L1 I1 A -> both L2 I2 A -> both (L1 :|: L2) (I1 :|: I2) 'bool := lift2_both (fun x y => geb x y : 'bool).

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := neqb (at level 40) : hacspec_scope.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

(* Lemma foldi_nat_both : *)
(*   forall {A : choice_type} {L : {fset Location}} {I} (lo hi : nat) *)
(*     (b : nat -> A -> both L I A) *)
(*     (v : A), *)
(*   ⊢ ⦃ true_precond ⦄ *)
(*       @foldi_nat _ lo hi b v *)
(*   ≈ *)
(*   ret_both (Hacspec_Lib_Pre.foldi_nat lo hi b v) : both L I A *)
(*   ⦃ pre_to_post_ret true_precond ((Hacspec_Lib_Pre.foldi_nat lo hi b v)) ⦄. *)
(* Proof. *)
(*   intros. *)
(*   unfold prog, is_state at 2. *)
(*   unfold foldi_nat. *)
(*   unfold Hacspec_Lib_Pre.foldi_nat. *)

(*     destruct (_ - lo). *)
(*   { apply r_ret ; intros ; subst. *)
(*     split. *)
(*     - easy. *)
(*     - easy. *)
(*   } *)

(*   generalize dependent lo. *)
(*   clear. *)
(*   generalize dependent v. *)

(*   induction n ; intros. *)
(*   - cbn. *)
(*     (* unfold repr. *) *)

(*     (* replace (fun cur' : choice.Choice.sort (chElement (A)) => *) *)
(*     (*            ret (cur')) with (@ret (chElement (A))) by (apply functional_extensionality ; intros ; now rewrite T_ct_id). *) *)
(*     rewrite bind_ret. *)
(*     apply (@code_eq_proof_statement). *)

(*   - rewrite <- foldi__nat_move_S. *)
(*     rewrite <- Hacspec_Lib_Pre.foldi__nat_move_S. *)

(*     set (b' := b lo v). *)

(*     pose @r_bind_trans_both. *)
(*     specialize r with (b := b'). *)

(*     specialize r with (g := fun temp => @ret (chElement (A)) *)
(*        ( *)
(*           (@Hacspec_Lib_Pre.foldi_nat_ ( A) (S n) (S lo) *)
(*              (fun (n0 : nat) (v0 : A) => @is_pure L I A (b n0 v0)) *)
(*              temp))). *)
(*     apply r. *)
(*     intros. *)

(*     apply IHn. *)
(* Qed. *)

(* Lemma foldi_as_both : *)
(*   forall {A : choice_type} {L I} (lo hi : both L I uint_size) *)
(*     (state : uint_size -> A -> code L I (A)) *)
(*     (pure : uint_size -> A -> A) *)
(*      v, *)
(*     (forall x y, *)
(*     ⊢ ⦃ true_precond ⦄ *)
(*         state x y ≈ lift_to_code (L := L) (I := I) (pure x y) *)
(*     ⦃ pre_to_post_ret true_precond ((pure x y)) ⦄) -> *)
(*   ⊢ ⦃ true_precond ⦄ *)
(*      @foldi _ (is_pure lo) (is_pure hi) L I state v *)
(*   ≈ *)
(*      ret_both (Hacspec_Lib_Pre.foldi lo hi pure v) : both L I A *)
(*   ⦃ pre_to_post_ret true_precond ((Hacspec_Lib_Pre.foldi (is_pure lo) (is_pure hi) pure v)) ⦄. *)
(* Proof. *)
(*   intros. *)
(*   pose (fun x y => Build_both L I A (pure x y) (state x y) (H x y)). *)
(*   unfold is_state. *)
(*   unfold prog. *)

(* (*   pose (code_eq_proof_statement (foldi_both lo hi (ret_both v) (fun x y => b x (y)))). *) *)
(* (*   cbn in r. *) *)
(* (*   cbn. *) *)

(* (*   apply (code_eq_proof_statement (foldi_both lo hi (ret_both v) (fun x y => b x (y)))). *) *)
(* (* Qed. *) *)

Notation "'matchb' x 'with' '|' a '=>' b 'end'" :=
  (bind_both x (fun y => match y with
                      | a => b end)) (at level 100, a pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d  'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d end)) (at level 100, a pattern, c pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d '|' e '=>' f  'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d
                      | e => f end)) (at level 100, a pattern, c pattern, e pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d '|' e '=>' f '|' g '=>' h 'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d
                      | e => f
                      | g => h end)) (at level 100, a pattern, c pattern, e pattern, g pattern).

Notation "'matchb' x 'with' '|' a '|' c '=>' d  'end'" :=
  (bind_both x (fun y => match y with | _ => d end)) (at level 100, a pattern, c pattern).

(* Notation "x + y" := (int_add x y) : hacspec_scope. *)

(* From RecordUpdate Require Import RecordSet. *)
