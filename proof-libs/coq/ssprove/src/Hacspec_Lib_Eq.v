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

From Hacspec Require Import Hacspec_Lib_Natmod.

(* Comparisons, boolean equality, and notation *)

Global Instance int_eqdec `{WS : wsize}: EqDec (@int WS) := {
  eqb := eqtype.eq_op ;
  eqb_leibniz := int_eqb_eq ;
}.

Global Instance int_comparable `{WS : wsize} : Comparable (@int WS) :=
    eq_dec_lt_Comparable (wlt Unsigned).

Definition uint8_equal (x y : int8) : both (fset []) ([interface]) 'bool := ret_both (eqb x y : 'bool).

Theorem nat_mod_eqb_spec : forall {p} (a b : nat_mod p),
    is_pure (nat_mod_equal a b) = true <-> a = b.
Proof.
  symmetry ; apply (ssrbool.rwP nat_mod_equal_reflect).
Qed.

Global Instance nat_mod_eqdec {p} : EqDec (nat_mod p) := {
  eqb a b := is_pure (nat_mod_equal a b);
  eqb_leibniz := nat_mod_eqb_spec;
}.

(* Global Instance nat_mod_comparable `{p : Z} : Comparable (nat_mod p) := *)
(*   eq_dec_lt_Comparable (@order.Order.lt order.Order.OrdinalOrder.ord_display (order.Order.OrdinalOrder.porderType _)). *)

Definition nat_mod_rem {n : Z} (a:nat_mod n) (b:nat_mod n) : both (fset []) ([interface]) (nat_mod n) :=
  ret_both (nat_mod_rem a b).


Infix "rem" := nat_mod_rem (at level 33) : hacspec_scope.

Global Instance bool_eqdec : EqDec bool := {
  eqb := Bool.eqb;
  eqb_leibniz := Bool.eqb_true_iff;
}.

Global Instance string_eqdec : EqDec String.string := {
  eqb := String.eqb;
  eqb_leibniz := String.eqb_eq ;
}.

Fixpoint list_eqdec {A} `{EqDec A} (l1 l2 : list A) : bool :=
  match l1, l2 with
  | x::xs, y::ys => if eqb x y then list_eqdec xs ys else false
  | [], [] => true
  | _,_ => false
  end.

Lemma list_eqdec_refl : forall {A} `{EqDec A} (l1 : list A), list_eqdec l1 l1 = true.
Proof.
  intros ; induction l1 ; cbn ; try rewrite eqb_refl ; easy.
Qed.

Lemma list_eqdec_sound : forall {A} `{EqDec A} (l1 l2 : list A), list_eqdec l1 l2 = true <-> l1 = l2.
Proof.
  intros A H l1.
  induction l1 ; induction l2 ; split ; intros ; simpl in * ; try easy ; try inversion H0.
  - (* inductive case *)
    apply Field_theory.if_true in H0; destruct H0.
    f_equal.
    (* show heads are equal *)
    + apply (proj1 (eqb_leibniz a a0) H0).
    (* show tails are equal using induction hypothesis *)
    + apply IHl1. assumption.
  - rewrite eqb_refl.
    apply list_eqdec_refl.
Qed.

Global Instance List_eqdec {A} `{EqDec A} : EqDec (list A) := {
  eqb := list_eqdec;
  eqb_leibniz := list_eqdec_sound;
}.

Lemma vector_eqb_sound : forall {A : Type} {n : nat} `{EqDec A} (v1 v2 : VectorDef.t A n), Vector.eqb _ eqb v1 v2 = true <-> v1 = v2.
Proof.
  intros.
  apply Vector.eqb_eq.
  intros.
  apply eqb_leibniz.
Qed.

Global Program Instance Vector_eqdec {A n} `{EqDec A}: EqDec (VectorDef.t A n) := {
  eqb := Vector.eqb _ eqb;
  eqb_leibniz := vector_eqb_sound;
}.

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
  eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
}.
Next Obligation.
  split ; intros ; destruct x ; destruct y.
  - (* symmetry in H1. *)
    (* apply Bool.andb_true_eq in H1. destruct H1. *)
    rewrite is_true_split_and in H1. destruct H1.
    rewrite (eqb_leibniz) in H1.
    rewrite (eqb_leibniz) in H2. now subst.
  - inversion_clear H1. now do 2 rewrite eqb_refl.
Defined.

Fixpoint array_eq_
  {a: choice_type}
  {len: nat}
  (eq: ( (a)) -> ( (a)) -> bool)
  (s1: ( (nseq_ a len)))
  (s2 : ( (nseq_ a len)))
  {struct len}
  : bool.
Proof.
  destruct len ; cbn in *.
  - exact  true.
  - destruct (getm s1 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s | ].
    + destruct (getm s2 (fintype.Ordinal (m := len) (ssrnat.ltnSn _))) as [s0 | ].
      * exact (eq s s0).
      * exact false.
    + exact false.
Defined.

Infix "array_xor" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_xor)) (at level 33) : hacspec_scope.
Infix "array_add" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_add)) (at level 33) : hacspec_scope.
Infix "array_minus" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_sub)) (at level 33) : hacspec_scope.
Infix "array_mul" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_mul)) (at level 33) : hacspec_scope.
Infix "array_div" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_div)) (at level 33) : hacspec_scope.
Infix "array_or" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_or)) (at level 33) : hacspec_scope.
Infix "array_and" := (@array_join_map (int _) _ _ _ _ _ (fun _ _ _ _ => int_and)) (at level 33) : hacspec_scope.

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.
