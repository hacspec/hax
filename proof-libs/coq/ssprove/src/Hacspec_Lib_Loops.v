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

From Hacspec Require Import Hacspec_Lib_Integers.

(*** Loops *)

Section Loops.

  Program Fixpoint foldi_
           {acc : choice_type}
           (fuel : nat)
           (i : both uint_size)
           (f: both uint_size -> both acc -> both (acc))
           (cur : both acc)
           {struct fuel} : both (acc) :=
    match fuel with
    | 0 => lift_both cur
    | S n' => foldi_ n' (int_add i (ret_both one)) f (f i cur)
    end.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  Equations foldi_both_
           {acc : choice_type}
           (fuel : nat)
           (i : both uint_size)
           (f: both (uint_size) -> both acc -> both (acc))
           (cur : both acc) : both (acc) :=
    foldi_both_ fuel i f cur :=
      match fuel with
      | 0 => lift_both cur
      | S n' => solve_lift foldi_both_ n' (int_add i (ret_both one)) (fun x y => solve_lift f (solve_lift x) y) (f i (solve_lift cur))
      end.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  Equations foldi
             {acc: choice_type}
             (lo: both uint_size)
             (hi: both uint_size) (* {lo <= hi} *)
           (f: both (uint_size) -> both acc -> both (acc)) (* {i < hi} *)
             (init: both acc) : both (acc) :=
    foldi lo hi f init :=
      bind_both lo (fun lo =>
      bind_both hi (fun hi =>
      match Z.sub (unsigned hi) (unsigned lo) with
      | Z0 => lift_both init
      | Zneg p => lift_both init
      | Zpos p => foldi_both_ (Pos.to_nat p) (solve_lift (ret_both lo)) (@f) init
      end))
  .
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  (* Fold done using natural numbers for bounds *)
  Fixpoint foldi_nat_
           {acc : choice_type}
           (fuel : nat)
           (i : nat)
           (f : nat -> chElement acc -> raw_code (acc))
           (cur : acc) : raw_code (acc) :=
    match fuel with
    | O => ret (cur)
    | S n' =>
        cur' ← f i cur ;;
        foldi_nat_ n' (S i) f (cur')
    end.
  Definition foldi_nat
             {acc: choice_type}
             (lo: nat)
             (hi: nat) (* {lo <= hi} *)
             (f: nat -> acc -> raw_code (acc)) (* {i < hi} *)
             (init: acc) : raw_code (acc) :=
    match Nat.sub hi lo with
    | O => ret (init)
    | S n' => foldi_nat_ (S n') lo f init
    end.

  Lemma foldi__nat_move_S :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      (cur' ← f i cur ;; foldi_nat_ fuel (S i) f (cur')) = foldi_nat_ (S fuel) i f cur.
  Proof. reflexivity. Qed.

  Lemma foldi__nat_move_S_append :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      (cur' ← foldi_nat_ fuel i f (cur) ;; f (i + fuel) (cur')) = foldi_nat_ (S fuel) i f cur.
  Proof.

    induction fuel ; intros.
    - rewrite <- foldi__nat_move_S.
      unfold foldi_nat_.
      replace (fun cur' => @ret acc ((cur'))) with (fun cur' => @ret acc cur').
      2: {
        apply functional_extensionality.
        reflexivity.
      }
      rewrite bind_ret.
      unfold bind at 1.
      rewrite Nat.add_0_r.
      reflexivity.
    - rewrite <- foldi__nat_move_S.
      rewrite <- foldi__nat_move_S.
      rewrite bind_assoc.
      f_equal.
      apply functional_extensionality.
      intros.
      replace (i + S fuel) with (S i + fuel) by lia.
      rewrite IHfuel.
      reflexivity.
  Qed.

  Lemma foldi__nat_move_to_function :
    forall {acc: choice_type}
      (fuel : nat)
      (i : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      foldi_nat_ fuel i (fun x => f (S x)) (cur) = foldi_nat_ fuel (S i) f cur.
  Proof.
    induction fuel ; intros.
    - reflexivity.
    - cbn.
      f_equal.
      apply functional_extensionality.
      intros.
      rewrite IHfuel.
      reflexivity.
  Qed.

  Lemma foldi__nat_move_to_function_add :
    forall {acc: choice_type}
      (fuel : nat)
      (i j : nat)
      (f : nat -> acc -> raw_code (acc))
      (cur : acc),
      foldi_nat_ fuel i (fun x => f (x + j)) (cur) = foldi_nat_ fuel (i + j) f cur.
  Proof.
    intros acc fuel i j. generalize dependent i.
    induction j ; intros.
    - rewrite Nat.add_0_r.
      replace (fun x : nat => f (x + 0)) with f.
      reflexivity.
      apply functional_extensionality.
      intros.
      now rewrite Nat.add_0_r.
    - replace (i + S j) with (S i + j) by lia.
      rewrite <- IHj.
      rewrite <- foldi__nat_move_to_function.
      f_equal.
      apply functional_extensionality.
      intros.
      f_equal.
      lia.
  Qed.

  Lemma bind_raw_both_ret :
    forall {A B : choice_type} (x : A) (f : A -> both B), bind_raw_both (both_ret x) f = f x.
  Proof.
    intros.
    unfold bind_raw_both.
    simpl.
    destruct (f x).
    destruct both_prog.
    simpl.
    reflexivity.
  Qed.

  Lemma bind_raw_both_assoc :
    forall {A B C : choice_type} (v : raw_both A) (k1 : A -> raw_both B) (k2 : B -> raw_both C),
  (bind_raw_both (bind_raw_both v k1) k2 = (bind_raw_both v (fun x => bind_raw_both (k1 x) k2))).
  Proof.
    intros.
    unfold bind_raw_both.
    simpl.
    rewrite bind_assoc.
    reflexivity.
  Qed.

  Lemma valid_remove_back :
    forall x (xs : {fset Location}) I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (xs ++ [x])) I ct c.
  Proof.
    intros.
    apply (valid_injectLocations) with (L1 := fset xs).
    - rewrite fset_cat.
      apply fsubsetUl.
    - apply H.
  Qed.

  Lemma list_constructor : forall {A : Type} (x : A) (xs : list A) (l : list A) (H : (x :: xs) = l), (l <> []).
  Proof.
    intros.
    subst.
    easy.
  Qed.

  Definition pop_back {A : Type} (l : list A) :=
    match (rev l) with
    | [] => []
    | (x :: xs) => rev xs ++ [x]
    end.

  Theorem pop_back_ignore_front : forall {A} (a : A) (l : list A), pop_back (a :: l) = a :: pop_back l.
  Proof.
    intros.
    induction l ; intros.
    - reflexivity.
    - unfold pop_back.
      destruct (rev (a :: a0 :: l)) eqn:orev.
      { apply f_equal with (f := @rev A) in orev.
        rewrite (rev_involutive) in orev.
        discriminate orev.
      }
      cbn in orev.

      destruct (rev (a0 :: l)) eqn:orev2.
      { apply f_equal with (f := @rev A) in orev2.
        rewrite (rev_involutive) in orev2.
        discriminate orev2.
      }
      cbn in orev2.
      rewrite orev2 in orev ; clear orev2.

      inversion_clear orev.
      rewrite rev_unit.
      reflexivity.
  Qed.

  Theorem pop_back_is_id : forall {A} (l : list A), l = pop_back l.
  Proof.
    intros.
    induction l.
    - reflexivity.
    - destruct l.
      + reflexivity.
      + rewrite pop_back_ignore_front.
        rewrite <- IHl.
        reflexivity.
  Qed.

  Ltac valid_remove_back' :=
    match goal with
    | _ : _ |- (ValidCode (fset (?l)) _ _) =>
        rewrite (@pop_back_is_id _ l)
    end ;
    apply valid_remove_back.


  Lemma valid_remove_front :
    forall x xs I {ct} c,
      ValidCode (fset xs) I c ->
      @ValidCode (fset (x :: xs)) I ct c.
  Proof.
    intros.
    apply (@valid_injectLocations) with (L1 := fset xs).
    - replace (x :: xs) with (seq.cat [x] xs) by reflexivity.
      rewrite fset_cat.
      apply fsubsetUr.
    - apply H.
  Qed.

Theorem for_loop_unfold :
  forall c n,
  for_loop (fun m : nat => c m) (S n) =
    (c 0 ;; for_loop (fun m : nat => c (S m)) (n) ).
  cbn.
  induction n ; intros.
  - reflexivity.
  - unfold for_loop ; fold for_loop.
    cbn.
    rewrite IHn.
    rewrite bind_assoc.
    reflexivity.
Qed.

End Loops.


(*** For loop again *)

(* SSProve for loop is inclusive upperbound, while hacspec is exclusive upperbound *)
Definition for_loop_range
  (lo: nat)
  (hi: nat)
  (f : nat -> raw_code 'unit) : raw_code 'unit :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end.

Fixpoint list_types_ (l : list choice_type) (init : choice_type) : choice_type  :=
  match l with
  | (t :: ts) => list_types_ ts t × init
  | [] => init
  end.

Definition list_types (l : list choice_type) : choice_type :=
  match l with
  | [] => 'unit
  | (t :: ts) => list_types_ ts t
  end.

Program Fixpoint vars_to_tuple (vars : list (∑ (t : choice_type), t)) {measure (length vars)} : list_types (seq.map (fun '(x ; y) => x) vars) :=
  match vars with
  | [] => tt
  | [x] => _
  | (x :: s :: xs) => (vars_to_tuple (s :: xs) , _)
  end.

Fixpoint for_loop_return_ (ℓ : list Location) (vars : list (∑ (t : choice_type), t)) : raw_code (list_types (seq.cat (seq.map (fun '(x ; y) => x) vars) (seq.map (fun '(x ; y) => x) ℓ) )).

  destruct ℓ as [ | l ls ].
  - rewrite seq.cats0.
    pose (ret (vars_to_tuple vars)).
    replace (fun pat : ∑ t : choice_type, t => _) with
      (fun pat : @sigT choice_type
       (fun t : choice_type => t) =>
         match pat return choice_type with
         | @existT _ _ x _ => x
         end)
      in r by (apply functional_extensionality ; now intros []).
    apply r.
  - apply (getr (l)).
    intros x.
    destruct l.
    cbn in x.
    pose (for_loop_return_ ls (vars ++ [(x0 ; x)])).
    rewrite seq.map_cat in r.
    cbn in r.
    rewrite <- seq.catA in r.
    cbn in r.
    apply r.
Defined.

Definition for_loop_return (ℓ : list Location) : raw_code (list_types (seq.map (fun '(x ; y) => x) ℓ)) := for_loop_return_ ℓ [].

Definition for_loop_locations
           (lo: nat)
           (hi: nat)
           (ℓ : list Location)
           (f : nat -> raw_code 'unit) :=
  match hi - lo with
  | O => @ret 'unit tt
  | S i => for_loop (fun n => f (n + lo)) i
  end  ;; for_loop_return ℓ.

Theorem empty_put {B} ℓ v (k h : raw_code B) :
  ⊢ ⦃ true_precond ⦄ k ≈ h ⦃ pre_to_post true_precond ⦄ ->
  ⊢ ⦃ true_precond ⦄ #put ℓ := v ;; k ≈ h ⦃ pre_to_post true_precond ⦄.
Proof.
  intros.
  apply better_r_put_lhs.
  eapply rpre_weaken_rule.
  apply H.
  intros.
  reflexivity.
Qed.

Theorem length_merge_sort_pop : forall {A} leb (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_pop leb l2 l1) = length (seq.cat (seq.flatten l1) l2).
Proof.
  intros.
  generalize dependent l2.
  induction l1 ; intros.
  - cbn.
    reflexivity.
  - cbn.
    rewrite IHl1.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite path.size_merge.
    rewrite seq.size_cat.
    rewrite ssrnat.addnA.
    f_equal.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.

Theorem length_sort_even : forall {A} leb a x (l1 : list (list A)) (l2 : list A),
    length (path.merge_sort_rec leb l1 (a :: x :: l2)) =
    length (path.merge_sort_rec leb
        (path.merge_sort_push leb (if leb a x then [a; x] else [x; a]) l1) l2).
Proof.
  reflexivity.
Qed.

Theorem length_sort_is_length' : forall {A} leb (l1 : list (list A)),
    length (path.merge_sort_rec leb l1 []) = length (seq.flatten l1).
Proof.
  destruct l1.
  + cbn.
    reflexivity.
  + cbn.
    rewrite length_merge_sort_pop.
    rewrite seq.size_cat.
    rewrite seq.size_cat.
    rewrite path.size_merge.
    rewrite seq.cats0.
    rewrite ssrnat.addnC.
    reflexivity.
Qed.
