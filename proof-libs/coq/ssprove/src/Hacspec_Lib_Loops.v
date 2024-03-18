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

From Hacspec Require Import Hacspec_Lib_Integers.

(*** Loops *)

Section Loops.

  Program Fixpoint foldi_
           {acc : choice_type}
           (fuel : nat)
           {L L2 I I2}
           (i : both L2 I2 uint_size)
           (f: both L2 I2 uint_size -> both L I acc -> both L I (acc))
           (cur : both L I acc)
           `{fsubset_loc : is_true (fsubset L2 L)}
           `{fsubset_opsig : is_true (fsubset I2 I)}
           {struct fuel} : both L I (acc) :=
    match fuel with
    | 0 => lift_both cur
    | S n' => foldi_ n' (int_add i (ret_both one)) f (f i cur)
    end.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  (* Obligation Tactic := (intros ; (fset_equality || solve_in_fset)). *)
  Equations foldi_both_
           {acc : choice_type}
           (fuel : nat)
           {L1 L2 I1 I2}
           (i : both L2 I2 uint_size)
           {L I}
           `{is_true (fsubset L1 L)} `{is_true (fsubset I1 I)}
           `{is_true (fsubset L2 L)} `{is_true (fsubset I2 I)}
           (f: both L2 I2 (uint_size) -> both L I acc -> both L I (acc))
           (cur : both L1 I1 acc) : both L I (acc) :=
    foldi_both_ fuel i f cur :=
      match fuel with
      | 0 => lift_both cur
      | S n' => solve_lift foldi_both_ n' (int_add i (ret_both one)) (fun x y => solve_lift f (solve_lift x) y) (f i (solve_lift cur))
      end.
  Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
  Fail Next Obligation.

  Equations foldi
             {acc: choice_type}
             {L1 L2 L3 I1 I2 I3}
             (lo: both L2 I2 uint_size)
             (hi: both L3 I3 uint_size) (* {lo <= hi} *)
             {L I}
           `{is_true (fsubset L1 L)} `{is_true (fsubset I1 I)}
           `{is_true (fsubset L2 L)} `{is_true (fsubset I2 I)}
           `{is_true (fsubset L3 L)} `{is_true (fsubset I3 I)}
           (f: both (L2 :|: L3) (I2 :|: I3) (uint_size) -> both L I acc -> both L I (acc)) (* {i < hi} *)
             (init: both L1 I1 acc) : both L I (acc) :=
    foldi lo hi f init :=
      bind_both lo (fun lo =>
      bind_both hi (fun hi =>
      match Z.sub (unsigned hi) (unsigned lo) with
      | Z0 => lift_both init
      | Zneg p => lift_both init
      | Zpos p => foldi_both_ (Pos.to_nat p) (solve_lift (ret_both lo)) (@f) init (* (fsubset_loc1 := fsubset_loc1) (fsubset_opsig1 := fsubset_opsig1) *)
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

  (* Lemma foldi__move_S : *)
  (*   forall {acc: choice_type} *)
  (*     (fuel : nat) *)
  (*     (i : uint_size) *)
  (*     {L I} *)
  (*     (f : uint_size -> acc -> both L I (acc)) *)
  (*     (cur : acc), *)
  (*     (bind_both (f i cur) (fun cur' => (bind_both (both_ret (Hacspec_Lib_Pre.int_add i one)) (fun Si => foldi_both_ fuel Si f (cur')))) = foldi_both_ (S fuel) i f cur). *)
  (* Proof. reflexivity. Qed. *)

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

  (* Lemma raw_code_type_from_choice_type_id : *)
  (*   forall (acc : choice_type) (x : raw_both (acc)), *)
  (*     (bind_both x (fun cur' => *)
  (*      both_ret ((cur')))) *)
  (*     = *)
  (*       x. *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold bind_both. *)
  (*   rewrite @bind_cong with (v := is_state x) (g := @ret (acc)). *)
  (*   rewrite bind_ret. *)
  (*   destruct x. *)
  (*   reflexivity. *)
  (*   reflexivity. *)

  (*   apply functional_extensionality. *)
  (*   intros. *)
  (*   reflexivity. *)
  (* Qed. *)

  Lemma bind_raw_both_ret :
    forall {A B : choice_type} {L I} (x : A) (f : A -> both L I B), bind_raw_both (both_ret x) f = f x.
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

  (* (* You can do one iteration of the fold by burning a unit of fuel *) *)
  (* Lemma foldi__move_S_fuel : *)
  (*   forall {acc: choice_type} *)
  (*     (fuel : nat) *)
  (*     (i : uint_size) *)
  (*     {L I} *)
  (*     (f : uint_size -> acc -> both L I (acc)) *)
  (*     (cur : acc), *)
  (*     (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z -> *)
  (*     (bind_both (foldi_both_ fuel i f cur) (fun cur' => *)
  (*      bind_both (both_ret (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat fuel)) i)) (fun fuel_add_i => *)
  (*      f fuel_add_i (cur')) *)
  (*     )) = foldi_both_ (S (fuel)) i f cur. *)
  (* Proof. *)
  (*   intros acc fuel. *)
  (*   induction fuel ; intros. *)
  (*   - cbn. *)
  (*     replace (repr _ 0%Z) with (@zero U32) by (apply word_ext ; reflexivity). *)
  (*     (* unfold Hacspec_Lib_Pre.int_add. *) *)
  (*     unfold Hacspec_Lib_Pre.int_add. *)
  (*     rewrite add0w. *)
  (*     rewrite raw_code_type_from_choice_type_id. *)
  (*     setoid_rewrite (bind_both_ret cur). *)
  (*     simpl. *)
  (*     reflexivity. *)
  (*   - unfold foldi_. *)
  (*     fold (@foldi_ acc fuel). *)

  (*     simpl. *)
  (*     rewrite (bind_both_assoc). *)
  (*     f_equal. *)
  (*     apply functional_extensionality. *)
  (*     intros. *)

  (*     (* unfold Hacspec_Lib_Pre.int_add at 1 3. *) *)
  (*     (* unfold ret_both, is_state at 1 3. *) *)
  (*     unfold prog, lift_to_code. *)
  (*     (* do 2 setoid_rewrite bind_rewrite. *) *)

  (*     specialize (IHfuel (Hacspec_Lib_Pre.int_add i one) L I f (x)). *)



  (*     replace (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat (S fuel))) _) *)
  (*       with (Hacspec_Lib_Pre.int_add (repr _ (Z.of_nat fuel)) (Hacspec_Lib_Pre.int_add i one)). *)
  (*     2 : { *)
  (*       (* unfold int_add. *) *)
  (*       unfold Hacspec_Lib_Pre.int_add. *)
  (*       rewrite <- addwC. *)
  (*       rewrite <- addwA. *)
  (*       rewrite addwC. *)
  (*       f_equal. *)
  (*       apply word_ext. *)
  (*       rewrite Z.add_1_l. *)
  (*       rewrite Nat2Z.inj_succ. *)

  (*       f_equal. *)
  (*       f_equal. *)
  (*       apply Zmod_small. *)
  (*       unfold wmax_unsigned in H. *)
  (*       unfold wbase in H. *)
  (*       lia. *)
  (*     } *)

  (*     setoid_rewrite IHfuel. *)
  (*     reflexivity. *)
  (*     lia. *)
  (* Qed. *)

  (* (* You can do one iteration of the fold by burning a unit of fuel *) *)
  (* Lemma foldi__nat_move_S_fuel : *)
  (*   forall {acc: choice_type} *)
  (*     (fuel : nat) *)
  (*     (i : nat) *)
  (*     (f : nat -> acc -> raw_both (acc)) *)
  (*     (cur : acc), *)
  (*     (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z -> *)
  (*     (cur' ← foldi_nat_ fuel i f cur ;; f (fuel + i)%nat (cur')) = foldi_nat_ (S fuel) i f cur. *)
  (* Proof. *)
  (*   induction fuel ; intros. *)
  (*   - cbn. *)
  (*     rewrite raw_code_type_from_choice_type_id. *)
  (*     reflexivity. *)
  (*   - unfold foldi_nat_. *)
  (*     fold (@foldi_nat_ acc fuel). *)
  (*     rewrite bind_assoc. *)
  (*     f_equal. *)
  (*     apply functional_extensionality. *)
  (*     intros. *)
  (*     replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm). *)
  (*     rewrite IHfuel. *)
  (*     + reflexivity. *)
  (*     + lia. *)
  (* Qed. *)

  (* (* folds and natural number folds compute the same thing *) *)
  (* Lemma foldi_to_foldi_nat : *)
  (*   forall {acc: choice_type} *)
  (*     (lo: uint_size) *)
  (*     (hi: uint_size) (* {lo <= hi} *) *)
  (*     {L I} *)
  (*     (f: (uint_size) -> acc -> code L I (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*     (unsigned lo <= unsigned hi)%Z -> *)
  (*     foldi_pre lo hi f init = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr _ (Z.of_nat x))) init. *)
  (* Proof. *)
  (*   intros. *)

  (*   unfold foldi_pre. *)
  (*   unfold foldi_nat. *)

  (*   destruct (uint_size_as_nat hi) as [ hi_n [ hi_eq hi_H ] ] ; subst. *)
  (*   rewrite (@unsigned_repr_alt U32 _ hi_H) in *. *)
  (*   rewrite Nat2Z.id. *)

  (*   destruct (uint_size_as_nat lo) as [ lo_n [ lo_eq lo_H ] ] ; subst. *)
  (*   rewrite (@unsigned_repr_alt U32 _ lo_H) in *. *)
  (*   rewrite Nat2Z.id. *)

  (*   remember (hi_n - lo_n)%nat as n. *)
  (*   apply f_equal with (f := Z.of_nat) in Heqn. *)
  (*   rewrite (Nat2Z.inj_sub) in Heqn by (apply Nat2Z.inj_le ; apply H). *)
  (*   rewrite <- Heqn. *)

  (*   assert (H_bound : (Z.pred 0 < Z.of_nat n < @modulus U32)%Z) by lia. *)

  (*   clear Heqn. *)
  (*   induction n. *)
  (*   - reflexivity. *)
  (*   - pose proof (H_max_bound := modulus_range_helper _ (range_of_nat_succ _ H_bound)). *)
  (*     rewrite <- foldi__nat_move_S_fuel by apply H_max_bound. *)
  (*     cbn. *)
  (*     rewrite SuccNat2Pos.id_succ. *)
  (*     rewrite <- foldi__move_S_fuel by apply H_max_bound. *)

  (*     destruct n. *)
  (*     + cbn. *)
  (*       replace (repr _ 0%Z) with (@zero U32) by (apply word_ext ; reflexivity). *)
  (*       unfold Hacspec_Lib_Pre.int_add. *)
  (*       rewrite add0w. *)
  (*       reflexivity. *)
  (*     + assert (H_bound_pred: (Z.pred 0 < Z.pos (Pos.of_succ_nat n) < @modulus U32)%Z) by lia. *)
  (*       rewrite <- (IHn H_bound_pred) ; clear IHn. *)
  (*       f_equal. *)
  (*       * cbn in *. *)
  (*         setoid_rewrite foldi__move_S. *)
  (*         f_equal. *)
  (*         lia. *)
  (*       * apply functional_extensionality. *)
  (*         intros. *)

  (*         (* unfold int_add. *) *)

  (*         setoid_rewrite bind_rewrite. *)
  (*         replace (Hacspec_Lib_Pre.int_add _ _) with (@repr U32 (Z.of_nat (Init.Nat.add (S n) lo_n))). reflexivity. *)

  (*         apply word_ext. *)

  (*         replace (urepr _) with (@unsigned U32 (repr _ (Z.of_nat (S n)))) by reflexivity. *)
  (*         replace (urepr _) with (@unsigned U32 (repr _ (Z.of_nat lo_n))) by reflexivity. *)
  (*         do 2 rewrite unsigned_repr_alt by lia. *)
  (*         rewrite Nat2Z.inj_add. *)
  (*         reflexivity. *)
  (* Qed. *)

  (* Lemma foldi_nat_to_foldi : *)
  (*   forall {acc: choice_type} *)
  (*     (lo: nat) *)
  (*     (hi: nat) (* {lo <= hi} *) *)
  (*     {L I} *)
  (*     (f: nat -> acc -> code L I (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*     (lo <= hi) -> *)
  (*     (Z.of_nat hi < @modulus U32)%Z -> *)
  (*     (forall x, f x = f (from_uint_size (repr _ (Z.of_nat x)))) -> *)
  (*     foldi_nat lo hi f init = *)
  (*       foldi_pre (usize lo) (usize hi) (fun x => f (from_uint_size x)) init. *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite foldi_to_foldi_nat. *)
  (*   2: { *)
  (*     unfold nat_uint_sizeable. *)
  (*     unfold usize, is_pure. *)
  (*     unfold Hacspec_Lib_Pre.usize. *)

  (*     do 2 rewrite wunsigned_repr. *)
  (*     rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]). *)
  (*     rewrite Zmod_small by (split ; try easy ; lia). *)
  (*     lia. *)
  (*   } *)

  (*   unfold nat_uint_sizeable. *)
  (*   unfold usize, is_pure. *)
  (*   unfold Hacspec_Lib_Pre.usize. *)

  (*   do 2 rewrite wunsigned_repr. *)
  (*   rewrite Zmod_small by (split ; [ lia | apply Z.le_lt_trans with (m := Z.of_nat hi) ; try apply inj_le ; assumption ]). *)
  (*   rewrite Zmod_small by (split ; try easy ; lia). *)
  (*   do 2 rewrite Nat2Z.id. *)

  (*   f_equal. *)
  (*   apply functional_extensionality. intros. *)
  (*   rewrite <- H1. *)
  (*   reflexivity. *)
  (* Qed. *)

  (* (* folds can be computed by doing one iteration and incrementing the lower bound *) *)
  (* Lemma foldi_nat_split_S : *)
  (*   forall {acc: choice_type} *)
  (*     (lo: nat) *)
  (*     (hi: nat) (* {lo <= hi} *) *)
  (*     (f: nat -> acc -> raw_code (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*     (lo < hi)%nat -> *)
  (*     foldi_nat lo hi f init = (cur' ← foldi_nat lo (S lo) f init ;; foldi_nat (S lo) hi f (cur')). *)
  (* Proof. *)
  (*   unfold foldi_nat. *)
  (*   intros. *)

  (*   assert (succ_sub_diag : forall n, (S n - n = 1)%nat) by lia. *)
  (*   rewrite (succ_sub_diag lo). *)

  (*   induction hi ; [ lia | ]. *)
  (*   destruct (S hi =? S lo)%nat eqn:hi_eq_lo. *)
  (*   - apply Nat.eqb_eq in hi_eq_lo ; rewrite hi_eq_lo in *. *)
  (*     rewrite (succ_sub_diag lo). *)
  (*     rewrite Nat.sub_diag. *)

  (*     rewrite raw_code_type_from_choice_type_id. *)
  (*     reflexivity. *)
  (*   - apply Nat.eqb_neq in hi_eq_lo. *)
  (*     apply Nat.lt_gt_cases in hi_eq_lo. *)
  (*     destruct hi_eq_lo. *)
  (*     + lia. *)
  (*     + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0). *)
  (*       rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H). *)
  (*       replace ((S (hi - S lo))) with (hi - lo)%nat by lia. *)

  (*       unfold foldi_nat_. *)
  (*       fold (@foldi_nat_ acc). *)
  (*       rewrite raw_code_type_from_choice_type_id. *)
  (*       reflexivity. *)
  (* Qed. *)

  (* (* folds can be split at some valid offset from lower bound *) *)
  (* Lemma foldi_nat_split_add : *)
  (*   forall (k : nat), *)
  (*   forall {acc: choice_type} *)
  (*     (lo: nat) *)
  (*     (hi: nat) (* {lo <= hi} *) *)
  (*     (f: nat -> acc -> raw_code (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*   forall {guarantee: (lo + k <= hi)%nat}, *)
  (*     foldi_nat lo hi f init = (cur' ← foldi_nat lo (k + lo) f init ;; foldi_nat (k + lo) hi f (cur')). *)
  (* Proof. *)
  (*   induction k ; intros. *)
  (*   - cbn. *)
  (*     unfold foldi_nat. *)
  (*     rewrite Nat.sub_diag. *)
  (*     cbn. *)
  (*     reflexivity. *)
  (*   - rewrite foldi_nat_split_S by lia. *)
  (*     replace (S k + lo)%nat with (k + S lo)%nat by lia. *)
  (*     specialize (IHk acc (S lo) hi f). *)

  (*     rewrite bind_cong with (v := foldi_nat lo (S lo) (fun (x : nat) (x0 : acc) => f x x0) init) (g := fun v => (cur' ← foldi_nat (S lo) (k + S lo) (fun (x : nat) (x0 : acc) => f x x0) (v) ;; *)
  (*                                                                                                            foldi_nat (k + S lo) hi (fun (x : nat) (x0 : acc) => f x x0) *)
  (*                                                                                                                      (cur'))). *)

  (*     rewrite <- bind_assoc. *)
  (*     f_equal. *)

  (*     rewrite <- foldi_nat_split_S by lia. *)
  (*     reflexivity. *)

  (*     reflexivity. *)

  (*     apply functional_extensionality. intros. rewrite IHk by lia. reflexivity. *)
  (* Qed. *)

  (* (* folds can be split at some midpoint *) *)
  (* Lemma foldi_nat_split : *)
  (*   forall (mid : nat), (* {lo <= mid <= hi} *) *)
  (*   forall {acc: choice_type} *)
  (*     (lo: nat) *)
  (*     (hi: nat) (* {lo <= hi} *) *)
  (*     (f: nat -> acc -> raw_code (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*   forall {guarantee: (lo <= mid <= hi)%nat}, *)
  (*     foldi_nat lo hi f init = (cur' ← foldi_nat lo mid f init ;; foldi_nat mid hi f (cur')). *)
  (* Proof. *)
  (*   intros. *)
  (*   assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia). *)
  (*   destruct mid_is_low_plus_constant ; subst. *)
  (*   rewrite Nat.add_comm. *)
  (*   pose foldi_nat_split_add. *)
  (*   apply foldi_nat_split_add. *)
  (*   apply guarantee. *)
  (* Qed. *)

  (* (* folds can be split at some midpoint *) *)
  (* Lemma foldi_split : *)
  (*   forall (mid : uint_size), (* {lo <= mid <= hi} *) *)
  (*   forall {acc: choice_type} *)
  (*     (lo: uint_size) *)
  (*     (hi: uint_size) (* {lo <= hi} *) *)
  (*     {L I} *)
  (*     (f: uint_size -> acc -> code L I (acc)) (* {i < hi} *) *)
  (*     (init: acc), *)
  (*   forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z}, *)
  (*     foldi_pre lo hi f init = (cur' ← foldi_pre lo mid f init ;; foldi_pre mid hi f (cur')). *)
  (* Proof. *)
  (*   intros. *)
  (*   rewrite foldi_to_foldi_nat by lia. *)
  (*   rewrite foldi_to_foldi_nat by lia. *)

  (*   pose @foldi_to_foldi_nat. *)

  (*   rewrite bind_cong with (v := foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned mid)) *)
  (*                                          (fun x : nat => f (repr _ (Z.of_nat x))) init) (g := fun init => foldi_nat (Z.to_nat (unsigned mid)) (Z.to_nat (unsigned hi)) *)
  (*                                                                                                           (fun x : nat => f (repr _ (Z.of_nat x))) (init)). *)

  (*   apply foldi_nat_split ; lia. *)
  (*   reflexivity. *)
  (*   apply functional_extensionality. *)
  (*   intros. *)

  (*   rewrite foldi_to_foldi_nat by lia. *)
  (*   reflexivity. *)
  (* Qed. *)


  (* Lemma valid_foldi_pre : *)
  (*   forall {acc : choice_type} (lo hi : int _) {L : {fset Location}} {I : Interface} (f : int _ -> _ -> both L I (_)), *)
  (*     forall init : (_), *)
  (*       ValidBoth L I (foldi_pre (acc := acc) lo hi f init). *)
  (* Proof. *)
  (*   intros. *)
  (*   unfold foldi_pre. *)
  (*   destruct (unsigned hi - unsigned lo)%Z. *)
  (*   - apply both_ret_valid. *)
  (*   - apply valid_foldi_. *)
  (*   - apply both_ret_valid. *)
  (* Qed. *)

  (* Program Definition foldi *)
  (*            {acc: choice_type} *)
  (*            (lo: uint_size) *)
  (*            (hi: uint_size) (* {lo <= hi} *) *)
  (*            {L} *)
  (*            {I} *)
  (*            (f: (uint_size) -> acc -> both L I (acc)) *)
  (*            (init: acc) *)
  (*   : *)
  (*   both L I (acc) := *)
  (*   {| both_prog := foldi_pre lo hi f init; both_prog_valid := valid_foldi_pre lo hi f init |}. *)
  (* Next Obligation. *)
  (*   intros. *)
  (*   unfold foldi_pre. *)
  (*   destruct (unsigned _ - _)%Z. *)
  (*   - now apply r_ret. *)
  (*   - generalize dependent lo. *)
  (*     generalize dependent init. *)
  (*     induction (Pos.to_nat p) ; intros. *)
  (*     + now apply r_ret. *)
  (*     + simpl. *)
  (*       pattern_both_fresh. *)
  (*       change (H1 (is_pure H)) with (temp_x ← ret (is_pure H) ;; H1 temp_x). *)
  (*       r_bind_both (f lo init). *)
  (*       subst H H0 H1. hnf. *)
  (*       apply IHn. *)
  (*   - now apply r_ret. *)
  (* Qed. *)
  (* (* Definition foldi' *) *)
  (* (*            {acc: choice_type} *) *)
  (* (*            (lo: uint_size) *) *)
  (* (*            (hi: uint_size) (* {lo <= hi} *) *) *)
  (* (*            {L1 L2 : {fset Location}} {H_loc_incl : List.incl L1 L2} *) *)
  (* (*            {I1 I2 : Interface} {H_opsig_incl : List.incl I1 I2} *) *)
  (* (*            (f: (uint_size) -> acc -> code L1 I1 (acc)) *) *)
  (* (*            (init: acc) *) *)
  (* (*   : *) *)
  (* (*   code L2 I2 (acc) *) *)
  (* (* . *) *)

  (*   eapply lift_code_scope. *)
  (*   apply (foldi lo hi f init). *)
  (*   apply H_loc_incl. *)
  (*   apply H_opsig_incl. *)
  (* Defined. *)

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
