From Coq Require Import ZArith List.
From Crypt Require Import choice_type Package.
Import PackageNotation.
From Crypt Require Import pkg_interpreter.
From extructures Require Import ord fset fmap.
From Hacspec Require Import Hacspec_Lib_Comparable.

From Hacspec Require Import LocationUtility.
Require Import Coq.Logic.FunctionalExtensionality.

Import RulesStateProb.
Import RulesStateProb.RSemanticNotation.
Open Scope rsemantic_scope.

From Crypt Require Import choice_type Package Prelude.
From Crypt Require Import Axioms. (* proof_irrelevance *)
Import PackageNotation.
From extructures Require Import ord fset fmap.

Import choice.Choice.Exports.

Import List.ListNotations.

From mathcomp Require Import ssrbool.

(*** Ltac *)

Ltac normalize_fset :=
  hnf ;
  autounfold with * ;
  try rewrite !fset_cons ;
  try rewrite <- !fset0E ;
  try rewrite !fsetU0 ;
  try rewrite !fset0U ;
  try rewrite !fset1E ;
  repeat (match goal with
          | |- context [?a :|: ?b :|: ?c] =>
              replace (a :|: b :|: c) with (a :|: (b :|: c)) by apply fsetUA
          end
          || match goal with
            | |- context [?a :|: (?a :|: ?b)] =>
                rewrite (fsetUA a a b) ; rewrite (fsetUid a)
            end
          || match goal with
            | |- context [?a :|: (?b :|: (?a :|: (?b :|: ?c)))] =>
                rewrite (fsetUA a b (a :|: (b :|: c))) ;
                rewrite (fsetUA a b c) ;
                rewrite (fsetUA (a :|: b) (a :|: b) c) ;
                rewrite (fsetUid (a :|: b))
            end).

Ltac solve_match :=
  try set (fset _) ;
  (lazymatch goal with
   | |- context [ fsubset ?a (?a :|: _) ] => apply fsubsetUl
   | |- context [ fsubset ?a (_ :|: ?a) ] => apply fsubsetUr
   | |- context [ fsubset fset0 _ ] => apply fsub0set
   | |- context [ fsubset ?a ?a ] => apply fsubsetxx
   end).

Ltac split_fsubset_lhs :=
  repeat (rewrite !is_true_split_and || rewrite !fsubUset) ;
  repeat (try rewrite !andb_true_intro ; split).

Ltac solve_single_fset_fsubset :=
  repeat (solve_match || apply fsubsetU ; rewrite is_true_split_or ; (left ; solve_match) || right).

Ltac solve_is_true :=
  now normalize_fset ;
  split_fsubset_lhs ;
  solve_single_fset_fsubset.

Ltac left_assoc :=
  repeat (match goal with
          | |- context [?a :|: ?b :|: ?c] =>
              replace (a :|: b :|: c) with (a :|: (b :|: c)) by apply fsetUA
          end).

Ltac solve_in_fset :=
  match goal with
  | [ |- context [ is_true (fsubset _ _) ] ] => solve_is_true
  | [ |- context [ fsubset _ _ = true ] ] => solve_is_true
  end.

Ltac solve_fset_eq :=
  apply (ssrbool.elimT eqtype.eqP) ;
  rewrite eqEfsubset ;
  rewrite is_true_split_and ; split ;
  solve_in_fset.

Ltac fset_equality :=
  repeat
    match goal with
    | H : fsubset (?x :|: ?y) ?z = true |- _ =>
        rewrite fsubUset in H ;
        apply andb_prop in H ;
        destruct H
    end ;
  match goal with
  | [ |- context [ @eq (fset_of _) _ _ ] ] =>
      solve_fset_eq
  | [ |- context [ @eq Interface _ _ ] ] =>
      solve_fset_eq
  | [ |- context [ @Logic.eq (fset_of _) _ _ ] ] =>
      solve_fset_eq
  | [ |- context [ @Logic.eq Interface _ _ ] ] =>
      solve_fset_eq
  end.

Notation "prod_ce( a , b )" := ((a , b) : chProd _ _) : hacspec_scope.
Notation "prod_ce( a , b , .. , c )" := ((.. ((a , b) : chProd _ _) .. , c) : chProd _ _) : hacspec_scope.

Definition lift_to_code {ce L I} (x : choice.Choice.sort ce) : code L I ce :=
  {code ret x}.

Definition pre_to_post (P : precond) {A} : postcond A A :=
  fun '(a, h₀) '(b, h₁) => a = b /\ P (h₀ , h₁).
Definition pre_to_post_ret (P : precond) {A} v : postcond A A :=
  fun '(a, h₀) '(b, h₁) => (a = b /\ b = v) /\ P (h₀ , h₁).

Definition true_precond : precond := fun _ => True.

Theorem forget_precond {B} (x y : raw_code B) P Q :
  ⊢ ⦃ true_precond ⦄ x ≈ y ⦃ Q ⦄ ->
  ⊢ ⦃ P ⦄ x ≈ y ⦃ Q ⦄.
Proof.
  intros.
  now apply (rpre_weaken_rule _ _ _ H).
Qed.

Section Both.
  Context (A : choice_type).

  Class raw_both :=
    {
      is_pure : choice.Choice.sort A ;
      is_state : raw_code A ;
    }.
  Arguments is_pure raw_both.
  Arguments is_state raw_both.

  Inductive valid_both :
    forall (b : raw_both), Prop :=
  | both_valid_ret :
    forall x, valid_both {| is_pure := x ; is_state := ret x |}.
  
  Class ValidBoth (p : raw_both) :=
    { is_valid_code : ValidCode fset0 fset0 (@is_state p) ;
      is_valid_both : @valid_both p ;
    }.
  Arguments is_valid_code {_} ValidBoth.
  Arguments is_valid_both {_} ValidBoth.

  Record both : Type :=
    mk2prog {
        both_prog :> raw_both ;
        both_prog_valid : @ValidBoth both_prog ;
        p_eq : ⊢ ⦃ true_precond ⦄ (@is_state both_prog) ≈ ret (@is_pure both_prog) ⦃ pre_to_post_ret true_precond (@is_pure both_prog) ⦄ ;
      }.
  Arguments both_prog b.
  Arguments both_prog_valid b.
  Arguments p_eq b.

End Both.

Arguments is_pure {_} raw_both.
Arguments is_state {_} raw_both.

Arguments valid_both {_}.
Arguments both_valid_ret {_}.

Arguments ValidBoth {_} p.
Arguments is_valid_code {_} {_} ValidBoth.
Arguments is_valid_both {_} {_} ValidBoth.

Arguments both_prog {_} b.
Arguments both_prog_valid {_} b.
Arguments p_eq {_} b.

Section Both_helper.

  Lemma valid_both_eta :
    forall {A : choice_type} {x : raw_both A},
      valid_both x ->
      valid_both {| is_pure := is_pure x ; is_state := is_state x |}.
  Proof.
    now intros ? [] ?.
  Defined.

  Lemma ValidBoth_eta :
    forall {A : choice_type} {x : both A},
      ValidBoth x ->
      ValidBoth {| is_pure := is_pure x ; is_state := is_state x |}.
  Proof.
    now intros ? [[] ? ?] ?.
  Defined.

  Definition bind_raw_both {A B} (c : raw_both A) (k : A -> raw_both B) : raw_both B :=
    {|
      is_pure := let x := (is_pure c) in is_pure (k x) ;
      is_state := bind (is_state c) (fun x => is_state (k x))
    |}.

  Lemma valid_bind_both_ :
    forall A B c k,
      valid_both c ->
      (forall x, valid_both {| is_pure := is_pure (k x) ; is_state := is_state (k x) |}) ->
      valid_both (@bind_raw_both A B c k).
  Proof.
    intros A B c k Hc Hk.
    induction Hc ; intros.
    apply Hk.
  Qed.

  Lemma valid_bind_both :
    forall A B c k,
      ValidBoth c ->
      (forall x, ValidBoth (k x)) ->
      ValidBoth (@bind_raw_both A B c k).
  Proof.
    intros A B c k Hc Hk.
    constructor ; simpl.
    - apply valid_bind.
      apply (is_valid_code Hc).
      apply (fun x => is_valid_code (Hk x)).
    - eapply valid_bind_both_.
      apply (is_valid_both Hc).
      intros.
      apply valid_both_eta.
      apply (fun x => is_valid_both (Hk x)).
  Qed.

  Definition both_ret {A : choice_type} (x : A) : raw_both A :=
    {| is_pure := x ; is_state := ret x |} .

  Program Definition both_ret_valid {A : choice_type} (x : A) : ValidBoth (both_ret x) :=
    {| is_valid_code := valid_ret _ _ _ ; is_valid_both := both_valid_ret _ |} 
    .
  Fail Next Obligation.

End Both_helper.

Program Definition ret_both {A : choice_type} (x : A) : both A :=
  {|
    both_prog := {| is_pure := x ; is_state := ret x |} ;
    both_prog_valid := {|
                        is_valid_code := valid_ret fset0 fset0 x ;
                        is_valid_both := both_valid_ret x ;
                      |} ;
    p_eq := r_ret _ _ _ _ _ ;
  |}.
Fail Next Obligation.

Ltac pattern_both Hx Hf Hg :=
  (match goal with
   | [ |- context [ @is_state _ ?x : both _ _ _ ] ] =>
       set (Hx := x)
       ; try change (@is_pure _ _) with (@is_pure _ Hx)
       ; match goal with
         | [ |- context [ ⊢ ⦃ _ ⦄ bind _ ?fb ≈ ?os ⦃ _ ⦄ ] ] =>
             let H := fresh in
             set (H := os)
             ; pattern (@is_pure _ Hx) in H
             ; subst H
             ; set (Hf := fb)
             ; match goal with
               | [ |- context [ ⊢ ⦃ _ ⦄ _ ≈ ?gb _ ⦃ _ ⦄ ] ] =>
                   set (Hg := gb)
               end
         end
   end).

Ltac pattern_both_fresh :=
  let x := fresh in
  let y := fresh in
  let z := fresh in
  pattern_both x y z.

Theorem r_bind_trans :
  forall {B C : choice_type}
     (f : choice.Choice.sort B -> raw_code C)
    (g : choice.Choice.sort B -> raw_code C) (x : raw_code B) (y : choice.Choice.sort B),
  forall (P P_mid : precond) (Q : postcond (choice.Choice.sort C) (choice.Choice.sort C)),
  forall (H_x_is_y : ⊢ ⦃ P ⦄ x  ≈ ret y ⦃ pre_to_post_ret P_mid (y) ⦄),
    (⊢ ⦃ P_mid ⦄ f (y)  ≈ g y ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← x ;; f temp ≈ g y ⦃ Q ⦄.
Proof.
  intros.
  replace (g y) with (temp ← ret y ;; g temp) by reflexivity.

  pose @r_bind.
  specialize r with (f₀ := f) (f₁ := fun x => g x).
  specialize r with (m₀ := x) (m₁ := (ret y)).
  specialize r with (pre := P) (mid := pre_to_post_ret P_mid y ) (post := Q).
  apply r ; clear r.

  - apply H_x_is_y.
  - intros.
    eapply rpre_hypothesis_rule.
    intros ? ? [[] ?]. subst.
    eapply rpre_weaken_rule.
    cbn in H2.
    subst.
    apply H.
    intros ? ? []. subst. apply H2.
Qed.

Theorem r_bind_trans_both : forall {B C : choice_type} {f : choice.Choice.sort B -> raw_code C} {g : choice.Choice.sort B -> raw_code C} (b : both B),
  forall (P : precond) (Q : postcond _ _),
    (⊢ ⦃ true_precond ⦄ f ((is_pure b))  ≈ g (is_pure b) ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← is_state b ;; f temp ≈ g (is_pure b) ⦃ Q ⦄.
Proof.
  intros.
  apply r_bind_trans with (P_mid := true_precond).

  eapply rpre_weaken_rule.
  apply p_eq.
  reflexivity.

  apply H.
Qed.

Ltac match_bind_trans_both :=
  let Hx := fresh in
  let Hf := fresh in
  let Hg := fresh in
  pattern_both Hx Hf Hg
  ; apply (@r_bind_trans_both) with (b := Hx) (f := Hf) (g := Hg)
  ; intros ; subst Hf ; subst Hg ; subst Hx ; hnf.

Ltac r_bind_both a :=
  eapply r_bind ; [ apply (p_eq a) | ] ;
  intros ;
  apply rpre_hypothesis_rule ;
  intros ? ? [[] []] ; subst ;
  apply forget_precond.

Ltac r_subst_both a :=
  let x := fresh in
  let y := fresh in
  let z := fresh in
  pattern_both x y z ;
  change (z _) with (temp ← ret (is_pure x) ;; z temp) ;
  r_bind_both a ;
  subst x y z ; hnf.

Program Definition bind_both {A B} (c : both A) (k : A -> both B) : both B :=
  {|
    both_prog := bind_raw_both (both_prog c) (fun x => both_prog (k x)) ;
    both_prog_valid := valid_bind_both A B c k (both_prog_valid c) (fun x => both_prog_valid (k x)) ;
  |}.
Next Obligation.
  intros.
  r_subst_both c.
  apply (k (is_pure c)).
Qed.

Lemma both_eq : forall {A : choice_type} (a b : both A),
    both_prog a = both_prog b ->
    a = b.
Proof.
  intros.
  destruct a , b.
  cbn in *. subst.
  f_equal ; apply proof_irrelevance.
Qed.

Lemma bind_ret_both : forall {A B : choice_type} (f : A -> both B) (x : A),
    (bind_both (ret_both x) f) = f x.
Proof.
  intros.
  apply both_eq.
  simpl.
  unfold bind_raw_both.
  simpl.
  destruct (f x). simpl.
  destruct both_prog0. simpl.
  reflexivity.
Qed.

Definition lift_both {A} (x : both A) : both A :=
    {| both_prog := x ;
      both_prog_valid := (both_prog_valid x) ;
      p_eq := p_eq x |}.

Notation "'solve_lift' x" := (lift_both x) (at level 100).

Equations lift1_both {A B : choice_type} (f : A -> B) (x : both A) : both B
  :=
  lift1_both f x := bind_both x (fun x' => solve_lift (ret_both (f x'))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Equations lift2_both {A B C : choice_type} (f : A -> B -> C) (x : both A) (y : both B)
  : both C
  :=
  lift2_both f x y :=
    bind_both x (fun x' =>
    bind_both y (fun y' =>
    solve_lift (ret_both (f x' y')))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Equations lift3_both {A B C D : choice_type} (f : A -> B -> C -> D) (x : both A) (y : both B) (z : both C)
  : both D :=
  lift3_both f x y z :=
  bind_both x (fun x' => lift_both (lift2_both (f x') y z)).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Definition choice_type_size (ce : choice_type) : nat.
Proof.
  induction ce.
  1, 2, 3, 4, 8, 9: exact 1.
  - refine (S (IHce1 + IHce2))%nat.
  - refine (S (S (S (IHce1 + IHce2))))%nat.
  - refine (S (IHce))%nat.
  - refine (S (IHce))%nat.
  - refine (S (IHce1 + IHce2))%nat.
Defined.

Fixpoint ce_to_chElement_ordType_ce (ce : choice_type) (X : chElement_ordType ce) : ce :=
  match ce as A return chElement_ordType A -> A with
  | 'unit | 'nat | 'int | 'bool | chFin _ | 'word _ => id
  | Y × Z => fun '(y,z) => (ce_to_chElement_ordType_ce Y y, ce_to_chElement_ordType_ce Z z)
  | chMap Y Z => fun y => mkfmap (seq.zip (seq.unzip1 (FMap.fmval y)) (List.map (ce_to_chElement_ordType_ce Z) (seq.unzip2 (FMap.fmval y))))
  | 'option Y => (fun y => match y with
                 | None => None
                 | Some z => Some (ce_to_chElement_ordType_ce Y z)
                       end)
  | chList Y => List.map (ce_to_chElement_ordType_ce Y)
  | Y ∐ Z => (fun y => match y with
            | inl z => inl (ce_to_chElement_ordType_ce Y z)
            | inr z => inr (ce_to_chElement_ordType_ce Z z)
            end)
  end X.

Fixpoint chElement_ordType_ce_to_ce (ce : choice_type) (X : ce) : chElement_ordType ce :=
  match ce as A return A -> chElement_ordType A with
  | 'unit | 'nat | 'int | 'bool | chFin _ | 'word _ => id
  | Y × Z => fun '(y,z) => (chElement_ordType_ce_to_ce Y y,
                        chElement_ordType_ce_to_ce Z z)
  | chMap Y Z => fun y => mkfmap (seq.zip (seq.unzip1 (FMap.fmval y)) (List.map (chElement_ordType_ce_to_ce Z) (seq.unzip2 (FMap.fmval y))))
  | 'option Y => (fun y => match y with
                 | None => None
                 | Some z => Some (chElement_ordType_ce_to_ce Y z)
                       end)
  | chList Y => List.map (chElement_ordType_ce_to_ce Y)
  | Y ∐ Z => (fun y => match y with
            | inl z => inl (chElement_ordType_ce_to_ce Y z)
            | inr z => inr (chElement_ordType_ce_to_ce Z z)
            end)
  end X.

Equations prod_both {ceA ceB : choice_type} (a : both ceA) (b : both ceB) : both (ceA × ceB) :=
  prod_both a b :=
    bind_both a (fun a' =>
    bind_both b (fun b' =>
                   solve_lift (ret_both ((a', b') : _ × _)))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Notation "'prod_b' ( a , b )" := (prod_both a b) : hacspec_scope.
Notation "'prod_b' ( a , b , .. , c )" := (prod_both .. (prod_both a b) .. c) : hacspec_scope.

Ltac ssprove_valid_program :=
  try (apply prog_valid) ;
  try (apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid).

Ltac destruct_choice_type_prod :=
  try match goal with
  | H : choice.Choice.sort (chElement (loc_type ?p)) |- _ =>
      unfold p in H ;
      unfold loc_type in H ;
      unfold projT1 in H
  end ;
  repeat match goal with
  | H : (chProd _ _) |- _ =>
      destruct H
  end ;
  repeat match goal with
  | H : choice.Choice.sort
         (chElement
            (choice.Choice.sort
               (chProd _ _))) |- _ =>
      destruct H
  end ;
  repeat match goal with
         | H : prod _ _ |- _ => destruct H
         end ;
  cbv zeta.

Theorem tag_leq_simplify :
  forall (a b : Location),
    is_true (ssrfun.tag a <= ssrfun.tag b)%ord ->
    is_true (ssrfun.tagged a <= ssrfun.tagged b)%ord ->
    is_true (tag_leq (I:=choice_type_choice_type__canonical__Ord_Ord) (T_:=fun _ : choice_type => Datatypes_nat__canonical__Ord_Ord) a b).
Proof.
  intros [] [].

  unfold tag_leq.
  unfold eqtype.tagged_as, ssrfun.tagged , ssrfun.tag , projT1 , projT2.

  intro.
  rewrite Ord.leq_eqVlt in H.
  rewrite is_true_split_or in H.
  destruct H.
  - apply Couplings.reflection_nonsense in H ; subst.

    rewrite Ord.ltxx.
    rewrite Bool.orb_false_l.
    rewrite eqtype.eq_refl.
    rewrite Bool.andb_true_l.

    destruct eqtype.eqP.
    + unfold eq_rect_r , eq_rect ; destruct eq_sym.
      trivial.
    + contradiction.
  - rewrite H ; clear H.
    reflexivity.
Qed.

Theorem tag_leq_inverse :
  forall a b,
    tag_leq (I:=choice_type_choice_type__canonical__Ord_Ord) (T_:=fun _ : choice_type => Datatypes_nat__canonical__Ord_Ord) a b
    =
      (negb (tag_leq (I:=choice_type_choice_type__canonical__Ord_Ord) (T_:=fun _ : choice_type => Datatypes_nat__canonical__Ord_Ord)
                    b a) ||
           eqtype.eq_op (ssrfun.tag a) (ssrfun.tag b) &&
        eqtype.eq_op (ssrfun.tagged a) (ssrfun.tagged b))%bool.
Proof.
  intros [a b] [c d].
  unfold tag_leq.

  rewrite Bool.negb_orb.
  rewrite Bool.negb_andb.
  rewrite Bool.andb_orb_distrib_r.

  unfold eqtype.tagged_as.
  unfold ssrfun.tagged , ssrfun.tag , projT1 , projT2.
  rewrite <- Bool.orb_assoc.

  f_equal.
  - rewrite <- Bool.negb_orb.
    rewrite <- Bool.orb_comm.
    rewrite <- Ord.leq_eqVlt.
    rewrite <- Ord.ltNge.
    reflexivity.
  - destruct (eqtype.eq_op a c) eqn:a_eq_c.
    + apply Couplings.reflection_nonsense in a_eq_c.
      subst.
      do 2 rewrite Bool.andb_true_l.

      destruct eqtype.eqP. 2: contradiction.

      unfold eq_rect_r , eq_rect.
      destruct eq_sym.

      rewrite Ord.leq_eqVlt.
      rewrite Bool.orb_comm.

      f_equal.
      rewrite <- Ord.ltNge.
      rewrite Ord.ltxx.
      reflexivity.
    + do 2 rewrite Bool.andb_false_l.
      rewrite Bool.orb_false_r.
      symmetry.

      destruct eqtype.eqP.
      { subst. rewrite eqtype.eq_refl in a_eq_c. discriminate a_eq_c. }

      rewrite Ord.eq_leq by reflexivity.
      rewrite Bool.andb_false_r.
      reflexivity.
Qed.

Ltac valid_program :=
  apply prog_valid
  || (apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid).


Definition heap_ignore_post fset {A} : postcond A A :=
  pre_to_post (heap_ignore fset).

Theorem heap_ignore_refl :
  forall {fset} h, heap_ignore fset (h, h).
Proof.
  intros fset h ℓ ?.
  reflexivity.
Qed.

Theorem heap_ignore_post_refl :
  forall {fset A} (x : A * heap), heap_ignore_post fset x x.
Proof.
  intros fset A [].
  split. reflexivity.
  apply heap_ignore_refl.
Qed.

Lemma heap_ignore_weaken :
  forall fset fset', is_true (fsubset fset fset') ->
  forall x, heap_ignore fset x -> heap_ignore fset' x.
Proof.
  intros.
  destruct x as [h h0].
  pose (INV'_heap_ignore fset fset' fset0).
  rewrite fsetU0 in i.
  unfold INV' in i.
  specialize (i H h h0).
  destruct i as [? _].
  intros l ?.
  specialize (H1 H0 l H2 ltac:(easy)).
  rewrite H1.
  reflexivity.
Qed.

Lemma rpost_heap_ignore_weaken :
  forall {A} fset fset', is_true (fsubset fset fset') ->
  forall (x y : raw_code A),
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
      ⦃ heap_ignore_post fset ⦄ ->
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
        ⦃ heap_ignore_post fset' ⦄.
Proof.
  intros.
  eapply rpost_weaken_rule.
  apply H0.

  intros [] [] []. subst.
  split. reflexivity.
  apply (heap_ignore_weaken fset) ; assumption.
Qed.


Lemma rpre_heap_ignore_weaken :
  forall {A} fset fset', is_true (fsubset fset fset') ->
  forall (x y : raw_code A),
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset' (h0, h1)) ⦄
        x ≈ y
      ⦃ heap_ignore_post fset ⦄ ->
    ⊢ ⦃ (fun '(h0, h1) => heap_ignore fset (h0, h1)) ⦄
        x ≈ y
        ⦃ heap_ignore_post fset ⦄.
Proof.
  intros.
  eapply rpre_weaken_rule.
  apply H0.
  intros. cbn.
  apply (heap_ignore_weaken fset fset') ; assumption.
Qed.

Theorem bind_rewrite : forall A B x f, @bind A B (ret x) f = f x.
Proof.
  intros.
  unfold bind.
  reflexivity.
Qed.

Theorem r_bind_eq : forall {B C : choice_type} (y : choice.Choice.sort B) (g : choice.Choice.sort B  -> raw_code C), (temp ← ret y ;; g temp) = g y.
Proof. reflexivity. Qed.

Theorem r_bind_trans' :
  forall {B C : choice_type}
     (f : choice.Choice.sort B -> raw_code C)
    (g : choice.Choice.sort B -> raw_code C) (x : raw_code B) (y : choice.Choice.sort B),
  forall (P : precond) (Q : postcond (choice.Choice.sort C) (choice.Choice.sort C)),
  forall (H_x_is_y : ⊨ repr x ≈ repr (ret y) [{retW (y, y)}]),
    (⊢ ⦃ P ⦄ f ( y)  ≈ g y ⦃ Q ⦄) ->
    ⊢ ⦃ P ⦄ temp ← x ;; f temp ≈ g y ⦃ Q ⦄.
Proof.
  intros.

  replace (g y) with (temp ← ret y ;; g temp) by reflexivity.

  pose @r_bind.
  specialize r with (f₀ := f) (f₁ := fun x => g x).
  specialize r with (m₀ := x) (m₁ := (ret y)).
  specialize r with (pre := P) (mid := fun s0 s1 => pre_to_post P s0 s1 /\ fst s1 = y) (post := Q).
  apply r ; clear r.

  - eapply from_sem_jdg.
    eapply (RulesStateProb.weaken_rule (retW (y , y))).
    + apply H_x_is_y.
    + unfold retW.
      intros [] X [? πa1a2] ; cbn in X.
      specialize (fun x => πa1a2 (x, s) (y, s0)).

      unfold proj1_sig.

      unfold RulesStateProb.WrelSt.
      unfold θ.
      unfold StateTransformingLaxMorph.rlmm_codomain ; simpl.

      apply πa1a2.
      split.
      cbn.
      split.
      reflexivity.
      2: { reflexivity. }
      apply H0.
  - intros.
    eapply rpre_hypothesis_rule.
    intros ? ? [[] ?]. subst.
    eapply rpre_weaken_rule.
    2: { intros ? ? []. subst. apply H1. }
    clear H1.
    apply H.
Qed.

Ltac solve_post_from_pre :=
  let H := fresh in
  intros ? ? H
  ; split
  ; [reflexivity | ]
  ; ( assumption
      || (apply restore_set_lhs in H
         ; [ assumption
           | intros ? ? ] )).

Corollary better_r :
  forall {A B : choice.Choice.type}
    (r₀ : raw_code A)
    (r₁ : raw_code B) (pre : precond)
    (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
    ⊢ ⦃ fun '(s₀, s₁) => pre (s₀, s₁) ⦄ r₀ ≈ r₁ ⦃ post ⦄ <->
      ⊢ ⦃ pre ⦄ r₀ ≈ r₁ ⦃ post ⦄.
Proof.
  split ; intros ; (eapply rpre_hypothesis_rule ; intros ; eapply rpre_weaken_rule ; [ apply H | intros ? ? [] ; subst ; easy ]).
Qed.

Corollary better_r_put_lhs : forall {A B : choice.Choice.type} (ℓ : Location)
       (v : choice.Choice.sort (Value (projT1 ℓ))) (r₀ : raw_code A)
       (r₁ : raw_code B) (pre : precond)
       (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
     ⊢ ⦃ set_lhs ℓ v pre ⦄ r₀ ≈ r₁ ⦃ post ⦄ ->
     ⊢ ⦃ pre ⦄ #put ℓ := v ;; r₀ ≈ r₁ ⦃ post ⦄.
Proof.
  intros ; now apply better_r, r_put_lhs, better_r.
Qed.

Corollary better_r_put_rhs : forall {A B : choice.Choice.type} (ℓ : Location)
                               (v : choice.Choice.sort (Value (projT1 ℓ))) (r₀ : raw_code A)
                               (r₁ : raw_code B) (pre : precond)
                               (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
    ⊢ ⦃ set_rhs ℓ v pre ⦄ r₀ ≈ r₁ ⦃ post ⦄ ->
    ⊢ ⦃ pre ⦄ r₀ ≈ #put ℓ := v ;; r₁ ⦃ post ⦄.
Proof.
  intros ; now apply better_r, r_put_rhs, better_r.
Qed.

Corollary better_r_put_get_lhs : forall (A : choice.Choice.type) (B : choice.Choice.type) (ℓ : Location) (v : choice.Choice.sort ℓ) (r : choice.Choice.sort ℓ -> raw_code A) rhs (pre : precond) (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
    ⊢ ⦃ pre ⦄
     #put ℓ := v ;;
     r v ≈ rhs ⦃ post ⦄ ->
    ⊢ ⦃ pre ⦄
        #put ℓ := v ;;
        x ← get ℓ ;;
        r x ≈ rhs ⦃ post ⦄.
Proof.
  intros.
  apply (r_transL (#put ℓ := v ;; r v )).
  apply r_put_get.
  apply H.
Qed.

Corollary better_r_put_get_rhs : forall (A : choice.Choice.type) (B : choice.Choice.type) (ℓ : Location) (v : choice.Choice.sort ℓ) (r : choice.Choice.sort ℓ -> raw_code B) lhs (pre : precond) (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
    ⊢ ⦃ pre ⦄
        lhs ≈
        #put ℓ := v ;;
        r v ⦃ post ⦄ ->
    ⊢ ⦃ pre ⦄
        lhs ≈
        #put ℓ := v ;;
        x ← get ℓ ;;
        r x ⦃ post ⦄.
Proof.
  intros.
  apply (r_transR _ (#put ℓ := v ;; r v )).
  apply r_put_get.
  apply H.
Qed.

Corollary better_r_get_remind_lhs : forall {A B : choice.Choice.type} (ℓ : Location)
       (v : choice.Choice.sort (Value (projT1 ℓ)))
       (r₀ : choice.Choice.sort (Value (projT1 ℓ)) -> raw_code A) (r₁ : raw_code B)
       (pre : precond) (post : postcond (choice.Choice.sort A) (choice.Choice.sort B)),
     Remembers_lhs ℓ v pre ->
     ⊢ ⦃ pre ⦄ r₀ v ≈ r₁ ⦃ post ⦄ ->
     ⊢ ⦃ pre ⦄ x ← get ℓ ;; r₀ x ≈ r₁ ⦃ post ⦄.
Proof.
  intros.
  apply better_r.
  eapply r_get_remind_lhs.
  apply H.
  apply better_r.
  apply H0.
Qed.

Lemma getr_set_lhs :
  forall {A B} ℓ v pre post (a : _ -> raw_code A) (b : raw_code B),
  ⊢ ⦃ set_lhs ℓ v pre ⦄
     a v
  ≈
     b
  ⦃ post ⦄ ->
  ⊢ ⦃ set_lhs ℓ v pre ⦄
     x ← get ℓ ;;
     a x
  ≈
     b
  ⦃ post ⦄.
Proof.
  clear.
  intros.

  eapply better_r_get_remind_lhs.
  unfold Remembers_lhs.
  intros ? ? [? []]. subst.
  unfold rem_lhs.
  rewrite get_set_heap_eq.
  reflexivity.
  apply H.
Qed.

Equations prod_to_prod {A B} (x : both (A × B)) : (both A * both B) :=
  prod_to_prod x :=
  (bind_both x (fun x' => solve_lift (ret_both (fst x'))) ,
   bind_both x (fun x' => solve_lift (ret_both (snd x')))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Equations let_both {A B} (x : both A) (f : both A -> both B) : both B :=
  let_both x f := f x.

Notation "'letb' x ':=' y 'in' f" :=
  (let_both y (fun x => f)) (at level 100, x pattern, right associativity).
Notation "'letb' ''' x ':=' y 'in' f" :=
  (let_both y (fun x => f)) (at level 100, x pattern, right associativity).

Fixpoint split_type (F : choice_type -> Type) (A : choice_type) : Type :=
  match A with
  | C × D => split_type F C * split_type F D
  | _ => F A
  end.

Fixpoint split_both {A} (x : both A) : (split_type (both) A) :=
   match A as c return (both c -> split_type (both) c) with
   | _ × _ => fun y => (split_both (fst (prod_to_prod y)) , split_both (snd (prod_to_prod y)))
   | _ => fun y : both _ => y
   end x.

Fixpoint unsplit_both {A} (s : split_type (both) A) : both A :=
  match A as c return (split_type (both) c -> both c) with
  | _ × _ =>
      fun y => prod_both ( unsplit_both (fst y)) ((unsplit_both (snd y)))
  | _ => fun y => y
  end s.

Notation "'unsplit_both_all' ( a , b , .. , c )" := ((.. ((unsplit_both a , unsplit_both b)) .. , unsplit_both c)).


(* Handle products of size 2 - 4 for letb *)

Fixpoint prod_to_prod_n_ty (n : nat) (F : choice_type -> Type) (A : choice_type) : Type :=
  match n with
  | O => F A
  | S n' =>
      match A with
      | B × C => (prod_to_prod_n_ty n' F B) * F C
      | _ => F A
      end
  end.
Eval simpl in prod_to_prod_n_ty 2 (both) ('nat × 'bool).

(* TODO: Currently duplicates code, due to prod_to_prod, should only evaluate and project the result ! *)
Fixpoint prod_to_prod_n {A} (n : nat) (x : both A) : prod_to_prod_n_ty n  (both) A :=
  match n as m return prod_to_prod_n_ty m (both) A with
  | O => x
  | S n' =>
      match A as B return both B -> prod_to_prod_n_ty (S n') (both) B with
      | B × C => fun y => (prod_to_prod_n n' (fst (prod_to_prod y)), snd (prod_to_prod y))
      | _ => fun y => y
      end x
  end.

Equations lift_n {A B} (n : nat) (z : both A) (f : prod_to_prod_n_ty n (both) A -> both B) : both B :=
  lift_n n z f :=
  (bind_both z (fun z' => f (prod_to_prod_n n (solve_lift (ret_both z'))))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Notation "'letb' ' '(' a ',' b ')' ':=' z 'in' f" :=
  (lift_n 1 z (fun '(a, b) => f))
    (at level 100).

Notation "'letb' ' '(' a ',' b ',' c ')' ':=' z 'in' f" :=
  (lift_n 2 z (fun '(a, b, c) => f))
    (at level 100).

Notation "'letb' ' '(' a ',' b ',' c ',' d ')' ':=' z 'in' f" :=
  (lift_n 3 z (fun '(a, b, c, d) => f))
    (at level 100).
