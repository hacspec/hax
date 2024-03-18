(* From extructures Require Import ord fset fmap. *)

(* Ltac left_assoc := *)
(*   repeat (match goal with *)
(*           | |- context [fsetU (fsetU ?a ?b) ?c] => *)
(*               replace (fsetU (fsetU a b) c) with (fsetU a (fsetU b c)) by apply fsetUA *)
(*           end). *)

(* Ltac prefer_is_true := *)
(*   match goal with *)
(*   | |- context [fsubset ?x ?y = true] => *)
(*       change (fsubset x y = true) with (is_true (fsubset x y)) *)
(*   end. *)

(* Ltac solve_structured_fsubset := *)
(*   left_assoc ; *)
(*   rewrite fsubUset ; apply andb_true_intro ; split ; [ apply fsubsetUl | prefer_is_true ; repeat match goal with *)
(*   | |- context [is_true (fsubset (fsetU _ _) (fsetU _ _)) ] => *)
(*       apply fsetUSS *)
(*   end ; (apply fsubsetxx || apply fsub0set) ]. *)

(* (* congruence? *) *)
(* Ltac solve_is_true_fast := (* fast ? *) *)
(*   try prefer_is_true ; *)
(*   apply fsubsetxx || *)
(*     (left_assoc ; *)
(*      match goal with *)
(*      | |- context [is_true (fsubset _ (fsetU ?x ?y)) ] => *)
(*          match goal with *)
(*          | |- context [is_true (fsubset ?lhs ?rhs) ] => *)
(*              let H_rhs := fresh in *)
(*              let H_f := fresh in *)
(*              let H_simpl := fresh in *)
(*              let H_ass_l := fresh in *)
(*              let H_ass_r := fresh in *)
(*              set (H_rhs := rhs) ; pattern x in H_rhs *)
(*              ; set (H_f := fun _ => _) in H_rhs *)
(*              ; set (H_simpl := H_f fset0) ; subst H_f *)
(*              ; assert (H_ass_l : is_true (fsubset lhs (fsetU H_simpl x))) by (subst H_rhs H_simpl ; hnf ; try rewrite !fset0U ; try rewrite ! fsetU0 ; solve_is_true_fast) *)
(*              ; assert (H_ass_r : is_true (fsubset (fsetU x H_simpl) rhs)) by (subst H_rhs H_simpl ; hnf ; solve_structured_fsubset) (* Should always be true (safe under approximation), by structure always eq or fset0 <= x *) *)
(*              ; replace (fsetU H_simpl x) with (fsetU x H_simpl) in H_ass_l by apply fsetUC *)
(*              ; apply (fsubset_trans H_ass_l H_ass_r) *)
(*          end *)
(*      end). *)

(* congruence? *)
(* Ltac solve_is_true_fast := (* fast ? *) *)
(*   try prefer_is_true ; *)
(*   apply fsubsetxx || *)
(*     (left_assoc ; *)
(*      match goal with *)
(*      | |- context [is_true (fsubset (fsetU ?x ?y) _) ] => *)
(*          match goal with *)
(*          | |- context [is_true (fsubset ?lhs ?rhs) ] => *)
(*              let H_rhs := fresh in *)
(*              let H_f := fresh in *)
(*              let H_simpl := fresh in *)
(*              let H_ass_l := fresh in *)
(*              let H_ass_r := fresh in *)
(*              set (H_rhs := rhs) ; pattern x in H_rhs *)
(*              ; set (H_f := fun _ => _) in H_rhs *)
(*              ; set (H_simpl := H_f fset0) ; subst H_f *)
(*              ; assert (H_ass_l : is_true (fsubset lhs (fsetU H_simpl x))) by (subst H_rhs H_simpl ; hnf ; try rewrite !fset0U ; try rewrite ! fsetU0 ; solve_is_true_fast) *)
(*              ; assert (H_ass_r : is_true (fsubset (fsetU x H_simpl) rhs)) by (subst H_rhs H_simpl ; hnf ; solve_structured_fsubset) (* Should always be true (safe under approximation), by structure always eq or fset0 <= x *) *)
(*              ; replace (fsetU H_simpl x) with (fsetU x H_simpl) in H_ass_l by apply fsetUC *)
(*              ; apply (fsubset_trans H_ass_l H_ass_r) *)
(*          end *)
(*      end). *)


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


(* Ltac GetPatterns pat res T :=  *)
(*   (* try prefer_is_true ; *) *)
(*   (left_assoc ; *)
(*    match pat with *)
(*    | (fsubset (fsetU ?x ?y) ?rhs) => *)
(*        let H_f := fresh in *)
(*        let temp := fresh in *)
(*        let H_sub := fresh in *)
(*        set (H_sub := fsubset _ _) ; *)
(*        pattern x in H_sub ; *)
(*        set (H_f := fun _ => _) in H_sub *)
(*        ; pose (H_f (@fset0 T)) *)
(*        ; match res with *)
(*          | fset0 => clear res ; set (res := x) *)
(*          | _ => set (temp := (res :|: x)%fset) *)
(*                ; subst res *)
(*                ; set (res := temp) *)
(*                ; subst temp *)
(*          end *)
(*        ;subst H_f *)
(*        ;subst H_sub *)
(*    end). *)

(* Goal forall (T : _) (L1 L2 : {fset (Ord.sort T)}), is_true (fsubset ( ( (fsetU (fsetU L1 (fsetU L1 L2)) (fsetU (fsetU (fsetU L1 L2) L1) L2)))) (fsetU L1 L2)  ). *)
(* Proof. *)
(*   intros. *)
(*   (* time solve_is_true_slow. *) *)

(*   left_assoc. *)
(*   set (res := (@fset0 T :|: L1)%fset). *)
(*   rewrite fset0U in res. *)

(*   GetPatterns (fsubset (L1 :|: (L1 :|: (L2 :|: (L1 :|: (L2 :|: (L1 :|: L2))))))%fset (L1 :|: L2)%fset) res T. *)
(*   rewrite fset0U in b. *)

(*   GetPatterns (fsubset (L1 :|: (L1 :|: (L2 :|: (L1 :|: (L2 :|: (L1 :|: L2))))))%fset (L1 :|: L2)%fset = true) res. *)
  

(*   assert (is_true (fsubset fset0 (fset0 :|: L1)%fset)). *)
(*   rewrite (@fset0E T). *)

(*   Set Printing Implicit. *)
(*   rewrite (@fset0U T L1) in res. *)
  
  
(*   GetPatterns (fsubset (fset0 :|: (fset0 :|: (L2 :|: (fset0 :|: (L2 :|: (fset0 :|: L2))))))%fset *)
(*                  (fset0 :|: L2)%fset = true) res. *)
  
(*   hnf in H1. *)
(*   try prefer_is_true. *)
(*   GetPatterns H1 res. *)
  
(*   try assert H1. *)
(*   2:{ *)
(*     GetPatterns (H1) res. *)
  
(*   rewrite <- fsetU0 in H1. *)

(*   pose (H (fset[])). *)
(*   GetPatterns P. *)
  
(*   try prefer_is_true ; *)
(*     (left_assoc ; *)
(*      match goal with *)
(*      | |- context [is_true (fsubset (fsetU ?x ?y) _) ] => *)
(*          match goal with *)
(*          | |- context [is_true (fsubset ?lhs ?rhs) ] => *)
(*              let H_f := fresh in *)
(*              pattern x ; *)
(*              set (H_f := fun _ => _) *)
(*              expression_of *)
(*          end *)
(*      end). *)
  

  
(*   caatime solve_is_true_fast. *)


(*** Ltac *)

Ltac normalize_fset :=
  hnf ;
  autounfold with * ;
  (* change ((Ord.sort *)
  (*            (@tag_ordType choice_type_ordType *)
  (*                          (fun _ : choice_type => nat_ordType)))) with *)
  (*   Location ; *)
  try rewrite !fset_cons ;
  try rewrite <- !fset0E ;
  try rewrite !fsetU0 ;
  try rewrite !fset0U ;
  try rewrite !fset1E ;
  (* try rewrite <- !fsetUA *)
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
  (apply fsub0set
   || apply fsubsetxx
   || (lazymatch (* match *) goal with
      | |- context [ fsubset ?a (?a :|: _) ] => apply fsubsetUl
      | |- context [ fsubset ?a (_ :|: ?a) ] => apply fsubsetUr
      | |- context [ fsubset fset0 _ ] => apply fsub0set
      | |- context [ fsubset ?a ?a ] => apply fsubsetxx
                                            (* | |- context [ fsubset ?a (?b :|: _) ] => assert (a = b) by reflexivity ; apply fsubsetUl *)
                                            (* | |- context [ fsubset ?a (_ :|: ?b) ] => assert (a = b) by reflexivity ; apply fsubsetUr *)
                                            (* | |- context [ fsubset ?a _ ] => assert (a = fset0) by reflexivity ; apply fsub0set *)
                                            (* | |- context [fsubset ?a ?b ] => assert (a = b) by reflexivity ; apply fsubsetxx *)
      end)).

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

(* Ltac solve_structured_fsubset := *)
(*   left_assoc ; *)
(*   try rewrite !fset_cons ; *)
(*   admit (* TODO solve head and tail recursively/iteratively *) *)

(* (* congruence? *) *)
(* Ltac solve_is_true_fast := (* fast ? *) *)
(*   easy || *)
(*   (left_assoc ; *)
(*    match goal with *)
(*    | |- context [is_true (fsubset _ (?x :|: ?y))] => *)
(*        match goal with *)
(*        | |- context [is_true (fsubset ?lhs ?rhs) ] => *)
(*            let H_rhs := fresh in *)
(*            let H_f := fresh in *)
(*            let H_simpl := fresh in *)
(*            let H_ass_l := fresh in *)
(*            let H_ass_r := fresh in *)
(*            set (H_rhs := rhs) ; pattern x in H_rhs ; *)
(*            set (H_f := fun _ => _) in H_rhs ; *)
(*            set (H_simpl := H_f fset0) ; subst H_f ; *)
(*            assert (H_ass_l : lhs = H_simpl :|: x) by (subst H_rhs H_simpl ; hnf ; try rewrite !fset0U ; try rewrite ! fsetU0 ; left_assoc ; solve_split_goal) ; *)
(*            assert (H_ass_r : x :|: H_simpl = rhs) by (subst H_rhs H_f ; hnf ; solve_structured_fsubset) ; (* Should always be true (safe under approximation), by structure always eq or fset0 <= x *) *)
(*            replace (H_simpl :|: x) with (x :|: H_simpl) in H_ass_l by apply add_commut ; *)
(*            transitivity (x :|: H_simpl) ; assumption *)
(*        end *)
(*    end). *)

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

(* Module Both. *)
(* Definition code_eq_proof_statement L I (A : choice_type) (functional : A) (state : code L I A) := *)
(*   ⊢ ⦃ true_precond ⦄ state ≈ ret (functional) *)
(*     ⦃ pre_to_post_ret true_precond (functional) ⦄. *)

(* Record mixin_of L I (A : choice_type) := Mixin { *)
(*                             functional : A  ; *)
(*                             state : code L I A ; *)
(*                             _ : code_eq_proof_statement L I A functional state ; *)
(*                         }. *)

(* Record class_of L I (A : choice_type) := *)
(*   Class {Base : choice.Choice.class_of A; mixin: mixin_of L I A}. *)

(* Structure both L I := *)
(*   Pack {sort; _ : class_of L I sort}. *)
(* End Both. *)

(* Class cfset := *)
(*   { *)
(*     L : list Location ; *)
(*     is_sorted : is_true (path.sorted (@Ord.lt _) L) ; *)
(*     is_unique : is_true (@seq.uniq loc_eqType L) *)
(*   }. *)
(* Definition cfset_to_fset : cfset -> {fset Location} := fun x => @FSet.FSet loc_ordType _ (FSet.fset_subproof (@L x)). *)
(* Coercion cfset_to_fset : cfset >-> fset_of. *)

(* Instance cfset0 : cfset := *)
(*   {| L := [] ; is_sorted := ltac:(reflexivity) ; is_unique := ltac:(reflexivity) |}. *)

(* Instance cfset1 (ℓ : Location) : cfset := *)
(*   {| L := [ℓ] ; is_sorted := ltac:(reflexivity) ; is_unique := ltac:(reflexivity) |}. *)

(* Require Import Hacspec_Lib_Comparable. *)
(* Program Fixpoint merge_undup (L1 L2 : list Location) {measure (length L1 + length L2)%nat} := *)
(*   match L1 with *)
(*   | [] => *)
(*       L2 *)
(*   | a :: xs => *)
(*       match L2 with *)
(*       | [] => a :: xs *)
(*       | b :: ys => *)
(*           if Ord.lt (* Hacspec_Lib_Comparable.leb *) a b *)
(*           then a :: merge_undup xs (b :: ys) *)
(*           else *)
(*             if Ord.lt b a (* Hacspec_Lib_Comparable.leb *) *)
(*             then b :: merge_undup (a :: xs) ys *)
(*             else a :: merge_undup xs ys *)
(*       end *)
(*   end. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   Lia.lia. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   Lia.lia. *)
(* Qed. *)
(* Fail Next Obligation. *)

(* Program Instance cfsetU (x y : cfset) : cfset := *)
(*   {| L := merge_undup (@L x) (@L y) ; |}. *)

(* Program Instance cfsetU (x y : cfset) : cfset := *)
(*   {| L := path.sort Ord.leq (@seq.undup loc_ordType (@L x ++ @L y)) ; |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   apply FSet.fset_subproof. *)
(* Qed. *)
(* Next Obligation. *)
(*   intros. *)
(*   apply (@path.sorted_uniq loc_ordType Ord.lt ). *)
(*   - apply Ord.lt_trans. *)
(*   - unfold ssrbool.irreflexive. *)
(*     intros. *)
(*     apply Ord.ltxx. *)
(*   - apply FSet.fset_subproof.  *)
(* Qed. *)
(* Fail Next Obligation. *)

From mathcomp Require Import ssrbool.

Section Both.

  Context (L : {fset Location}).
  Context (I : Interface).
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
    forall x, valid_both {| is_pure := x ; is_state := ret x |}
  | both_valid_putr_getr :
    forall l k v,
      l \in L ->
      (forall v, valid_both (k v)) ->
      valid_both
        ({| is_pure := @is_pure (k v) ;
           is_state := putr l v (getr l (fun x => @is_state (k x))) |})
  (* | both_valid_getr : *)
  (*   forall (l : Location) (v : l) (k : l -> raw_both), *)
  (*     l \in L -> *)
  (*     valid_both ({| is_pure := @is_pure (k v) ; is_state := @is_state (k v) |}) -> *)
  (*     valid_both ({| is_pure := @is_pure (k v) ; is_state := getr l (fun v => @is_state (k v)) |}) *)
  | both_valid_putr :
    forall l v k,
      l \in L ->
      valid_both k ->
      valid_both ({| is_pure := @is_pure k ; is_state := putr l v (@is_state k) |}).

  (* | valid_opr : *)
  (*   forall o x k, *)
  (*     o \in import -> *)
  (*           (forall v, valid_both (k v)) -> *)
  (*           valid_both ({| is_pure := k v ;  opr o x k |}) *)

  (* | valid_sampler : *)
  (*   forall op k, *)
  (*     (forall v, valid_code (k v)) -> *)
  (*     valid_code (sampler op k) *)

  Class ValidBoth (p : raw_both) :=
    { is_valid_code : ValidCode L I (@is_state p) ;
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

Arguments valid_both L {_}.
Arguments both_valid_ret L {_}.
Arguments both_valid_putr_getr L {_}.
Arguments both_valid_putr L {_}.

Arguments ValidBoth L I {_} p.
Arguments is_valid_code {_} {_} {_} {_} ValidBoth.
Arguments is_valid_both {_} {_} {_} {_} ValidBoth.

Arguments both_prog {_} {_} {_} b.
Arguments both_prog_valid {_} {_} {_} b.
Arguments p_eq {_} {_} {_} b.

Section Both_helper.

  Lemma valid_both_eta :
    forall {L (* I *)} {A : choice_type} {x : raw_both A},
      valid_both L (* I *) x ->
      valid_both L (* I *) {| is_pure := is_pure x ; is_state := is_state x |}.
  Proof.
    now intros ? (* ? *) ? [] ?.
  Defined.

  Lemma ValidBoth_eta :
    forall {L I} {A : choice_type} {x : both L I A},
      ValidBoth L I x ->
      ValidBoth L I {| is_pure := is_pure x ; is_state := is_state x |}.
  Proof.
    now intros ? ? ? [[] ? ?] ?.
  Defined.

  Lemma both_valid_injectLocations :
    forall A L1 L2 (* I *) (v : raw_both A),
      fsubset L1 L2 ->
      valid_both L1 (* I *) v ->
      valid_both L2 (* I *) v.
  Proof.
    intros A L1 L2 (* I *) v h p.
    induction p ; simpl in * ; intros.
    + constructor.
    + apply both_valid_putr_getr ; eauto.
      eapply injectSubset.
      apply h.
      assumption.
    (* - constructor ; eauto. *)
    (*   eapply injectSubset. *)
    (*   apply h. *)
    (*   assumption. *)
    - constructor ; eauto.
      eapply injectSubset.
      apply h.
      assumption.
  Qed.

  Lemma valid_injectLocations_both :
    forall A L1 L2 I (v : raw_both A),
      fsubset L1 L2 ->
      ValidBoth L1 I v ->
      ValidBoth L2 I v.
  Proof.
    intros A L1 L2 I v h p.
    destruct p as [is_valid_code valid_both].
    constructor.
    - eapply valid_injectLocations.
      apply h.
      apply is_valid_code.
    - eapply both_valid_injectLocations.
      apply h.
      apply valid_both.
  Qed.

  Lemma valid_injectMap_both :
    forall A L I1 I2 (v : raw_both A),
      fsubset I1 I2 ->
      ValidBoth L I1 v ->
      ValidBoth L I2 v.
  Proof.
    intros A L I1 I2 v h p.
    destruct p as [is_valid_code valid_both].
    constructor.
    - eapply valid_injectMap.
      apply h.
      apply is_valid_code.
    - generalize dependent is_valid_code.
      induction valid_both ; simpl in *.
      + constructor.
      + constructor ; eauto.
      (* + constructor ; eauto. *)
      + constructor ; eauto.
  Qed.

  Definition bind_raw_both {A B} (c : raw_both A) (k : A -> raw_both B) : raw_both B :=
    {|
      is_pure := let x := (is_pure c) in is_pure (k x) ;
      is_state := bind (is_state c) (fun x => is_state (k x))
    |}.

  Lemma valid_bind_both_ :
    forall {L1 L2 (* I1 I2 *)} A B c k,
      valid_both L1 (* I1 *) c ->
      (forall x, valid_both L2 (* I2 *) {| is_pure := is_pure (k x) ; is_state := is_state (k x) |}) ->
      `{is_true (fsubset L1 L2)} ->
      valid_both L2 (@bind_raw_both A B c k).
  Proof.
    intros L1 L2 (* I1 I2 *) A B c k Hc Hk Hfsubset.
    induction Hc ; intros.
    - apply Hk.
    - unfold bind_raw_both.
      simpl.
      apply (both_valid_putr_getr L2 l (fun l => bind_raw_both (k0 l) k) v (injectSubset Hfsubset H) H1).
    (* - admit. *)
    - apply (both_valid_putr L2 l v (bind_raw_both k0 k) (injectSubset Hfsubset H) IHHc).
  (* Admitted. *)
  Qed.

  Lemma valid_bind_both :
    forall {L1 L2 I1 I2} A B c k,
      ValidBoth L1 I1 c ->
      (forall x, ValidBoth L2 I2 (k x)) ->
      `{fsubset L1 L2} ->
      `{fsubset I1 I2} ->
      ValidBoth L2 I2 (@bind_raw_both A B c k).
  Proof.
    intros L1 L2 I1 I2 A B c k Hc Hk Hloc Hopsig.
    constructor ; simpl.
    - apply valid_bind.
      eapply valid_injectLocations. apply Hloc.
      eapply valid_injectMap. apply Hopsig.
      apply (is_valid_code Hc).
      apply (fun x => is_valid_code (Hk x)).
    - eapply valid_bind_both_.
      apply (is_valid_both Hc).
      intros.
      apply valid_both_eta.
      apply (fun x => is_valid_both (Hk x)).
      assumption.
  Qed.

  Instance valid_putr_both :
    forall {L I A} ℓ v (k : both L I A),
      ℓ \in L ->
      ValidBoth L I ({| is_pure := is_pure k ; is_state := #put ℓ := v ;; is_state k |}).
  Proof.
    intros.
    constructor.
    - simpl.
      apply valid_putr. assumption.
      apply k.
    - apply both_valid_putr. assumption.
      apply k.
  Qed. 

  (* Instance valid_getr_both : *)
  (*   forall {L I A} (ℓ : Location) (v : ℓ) (k : ℓ -> both L I A), *)
  (*     ℓ \in L -> *)
  (*     ValidBoth L I ({| is_pure := is_pure (k v) ; is_state := v ← get ℓ ;; is_state (k v) |}). *)
  (* Proof. *)
  (*   intros. *)
  (*   constructor. *)
  (*   - simpl. *)
  (*     apply valid_getr. assumption. *)
  (*     apply k. *)
  (*   - apply (both_valid_getr L A ℓ v k H). *)
  (*     apply valid_both_eta. *)
  (*     apply (both_prog_valid (k v)). *)
  (* Qed. *)

  Instance valid_putr_getr_both :
    forall {L I A} ℓ v (k : _ -> both L I A),
      ℓ \in L ->
      (forall v, ValidBoth L I (k v)) ->
      ValidBoth L I ({| is_pure := is_pure (k v) ;
           is_state := putr ℓ v (getr ℓ (fun x => is_state (k x))) |}).
  Proof.
    intros.
    constructor.
    - simpl.
      apply valid_putr. assumption.
      apply valid_getr. assumption.
      apply k.
    - apply (both_valid_putr_getr L (* I *) ℓ k v H).
      apply H0.
  Qed.

  
  Definition both_ret {A : choice_type} (x : A) : raw_both A :=
    {| is_pure := x ; is_state := ret x |} .

  Program Definition both_ret_valid {L I} {A : choice_type} (x : A) : ValidBoth L I (both_ret x) :=
    {| is_valid_code := valid_ret _ _ _ ; is_valid_both := both_valid_ret L (* I *) _ |} 
    .
  Fail Next Obligation.

  
End Both_helper.

Program Definition ret_both (* {L I} *) {A : choice_type} (x : A) : both (fset []) ([interface]) A :=
  {|
    both_prog := {| is_pure := x ; is_state := ret x |} ;
    both_prog_valid := {|
                        is_valid_code := valid_ret (fset []) ([interface]) x ;
                        is_valid_both := both_valid_ret (fset []) x ;
                      |} ;
    p_eq := r_ret _ _ _ _ _ ;
  |}.
Fail Next Obligation.

(* Program Definition ret_both {L I} {A : choice_type} (x : A) : both L I A := *)
(*   {| *)
(*     both_prog := {| is_pure := x ; is_state := ret x |} ; *)
(*     both_prog_valid := {| *)
(*                         is_valid_code := valid_ret L I x ; *)
(*                         is_valid_both := both_valid_ret L x ; *)
(*                       |} ; *)
(*     p_eq := r_ret _ _ _ _ _ ; *)
(*   |}. *)
(* Fail Next Obligation. *)

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

Theorem r_bind_trans_both : forall {B C : choice_type} {L I} {f : choice.Choice.sort B -> raw_code C} {g : choice.Choice.sort B -> raw_code C} (b : both L I B),
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

Program Definition bind_both {L1 L2 I1 I2} {A B} (c : both L1 I1 A) (k : A -> both L2 I2 B) `{fsubset_loc : fsubset L1 L2} `{fsubset_opsig : fsubset I1 I2} : both L2 I2 B :=
  {|
    both_prog := bind_raw_both (both_prog c) (fun x => both_prog (k x)) ;
    both_prog_valid := valid_bind_both A B c k (both_prog_valid c) (fun x => both_prog_valid (k x)) _ _ ;
  |}.
Next Obligation.
  intros.
  r_subst_both c.
  apply (k (is_pure c)).
Qed.

Lemma both_eq : forall {A : choice_type} {L I} (a b : both L I A),
    both_prog a = both_prog b ->
    a = b.
Proof.
  intros.
  destruct a , b.
  cbn in *. subst.
  f_equal ; apply proof_irrelevance.
Qed.

Lemma bind_ret_both : forall {A B : choice_type} {L I} `{fsubset_loc : is_true (fsubset (fset []) L)} `{fsubset_opsig : is_true (fsubset (fset []) I)} (f : A -> both L I B) (x : A),
    (bind_both (fsubset_loc := fsubset_loc) (fsubset_opsig := fsubset_opsig) (ret_both x) f) = f x.
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

Definition lift_both {L1 L2 I1 I2} {A} (x : both L1 I1 A) `{fsubset_loc : is_true (fsubset L1 L2)} `{fsubset_opsig : is_true (fsubset I1 I2)} : both L2 I2 A :=
    {| both_prog := x ;
      both_prog_valid := valid_injectLocations_both A L1 L2 I2 x fsubset_loc (valid_injectMap_both A L1 I1 I2 x fsubset_opsig (both_prog_valid x)) ;
      p_eq := p_eq x |}.

Notation "'solve_lift' x" := (lift_both (* (L1 := _) (L2 := _) (I1 := _) (I2 := _) (A := _) *) x (* (fsubset_loc := _) (fsubset_opsig := _) *)) (at level 100).

Equations lift1_both {A B : choice_type} {L : {fset Location}} {I : Interface} (f : A -> B) (x : both L I A)
        (* `{H_loc_incl_x : is_true (fsubset L1 L2)} `{H_opsig_incl_x : is_true (fsubset I1 I2)} *)
  : both L I B
  :=
  lift1_both f x := bind_both x (fun x' => solve_lift (ret_both (f x'))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Equations lift2_both {A B C : choice_type} {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} (f : A -> B -> C) (x : both L1 I1 A) (y : both L2 I2 B)
        (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
        (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *)
  : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) C
  :=
  lift2_both f x y :=
    bind_both x (fun x' =>
    bind_both y (fun y' =>
    solve_lift (ret_both (f x' y')))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Equations lift3_both {A B C D : choice_type} {L1 L2 L3 (* L4 *) : {fset Location}} {I1 I2 I3 (* I4 *) : Interface} (f : A -> B -> C -> D) (x : both L1 I1 A) (y : both L2 I2 B) (z : both L3 I3 C)
        (* `{H_loc_incl_x : is_true (fsubset L1 L4)} `{H_opsig_incl_x : is_true (fsubset I1 I4)} *)
        (* `{H_loc_incl_y : is_true (fsubset L2 L4)} `{H_opsig_incl_y : is_true (fsubset I2 I4)} *)
        (* `{H_loc_incl_z : is_true (fsubset L3 L4)} `{H_opsig_incl_z : is_true (fsubset I3 I4)} *)
  : both (L1 :|: L2 :|: L3) (* L4 *) (I1 :|: I2 :|: I3) (* I4 *) D :=
  lift3_both f x y z :=
  bind_both x (fun x' => lift_both (lift2_both (f x') y z)).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

(* Class both (L : {fset Location}) I (A : choice_type) := *)
(*   { *)
(*     is_pure : choice.Choice.sort A ; *)
(*     is_state : code L I A ; *)
(*     code_eq_proof_statement : *)
(*     ⊢ ⦃ true_precond ⦄ is_state ≈ ret (is_pure) *)
(*       ⦃ pre_to_post_ret true_precond (is_pure) ⦄ *)
(*   }. *)

(* Class both L I (A : choice_type) := *)
(*   { *)
(*     is_pure : choice.Choice.sort A ; *)
(*     is_state : code L I A ; *)
(*     code_eq_proof_statement : *)
(*     ⊢ ⦃ true_precond ⦄ is_state ≈ ret (is_pure) *)
(*       ⦃ pre_to_post_ret true_precond (is_pure) ⦄ *)
(*   }. *)

(* Arguments is_pure {_} {_} {_} both. *)
(* Arguments is_state {_} {_} {_} both. *)
(* Arguments code_eq_proof_statement {_} {_} {_} both. *)

(* Coercion is_pure : both >-> choice.Choice.sort. *)
(* Coercion is_state : both >-> code. *)

(* Definition both_fun (L : cfset) I (A B : choice_type) := *)
(*   ∑ (is_pure_f : choice.Choice.sort A -> choice.Choice.sort B) (is_state_f : code L I A -> code L I B), *)
(*     forall (x : both L I A), ⊢ ⦃ true_precond ⦄ is_state_f x ≈ ret (is_pure_f x) ⦃ pre_to_post_ret true_precond (is_pure_f (is_pure x)) ⦄. *)

(* Lemma helper : *)
(*   forall (o : opsigCE), *)
(*     choice.Choice.sort (fst (snd o)) = choice.Choice.sort (src (opsigCE_opsig o)). *)
(* Proof. now intros [? []]. Qed. *)

(* Lemma pack_helper : *)
(*   forall {E : InterfaceCE} {o} (H : In o E), *)
(*     is_true *)
(*    (ssrbool.in_mem (opsigCE_opsig o) *)
(*       (ssrbool.mem (IfToCEIf E))). *)
(* Proof. *)
(*   intros. *)
(*   apply (ssrbool.introT (xseq.InP _ _)). *)
(*   unfold IfToCEIf. *)
(*   apply -> (in_remove_fset (T:=opsig_ordType)). *)
(*   apply in_map. *)
(*   apply H. *)
(* Defined. *)

(* Class both_package L I (E : InterfaceCE) := *)
(*   { *)
(*     pack_pure : forall o, List.In o E -> fst (snd o) -> snd (snd o) ; *)
(*     pack_state : package L I (IfToCEIf E) ; *)
(*     pack_eq_proof_statement : forall i s t (H : In (i,(s,t)) E), forall (v : s), *)
(*       forall f, (pack pack_state) i = Some *)
(*     (existT *)
(*        (fun S0 : choice_type => {T0 : choice_type & choice.Choice.sort S0 -> raw_code T0}) *)
(*        s (existT (fun T0 : choice_type => choice.Choice.sort s -> raw_code T0) t f)) -> *)
(*       ⊢ ⦃ true_precond ⦄ *)
(*           f v *)
(*           ≈ lift_to_code (L := L) (I := I) (pack_pure (i,(s,t)) H v) *)
(*       ⦃ pre_to_post_ret true_precond (T_ct (pack_pure (i,(s,t)) H v)) ⦄ *)
(*   }. *)

(* Arguments pack_pure {_} {_} {_} {_} {_} {_} both_package. *)
(* Arguments pack_state {_} {_} {_} both_package. *)

(* Coercion pack_pure : both_package >-> Funclass. *)
(* Coercion pack_state : both_package >-> package. *)

(* Instance package_both {L I} {x y z} (pkg : both_package L I ((x, (y, z)) :: nil)) (args : y) *)
(*   : both L I (z). *)
(* Proof. *)
(*   destruct pkg as [pure state eq_proof]. *)
(*   pose (o := (x, (y, z)) : opsigCE). *)
(*   refine {| is_pure := pure o (List.in_eq _ _) args ; *)
(*            is_state := {code get_op_default state (opsigCE_opsig o) (args) #with valid_get_op_default _ _ _ state (opsigCE_opsig o) (args) _ (pack_helper (List.in_eq _ _)) } |}. *)
(*   apply eq_proof. *)
(*   cbn. *)
(*   destruct (from_valid_package _ _ _ _ (pack_valid state) (opsigCE_opsig o) (pack_helper (List.in_eq _ _))) as [? []]. *)
(*   rewrite H. *)
(*   apply f_equal. *)
(*   apply f_equal. *)
(*   apply f_equal. *)
(*   unfold get_op_default. *)
(*   cbn. *)
(*   rewrite H. *)
(*   destruct choice_type_eqP ; [ | contradiction ]. *)
(*   destruct choice_type_eqP ; [ | contradiction ]. *)
(*   rewrite pkg_composition.cast_fun_K. *)
(*   reflexivity. *)
(* Defined. *)

(* Program Instance both_package' L I o (bf : T (fst (snd o)) -> both L I (snd (snd o))) *)
(*   : both_package L I (o :: nil) := *)
(*   {| *)
(*     pack_pure := fun o0 H => ltac:((assert (o = o0) by now destruct H) ; subst ; apply bf ; apply X) ; *)
(*     pack_state := (mkpackage (mkfmap ((fst o, pkg_composition.mkdef _ _ (fun x => bf (ct_T x))) :: nil)) (valid_package1 L I (fst o) (fst (snd o)) (snd (snd o)) (fun x => bf (ct_T x)) (fun x => prog_valid (is_state (bf (ct_T x)))))) ; *)
(*     pack_eq_proof_statement := _ *)
(*   |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   destruct H ; [ subst | contradiction ]. *)
(*   cbn in H0. *)
(*   rewrite (ssrbool.introT ssrnat.eqnP eq_refl) in H0. *)
(*   inversion H0. *)
(*   do 2 apply Eqdep.EqdepTheory.inj_pair2 in H1. *)
(*   subst. *)
(*   cbn. *)
(*   rewrite ct_T_id. *)
(*   apply bf. *)
(* Defined. *)

Definition choice_type_size (ce : choice_type) : nat.
Proof.
  (* remember ce. *)
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

(* Equations? lift_to_code2 (ce : choice_type) {L I} (x : choice.Choice.sort ce) : code L I ce := *)
(*   lift_to_code2 'unit x := {code ret x} ; *)
(*   lift_to_code2 'nat x := {code ret x} ; *)
(*   lift_to_code2 'int x := {code ret x} ; *)
(*   lift_to_code2 'bool x := {code ret x} ; *)
(*   lift_to_code2 (chFin _) x := {code ret x} ; *)
(*   lift_to_code2 ('word _) x := {code ret x} ; *)
(*   lift_to_code2 (Y × Z) (y, z) := *)
(*     {code temp_y ← lift_to_code2 Y y ;; *)
(*      temp_z ← lift_to_code2 Z z ;; *)
(*      ret ((temp_y, temp_z) : Y × Z)} ; *)
(*   lift_to_code2 (chMap Y Z) y :=  *)
(*     {code *)
(*        targets ← lift_to_code2 _ (seq.zip (List.map (ce_to_chElement_ordType_ce Y) (seq.unzip1 (FMap.fmval y))) (seq.unzip2 (FMap.fmval y)) : chList (Y × _))  ;; *)
(*      ret (mkfmap (seq.zip (List.map (chElement_ordType_ce_to_ce Y) (seq.unzip1 targets)) (seq.unzip2 targets)))} ; *)
(*   lift_to_code2 ('option Y) y := *)
(*       {code match y with *)
(*             | None => ret (None : 'option Y) *)
(*             | Some y => (temp_y ← lift_to_code2 _ y ;; *)
(*                         ret (Some temp_y : 'option Y)) *)
(*               end } ; *)
(*   lift_to_code2 (chList Y) y := *)
(*       {code (List.fold_right *)
(*                      (fun (a : Y) *)
(*                         (b : raw_code (chList Y)) => *)
(*                         temp_a ← lift_to_code2 _ a ;; *)
(*                         temp_b ← b ;; *)
(*                         ret (temp_a :: temp_b : chList Y)) *)
(*                      (ret (nil : chList Y)) (y : list Y)) #with _} ; *)
(*   lift_to_code2 (Y ∐ Z) y := *)
(*       fun y _ => *)
(*         {code match y with *)
(*               | inl y' => temp_y ← (lift_to_code2 y') ;; ret (inl temp_y : Y ∐ Z) *)
(*               | inr y' => temp_y ← (lift_to_code2 y') ;; ret (inr temp_y : Y ∐ Z) *)
(*               end} *)
(*   . *)

(* Program Fixpoint lift_to_code2 {ce : choice_type} {L I} (x : choice.Choice.sort ce) {measure (choice_type_size ce)} : code L I ce := *)
(*   match ce as A return A -> A = ce -> code L I A with *)
(*   | 'unit | 'nat | 'int | 'bool | chFin _ | 'word _ => fun y _ => {code ret y} *)
(*   | Y × Z => fun yz H => *)
(*               {code temp_y ← @lift_to_code2 _ _ _ (fst yz) (eq_ind (Y × Z) *)
(*     (fun ce => choice_type_size Y < choice_type_size ce) *)
(*     (eq_ind (S (choice_type_size Y) + choice_type_size Z)%nat *)
(*        (fun n : nat => choice_type_size Y < n) *)
(*        (lt_plus_trans (choice_type_size Y) (S (choice_type_size Y)) *)
(*           (choice_type_size Z) (Nat.lt_succ_diag_r (choice_type_size Y))) *)
(*        (S (choice_type_size Y + choice_type_size Z)) *)
(*        (Nat.add_succ_l (choice_type_size Y) (choice_type_size Z))) ce H) ;; *)
(*                temp_z ← lift_to_code2 (snd yz) ;; *)
(*                ret ((temp_y, temp_z) : Y × Z) #with _} *)
(*   | chMap Y Z => *)
(*       fun y _ => *)
(*         {code *)
(*            targets ← lift_to_code2 (seq.zip (List.map (ce_to_chElement_ordType_ce Y) (seq.unzip1 (FMap.fmval y))) (seq.unzip2 (FMap.fmval y)) : chList (Y × _))  ;; *)
(*          ret (mkfmap (seq.zip (List.map (chElement_ordType_ce_to_ce Y) (seq.unzip1 targets)) (seq.unzip2 targets))) #with _} *)
(*   | 'option Y => *)
(*       fun y _ => *)
(*         {code match y with *)
(*               | None => ret (None : 'option Y) *)
(*               | Some y => (temp_y ← lift_to_code2 (L := L) (I := I) y ;; *)
(*                           ret (Some temp_y : 'option Y)) *)
(*               end #with _} *)
(*   | chList Y => *)
(*       fun y  _=> {code (List.fold_right *)
(*                      (fun (a : Y) *)
(*                         (b : raw_code (chList Y)) => *)
(*                         temp_a ← lift_to_code2 (L := L) (I := I) a ;; *)
(*                         temp_b ← b ;; *)
(*                         ret (temp_a :: temp_b : chList Y)) *)
(*                      (ret (nil : chList Y)) (y : list Y)) #with _} *)
(*   | Y ∐ Z => *)
(*       fun y _ => *)
(*         {code match y with *)
(*               | inl y' => temp_y ← (lift_to_code2 (L := L) (I := I) y') ;; ret (inl temp_y : Y ∐ Z) *)
(*               | inr y' => temp_y ← (lift_to_code2 (L := L) (I := I) y') ;; ret (inr temp_y : Y ∐ Z) *)
(*               end #with _} *)
(*   end x eq_refl. *)
(* Next Obligation. *)
(*   intros. *)
(*   refine (eq_ind (Y × Z) *)
(*     (fun ce => choice_type_size Z < choice_type_size ce) *)
(*     (eq_ind ((choice_type_size Y) + S (choice_type_size Z))%nat *)
(*        (fun n : nat => choice_type_size Z < n) *)
(*        (lt_plus_trans (choice_type_size Z) (S (choice_type_size Z)) *)
(*           (choice_type_size Z) (Nat.lt_succ_diag_r (choice_type_size Z))) *)
(*        ((choice_type_size Y + S (choice_type_size Z)) *)
(*        (Nat.add_succ_r (choice_type_size Y) (choice_type_size Z))) ce H)). *)
(*   refine (eq_ind (Y × Z) *)
(*     (fun ce0 : choice_type => choice_type_size Y < choice_type_size ce0) _ ce H). *)
(*   simpl. *)
(*   rewrite <- Nat.add_succ_l. *)
(*   apply lt_plus_trans. *)
(*   apply Nat.lt_succ_diag_r. *)
(*   Show Proof. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   rewrite <- Nat.add_succ_r. *)
(*   rewrite Nat.add_comm. *)
(*   apply lt_plus_trans. *)
(*   apply Nat.lt_succ_diag_r. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   destruct y. *)
(*   simpl. *)
(*   ssprove_valid. *)
(*   apply lift_to_code2. *)
(*   apply valid_ret. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   induction y. *)
(*   simpl. *)
(*   ssprove_valid. *)
(*   simpl. *)
(*   ssprove_valid. *)
(*   apply lift_to_code2. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   rewrite <- Nat.add_succ_l. *)
(*   apply lt_plus_trans. *)
(*   apply Nat.lt_succ_diag_r. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   rewrite <- Nat.add_succ_r. *)
(*   rewrite Nat.add_comm. *)
(*   apply lt_plus_trans. *)
(*   apply Nat.lt_succ_diag_r. *)
(* Defined. *)
(* Next Obligation. *)
(*   intros. *)
(*   subst. *)
(*   simpl. *)
(*   destruct y. *)
(*   ssprove_valid. *)
(*   apply lift_to_code2. *)
(*   ssprove_valid. *)
(*   apply lift_to_code2. *)
(* Defined. *)

(* Program Fixpoint lift_to_both {ce : choice_type} {L I} (x : choice.Choice.sort ce) : both L I ce := *)
(*   {| is_pure := x ; *)
(*     is_state := lift_to_code x |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   now apply r_ret. *)
(* Defined. *)

(* Notation "'lift_to_both' x" := *)
(*   ({| is_pure := x ; *)
(*     is_state := {code ret x #with valid_ret _ _ x }; *)
(*     code_eq_proof_statement := r_ret x x true_precond (pre_to_post_ret true_precond x) (fun (s₀ s₁ : heap) => conj (conj eq_refl eq_refl)) *)
(*   |}) (at level 100). *)
(* Notation both0 := (both (fset []) [interface]). *)
(* Notation lift_to_both0 := (@lift_to_both _ fset.fset0 [interface]). *)

(* Definition lift_code_scope {L1 L2 : {fset Location}} {I1 I2 : {fset opsig}} {A} (c : code L1 I1 A) `{H_loc_incl : List.incl L1 L2} `{H_opsig_incl : List.incl I1 I2} : code L2 I2 A := *)
(*   {code (prog c) #with *)
(*     (@valid_injectMap L2 A I1 I2 _ (proj2 (opsig_list_incl_fsubset _ _) H_opsig_incl) (@valid_injectLocations I1 A L1 L2 _ (proj2 (loc_list_incl_fsubset _ _) H_loc_incl) (prog_valid c))) }. *)

(* Program Definition lift_scope {L1 L2 : {fset Location}} {I1 I2 : {fset opsig}} {A} (b : both L1 I1 A) : both L2 I2 A := *)
(*   {| *)
(*     both_prog := both_prog b ; *)
(*   |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   apply (@valid_injectMap L2 A I1 I2 _ ). *)
  
(*     {| *)
(*       prog := {| is_pure := is_pure b ; prog (is_state b) |} ; *)
(*     is_state := {code (prog (is_state b)) #with *)
(*     (@valid_injectMap L2 A I1 I2 _ (proj2 (opsig_list_incl_fsubset _ _) H_opsig_incl) (@valid_injectLocations I1 A L1 L2 _ (proj2 (loc_list_incl_fsubset _ _) H_loc_incl) (prog_valid (is_state b)))) } ; *)
(*     code_eq_proof_statement := code_eq_proof_statement b *)
(*   |}. *)

(* Definition lift_scope {L1 L2 : {fset Location}} {I1 I2 : {fset opsig}} {A} (b : both L1 I1 A) `{H_loc_incl : List.incl L1 L2} `{H_opsig_incl : List.incl I1 I2} : both L2 I2 A := *)
(*   {| *)
(*     is_pure := is_pure b ; *)
(*     is_state := lift_code_scope (H_loc_incl := H_loc_incl) (H_opsig_incl := H_opsig_incl) (is_state b) ; *)
(*     code_eq_proof_statement := code_eq_proof_statement b *)
(*   |}. *)

(* Definition lift_scopeI *)
(*   {L1 L2 : {fset Location}} {I : {fset opsig}} {A} (b : both L1 I A) `{H_loc_incl : List.incl L1 L2} : both L2 I A := *)
(*   {| *)
(*     is_pure := is_pure b ; *)
(*     is_state := lift_code_scope (H_loc_incl := H_loc_incl) (H_opsig_incl := incl_refl _) (is_state b) ; *)
(*     code_eq_proof_statement := code_eq_proof_statement b *)
(*   |}. *)

(* Definition lift_scope0 {L I} {A} (b : both fset0 [interface] A) : both L I A := *)
(*   lift_scope (H_loc_incl := incl_nil_l _) (H_opsig_incl := ltac:(rewrite <- fset0E ; apply incl_nil_l)) b. *)

(* (* TODO: *) *)
(* Instance both_comparable {A : choice_type} `{Comparable (choice.Choice.sort A)} {L I} : Comparable (both L I A) := *)
(*   {| *)
(*     ltb x y := ltb (is_pure x) (is_pure y) ; *)
(*     leb x y := leb (is_pure x) (is_pure y) ; *)
(*     gtb x y := gtb (is_pure x) (is_pure y) ; *)
(*     geb x y := geb (is_pure x) (is_pure y) *)
(*   |}. *)

(* Goal forall (L1 L2 : cfset), True. *)
(*   intros. *)
(*   assert (cfsetU L1 L2 = cfsetU L2 L1). *)
  

(* Theorem valid_cfsetUl : *)
(*   forall A (L1 L2 : cfset) I (c : raw_code A), *)
(*   valid_code L1 I c -> *)
(*   valid_code (cfsetU L1 L2) I c. *)
(* Proof. *)
(*   intros. *)
(*   apply valid_injectLocations with (L1 := L1). *)
(*   destruct L1. *)
(*   unfold cfset_to_fset in *. *)
(*   cbn. *)

  
(*   intros. *)
(*   destruct L2. *)
(*   induction L0. *)
(*   - unfold cfsetU. *)
(*     cbn. *)

Equations prod_both {ceA ceB : choice_type} {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : {fset _}} (a : both L1 I1 ceA) (b : both L2 I2 ceB) (* `{fsubset L1 L3} `{fsubset I1 I3} `{fsubset L2 L3} `{fsubset I2 I3} *) : both (L1 :|: L2) (I1 :|: I2) (ceA × ceB) :=
  prod_both a b :=
    bind_both a (fun a' =>
    bind_both b (fun b' =>
                   solve_lift (ret_both ((a', b') : _ × _)))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

Notation "'prod_b' ( a , b )" := (prod_both a b) : hacspec_scope.
Notation "'prod_b' ( a , b , .. , c )" := (prod_both .. (prod_both a b) .. c) : hacspec_scope.

(* Equations *) Program Definition prod_both0 {ceA ceB : choice_type} {L : {fset _}} {I : {fset _}} (a : both L I ceA) (b : both L I ceB) : both (L) (I) (ceA × ceB) :=
  (* prod_both0 a b := *)
  prod_both a b.
Solve All Obligations with intros ; fset_equality.
Fail Next Obligation.

(* Notation "prod_b0( a , b )" := (prod_both0 a b) : hacspec_scope. *)
(* Notation "prod_b0( a , b , .. , c )" := (prod_both0 .. (prod_both0 a b) .. c) : hacspec_scope. *)

(* Ltac ssprove_valid_fset T := *)
(*   apply (fset_compute (T:=T)) ; try apply -> (in_remove_fset (T:=T)) ; repeat (try (left ; reflexivity) ; right) ; try reflexivity. *)

(* Ltac ssprove_valid_location := ssprove_valid_fset loc_ordType. *)
(* Ltac ssprove_valid_opsig := ssprove_valid_fset opsig_ordType. *)

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

(* Theorem single_mem : forall m, *)
(* Datatypes.is_true *)
(*     (@ssrbool.in_mem *)
(*        (Ord.sort (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) *)
(*        m *)
(*        (@ssrbool.mem *)
(*           (Ord.sort *)
(*              (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) *)
(*           (fset_predType *)
(*              (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))) *)
(*           (@fset (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType)) *)
(*              (@cons (@sigT choice_type (fun _ : choice_type => nat)) m *)
(*                     (@nil (@sigT choice_type (fun _ : choice_type => nat))))))). *)
(* Proof. *)
(*   intros. *)
(*   rewrite <- (@fset1E (@tag_ordType choice_type_ordType (fun _ : choice_type => nat_ordType))). *)
(*   rewrite (ssrbool.introT (fset1P _ _)) ; reflexivity. *)
(* Qed. *)

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

(* Ltac loc_incl_compute := *)
(*   now (try apply -> loc_list_incl_remove_fset ; apply loc_list_incl_expand ; (now repeat (split ; [ repeat ((left ; reflexivity) || (right)) | ]))). *)

(* Ltac opsig_incl_compute := *)
(*   now (try apply -> opsig_list_incl_remove_fset ; apply opsig_list_incl_expand ; (now repeat (split ; [ repeat ((left ; reflexivity) || (right)) | ]))). *)

(* Lemma valid_subset_fset : *)
(*   forall xs ys I {ct} c, *)
(*     List.incl (xs) (ys) -> *)
(*     ValidCode (fset xs) I c -> *)
(*     @ValidCode (fset ys) I ct c. *)
(* Proof. *)
(*   intros. *)
(*   apply (valid_injectLocations) with (L1 := fset xs). *)
(*   - apply loc_list_incl_fsubset. *)
(*     apply -> loc_list_incl_remove_fset. *)
(*     apply H. *)
(*   - apply H0. *)
(* Qed. *)

(* Lemma valid_subset : *)
(*   forall (xs ys : {fset Location}) I {ct} c, *)
(*     List.incl (xs) (ys) -> *)
(*     ValidCode (xs) I c -> *)
(*     @ValidCode (ys) I ct c. *)
(* Proof. *)
(*   intros. *)
(*   apply (valid_injectLocations) with (L1 := xs). *)
(*   - apply loc_list_incl_fsubset. *)
(*     apply H. *)
(*   - apply H0. *)
(* Qed. *)

Ltac valid_program :=
  apply prog_valid
  || (apply valid_scheme ; try rewrite <- fset.fset0E ; apply prog_valid)
  (* || (eapply (valid_subset_fset) ; [ | apply prog_valid ] ; loc_incl_compute) *).


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

(* Lemma heap_ignore_remove_set_heap : *)
(*   forall {fset} {s₀ s₁ : heap} {ℓ v}, *)
(*   is_true (ssrbool.in_mem ℓ (ssrbool.mem fset)) -> *)
(*   heap_ignore (fset) (s₀, s₁) -> *)
(*   heap_ignore (fset) (set_heap s₀ ℓ v, s₁). *)
(* Proof. *)
(*   intros. *)
(*   unfold heap_ignore. *)
(*   intros. *)
(*   unfold heap_ignore in H0. *)
(*   specialize (H0 ℓ0 ltac:(assumption)). *)
(*   rewrite <- H0. *)
(*   rewrite <- get_heap_set_heap. *)
(*   reflexivity. *)

(*   destruct (@eqtype.eq_op *)
(*           (@eqtype.tag_eqType choice_type_eqType *)
(*                               (fun _ : choice_type => ssrnat.nat_eqType)) ℓ0 ℓ) eqn:ℓ_eq. *)
(*   - apply (ssrbool.elimT eqtype.eqP) in ℓ_eq. *)
(*     subst. *)
(*     exfalso. *)
(*     apply (ssrbool.elimT ssrbool.negP) in H. *)
(*     + apply H. *)
(*     + assumption. *)
(*   - reflexivity. *)
(* Qed. *)

(* Lemma isolate_mem_section : *)
(*   forall (fset : {fset Location}) ℓ  fset_head fset_tail, *)
(*     is_true (ssrbool.in_mem ℓ (ssrbool.mem fset)) -> *)
(*     is_true (ssrbool.in_mem ℓ (ssrbool.mem (fset_head :|: fset :|: fset_tail))). *)
(* Proof. *)
(*   intros. *)
(*   apply fset_compute. apply in_split_fset_cat ; left ; apply in_split_fset_cat ; right. *)
(*   apply fset_compute. apply H. *)
(* Qed. *)

(* Ltac solve_heap_ignore_remove_set_heap := *)
(*   apply (heap_ignore_remove_set_heap) ; [ apply isolate_mem_section ; apply fset_compute ; apply -> in_remove_fset ; cbn ; repeat (left ; reflexivity || right || reflexivity) | assumption ]. *)


Ltac solve_post_from_pre :=
  let H := fresh in
  intros ? ? H
  ; split
  ; [reflexivity | ]
  ; ( assumption
      || (apply restore_set_lhs in H
         ; [ assumption
           | intros ? ?
             (* ; solve_heap_ignore_remove_set_heap *) ] )).

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

Equations prod_to_prod {A B} {L I} (x : both L I (A × B)) : (both L I A * both L I B) :=
  prod_to_prod x :=
  (bind_both x (fun x' => solve_lift (ret_both (fst x'))) ,
   bind_both x (fun x' => solve_lift (ret_both (snd x')))).
Solve All Obligations with intros ; solve_in_fset.
Fail Next Obligation.

(* Equations prod_to_prod {A B} {L I} (x : both L I (A × B)) : (both L I A * both L I B) := *)
(*   prod_to_prod x := *)
(*   (bind_both x (fun x' => solve_lift (ret_both (fst x'))) , *)
(*    bind_both x (fun x' => solve_lift (ret_both (snd x')))). *)
(* Solve All Obligations with intros ; solve_in_fset. *)
(* Fail Next Obligation. *)

Equations let_both {L1 L2 I1 I2 A B} (x : both L1 I1 A) (f : both L1 I1 A -> both L2 I2 B) `{fsubset_loc : is_true (fsubset L1 L2)} `{fsubset_opsig : is_true (fsubset I1 I2)} : both L2 I2 B :=
  let_both x f := f x.

Notation "'letb' x ':=' y 'in' f" :=
  (let_both (* (L1 := _) (L2 := _) (I1 := _) (I2 := _) (A := _) (B := _) *) y (fun x => f) (* (fsubset_loc := _) (fsubset_opsig := _) *)) (* (let_both y (fun x => f)) *) (at level 100, x pattern, right associativity).
Notation "'letb' ''' x ':=' y 'in' f" :=
  (let_both (* (L1 := _) (L2 := _) (I1 := _) (I2 := _) (A := _) (B := _) *)  y (fun x => f) (* (fsubset_loc := _) (fsubset_opsig := _) *)) (* (let_both y (fun x => f)) *) (at level 100, x pattern, right associativity).
(* (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) *)

(* Equations split_both_func {A B : choice_type} {L1 L2 : {fset Location}} {I1 I2} *)
(*           (f : both L1 I1 A -> both L2 I2 B) `{fsubset L1 L2} `{fsubset I1 I2} : (A -> B) * (code L1 I1 A -> code L2 I2 B) := *)
(*   split_both_func f := *)
(*     (fun y : A => is_pure ((fun temp : A => f (solve_lift (ret_both temp))) y), *)
(*      fun y : code L1 I1 A => {code temp ← y ;; is_state (f (solve_lift (ret_both temp))) #with _}). *)
(* Solve All Obligations with intros ; solve_in_fset. *)
(* Next Obligation. *)
(*   intros. *)
(*   ssprove_valid. *)

(*   apply valid_injectLocations with (L1 := L1). apply fsubset2. *)
(*   apply @valid_injectMap with (I1 := I1). apply fsubset3. *)
(*   apply y. *)

(*   apply (f (solve_lift (ret_both x))). *)
(* Qed. *)
(* Fail Next Obligation. *)

(* Equations get_both {L1 I1} (x_loc : Location) `{loc_in : x_loc \in L1} (x : both L1 I1 x_loc) : both L1 I1 x_loc := *)
(*   get_both x_loc x := *)
(*     bind_both x (fun x => *)
(*     {| both_prog := *)
(*         {| *)
(*           is_pure := x ; *)
(*           is_state := (getr x_loc (fun v => ret v)) *)
(*         |}; *)
(*       both_prog_valid := valid_getr_both x_loc x (fun x => solve_lift ret_both x) loc_in *)
(*     |}). *)
(* Solve All Obligations with now intros ; rewrite <- fset0E ; solve_single_fset_fsubset. *)
(* Next Obligation. *)
(*   intros. *)
(*   eapply better_r_get_remind_lhs. *)
(*   2: now apply r_ret. *)
(*   unfold Remembers_lhs. *)
(*   intros. *)
(*   unfold rem_lhs. *)

(*   apply r_get. *)
(*   apply better_r. *)
(*   apply forget_precond. *)
(*   apply (p_eq y). *)
(* Qed. *)
(* Fail Next Obligation. *)

(* Notation "'getb' x 'loc(' ℓ ')' 'in' y" := *)
(*   (solve_lift get_both ℓ x (loc_in := _) y (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'getb'  x 'loc(' ℓ ')'  'in' y"). *)
(* Notation "'getb' ''' x  'loc(' ℓ ')' 'in' y" := *)
(*   (solve_lift get_both ℓ x (loc_in := _) y (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'getb' ''' x  'loc(' ℓ ')' 'in'  y"). *)

Equations assign_mut_both {L1 I1} (x_loc : Location) (x : both L1 I1 x_loc) : both (fset [x_loc] :|: L1) I1 'unit :=
  assign_mut_both x_loc x :=
    bind_both x (fun x =>
    {| both_prog :=
        {|
          is_pure := (tt : 'unit) ;
          is_state := (putr x_loc x (ret (tt : 'unit)))
        |};
      both_prog_valid := @valid_putr_both (fset [x_loc] :|: L1) I1 'unit x_loc x (solve_lift ret_both (tt : 'unit)) _
    |}).
Next Obligation.
  intros.
  normalize_fset.
  solve_single_fset_fsubset.
Qed.
Next Obligation.
  intros.
  normalize_fset.
  solve_single_fset_fsubset.
Qed.
Next Obligation.
  intros.
  rewrite <- fset1E.
  now apply (ssrbool.introT (fsetU1P _ _ _)) ; left.
Qed.
Next Obligation.
  intros.
  apply better_r_put_lhs.
  now apply r_ret.
Qed.
Next Obligation.
  intros.
  normalize_fset.
  solve_single_fset_fsubset.
Qed.
Next Obligation.
  intros.
  normalize_fset.
  solve_single_fset_fsubset.
Qed.
Fail Next Obligation.

Notation "'assignb' x 'loc(' ℓ ')' ':=' y ;" :=
  (solve_lift assign_mut_both ℓ y (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'assignb'  x 'loc(' ℓ ')'  ':=' y ;").
Notation "'assignb' ''' x  'loc(' ℓ ')' ':=' y ;" :=
  (solve_lift assign_mut_both ℓ y (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'assignb' ''' x  'loc(' ℓ ')' ':='  y  ;").

Equations let_mut_both {L1 L2 I1 I2 B} (x_loc : Location) `{loc_in : x_loc \in L2} (x : both L1 I1 x_loc) (f : both (fset [x_loc] :|: L1) I1 x_loc -> both L2 I2 B) `{fsubset_loc : is_true (fsubset L1 L2)} `{fsubset_opsig : is_true (fsubset I1 I2)} : both L2 I2 B :=
  let_mut_both x_loc x f :=
  bind_both x (fun y =>
   {| both_prog :=
     {|
       is_pure := is_pure (f (solve_lift (ret_both y))) ;
       is_state := putr x_loc y (getr x_loc (fun y => is_state (f (solve_lift (ret_both y)))))
     |};
       both_prog_valid := (@valid_putr_getr_both L2 I2 B x_loc y (fun x => f (solve_lift (ret_both x))) loc_in (fun x => both_prog_valid (f (solve_lift (ret_both x)))))
   |}).
Solve All Obligations with intros ; solve_in_fset.
Next Obligation.
  intros.
  apply better_r_put_lhs.
  apply getr_set_lhs.
  apply forget_precond.
  apply f.
Qed.
Fail Next Obligation.

Notation "'letb' x 'loc(' ℓ ')' ':=' y 'in' f" :=
  (let_mut_both ℓ y (fun x => f) (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'letb'  x 'loc(' ℓ ')'  ':=' y  'in' '//' f").
Notation "'letb' ''' x  'loc(' ℓ ')' ':=' y 'in' f" :=
  (let_mut_both ℓ y (fun x => f) (* (fsubset_loc := _) (fsubset_opsig := _) (loc_in := _) *)) (at level 100, x pattern, right associativity, format "'letb' ''' x  'loc(' ℓ ')' ':='  y  'in' '//' f").

Fixpoint split_type (F : choice_type -> Type) (A : choice_type) : Type :=
  match A with
  | C × D => split_type F C * split_type F D
  | _ => F A
  end.

Fixpoint split_both {L I A} (x : both L I A) : (split_type (both L I) A) :=
   match A as c return (both L I c -> split_type (both L I) c) with
   | _ × _ => fun y => (split_both (fst (prod_to_prod y)) , split_both (snd (prod_to_prod y)))
   | _ => fun y : both L I _ => y
   end x.

Fixpoint unsplit_both {L I A} (s : split_type (both L I) A) : both L I A :=
  match A as c return (split_type (both L I) c -> both L I c) with
  | _ × _ =>
      fun y => prod_both0 ( unsplit_both (fst y)) ((unsplit_both (snd y)))
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
Eval simpl in prod_to_prod_n_ty 2 (both fset0 fset0) ('nat × 'bool).

(* TODO: Currently duplicates code, due to prod_to_prod, should only evaluate and project the result ! *)
Fixpoint prod_to_prod_n {L I A} (n : nat) (x : both L I A) : prod_to_prod_n_ty n  (both L I) A :=
  match n as m return prod_to_prod_n_ty m (both L I) A with
  | O => x
  | S n' =>
      match A as B return both L I B -> prod_to_prod_n_ty (S n') (both L I) B with
      | B × C => fun y => (prod_to_prod_n n' (fst (prod_to_prod y)), snd (prod_to_prod y))
      | _ => fun y => y
      end x
  end.

Equations lift_n {L1 L2 I1 I2 A B} (n : nat) {fsubset_loc : is_true (fsubset L1 L2)} {fsubset_opsig : is_true (fsubset I1 I2)} (z : both L1 I1 A) (f : prod_to_prod_n_ty n (both L1 I1) A -> both L2 I2 B) : both L2 I2 B :=
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

(* Notation "'letb' ' '(' a ',' b ')' ':=' z 'in' f" := *)
(*   (let '(a,b) := prod_to_prod_n 1 z in *)
(*    f) (at level 100). *)

(* Notation "'letb' ' '(' a ',' b ',' c ')' ':=' z 'in' f" := *)
(*   (let '(a, b, c) := prod_to_prod_n 2 z in *)
(*    f) (at level 100). *)

(* Notation "'letb' ' '(' a ',' b ',' c ',' d ')' ':=' z 'in' f" := *)
(*   (  let '(a, b, c, d) := prod_to_prod_n 3 z in *)
(*      f) (at level 100). *)

(* Locate prod_b( _ , _ ). *)


Equations let_both0 {A B} (x : both (fset []) (fset []) A) (f : both (fset []) (fset []) A -> both (fset []) (fset []) B) : both (fset []) (fset []) B :=
  let_both0 x f := f x.

Notation "'letb0' x ':=' y 'in' f" :=
  (let_both0 (* (L1 := _) (L2 := _) (I1 := _) (I2 := _) (A := _) (B := _) *) y (fun x => f)) (* (let_both y (fun x => f)) *) (at level 100, x pattern, right associativity).
Notation "'letb0' ''' x ':=' y 'in' f" :=
  (let_both0 (* (L1 := _) (L2 := _) (I1 := _) (I2 := _) (A := _) (B := _) *)  y (fun x => f)) (* (let_both y (fun x => f)) *) (at level 100, x pattern, right associativity).
(* (lift_scope (H_loc_incl := _) (H_opsig_incl := _) y) *)

Notation "'letb0' ' '(' a ',' b ')' ':=' z 'in' f" :=
  (lift_n 1 z (fun '(a, b) => f))
    (at level 100).

Notation "'letb0' ' '(' a ',' b ',' c ')' ':=' z 'in' f" :=
  (lift_n 2 z (fun '(a, b, c) => f))
    (at level 100).

Notation "'letb0' ' '(' a ',' b ',' c ',' d ')' ':=' z 'in' f" :=
  (lift_n 3 z (fun '(a, b, c, d) => f))
    (at level 100).
