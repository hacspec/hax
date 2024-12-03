(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.

(* From Core Require Import Core. *)

From Core Require Import Core_Base_Spec.
Export Core_Base_Spec.

From Core Require Import Core_Base_Pos.
Export Core_Base_Pos.

From Core Require Import Core_Clone (t_Clone).
Export Core_Clone (t_Clone).

From Core Require Import Core_Cmp.
Export Core_Cmp.

From Core Require Import Core_Marker (t_Sized).
Export Core_Marker (t_Sized).

From Core Require Import Core_Panicking.
Export Core_Panicking.

Definition hd__panic_cold_explicit '(_ : unit) `{HFalse : t_Never} : t_Never :=
  panic_explicit (tt) HFalse.

Definition set_index__set_index_unary__panic_cold_explicit '(_ : unit) `{HFalse : t_Never} : t_Never :=
  panic_explicit (tt) HFalse.

Definition is_empty `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) : bool :=
  match match_list (s) with
  | LIST_NIL =>
    true
  | LIST_CONS (_) (_) =>
    false
  end.

Definition hd `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) `{Hpre : negb (is_empty (s)) = true} : v_T :=
  match match_list (s) as s return negb (is_empty (s)) = true -> _ with
  | LIST_NIL =>
    fun HFalse => never_to_any (hd__panic_cold_explicit (tt) (False_rect _ (Bool.diff_false_true HFalse)))
  | LIST_CONS (hd) (_) =>
    fun _ => hd
  end Hpre.

Definition tl `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) `{Hpre : negb (is_empty (s)) = true} : t_Seq ((v_T)) :=
  match match_list (s) with
  | LIST_NIL =>
    nil (* (tt) *)
  | LIST_CONS (_) (tl) =>
    tl
  end.

Fixpoint eq_inner `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} `{t_PartialEq (v_T) (v_T)} (s : t_Seq ((v_T))) (other : t_Seq ((v_T))) : bool :=
  match match_list (Clone_f_clone (s)) with
  | LIST_NIL =>
    is_empty (Clone_f_clone (other))
  | LIST_CONS (x) (xs) =>
    match match_list (Clone_f_clone (other)) with
    | LIST_NIL =>
      false
    | LIST_CONS (y) (ys) =>
      andb (PartialEq_f_eq (x) (y)) (eq_inner (xs) (ys))
    end
  end.

Instance t_PartialEq_126322860 `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} `{t_PartialEq (v_T) (v_T)} : t_PartialEq ((t_Seq ((v_T)))) ((t_Seq ((v_T)))) :=
  {
    PartialEq_f_eq := fun  (self : t_Seq ((v_T))) (other : t_Seq ((v_T)))=>
      eq_inner (Clone_f_clone (self)) (Clone_f_clone (other));
    PartialEq_f_ne := fun  (self : t_Seq ((v_T))) (other : t_Seq ((v_T)))=>
      negb (eq_inner (Clone_f_clone (self)) (Clone_f_clone (other)));
  }.

Fixpoint len__len_unary `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) : t_Unary :=
  match match_list (s) with
  | LIST_NIL =>
    unary_from_int(v_HaxInt_ZERO)
  | LIST_CONS (_) (tl) =>
    succ (len__len_unary (tl))
  end.

Definition len `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) : t_HaxInt :=
  unary_to_int(len__len_unary(s)).

Lemma positive_cmp_is_spec :
  forall p q, match positive_cmp p q with | Ordering_Less => Lt | Ordering_Equal => Eq | Ordering_Greater => Gt end = (p ?= q)%positive.
  {
    clear.
    intros.

    unfold positive_cmp.
    unfold "?="%positive.

    set (Ordering_Equal).
    pose (match Eq with | Lt => Ordering_Less | Gt => Ordering_Greater | Eq => Ordering_Equal end).
    replace t with t0 by reflexivity.
    clear t.

    assert (forall c p q, c <> Eq -> Pos.compare_cont c p q <> Eq).
    {
      clear ; intros.
      generalize dependent c.
      generalize dependent q.
      induction p ; intros ; destruct q, c ; (easy || now apply IHp).
    }

    assert (forall c p q, c <> Ordering_Equal -> positive_cmp__cmp_binary_cont p q c <> Ordering_Equal).
    {
      clear ; intros.
      generalize dependent c.
      generalize dependent q.
      induction p ; intros ; destruct q, c ; (easy || now apply IHp).
    }

    subst t0.
    set Eq.
    generalize dependent c.
    generalize dependent q.
    induction p ; intros.
    - destruct q.
      + apply IHp.
      + simpl.
        rewrite <- IHp.
        destruct positive_cmp__cmp_binary_cont eqn:ov.
        * reflexivity.
        * exfalso. refine (H0 _ p q _ ov). easy.
        * reflexivity.
      + reflexivity.
    - destruct q.
      + simpl.
        rewrite <- IHp.
        destruct positive_cmp__cmp_binary_cont eqn:ov.
        * reflexivity.
        * exfalso. refine (H0 _ p q _ ov). easy.
        * reflexivity.
      + apply IHp.
      + reflexivity.
    - now destruct q, c.
  }
Qed.

Lemma haxint_lt_is_spec : forall x y, haxint_lt x y = N.ltb x y.
  {
    intros.
    destruct x as [ | p], y as [ | q].
    - easy.
    - easy.
    - easy.
    - unfold haxint_lt.
      unfold haxint_cmp.
      simpl.

      unfold N.ltb.
      simpl.

      rewrite <- positive_cmp_is_spec.

      now destruct (positive_cmp).
  }
Qed.

Program Fixpoint get_index__get_index_unary `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (l : t_Seq ((v_T))) (i : t_Unary) `{Hpre : haxint_lt(unary_to_int i) (len l) = true} : v_T :=
  match match_unary (i) with
  | UNARY_ZERO =>
    hd (Hpre := Hpre) (l)
  | UNARY_SUCC (n) =>
    get_index__get_index_unary (tl (Hpre := _) (l)) (n)
  end.
Next Obligation.
  unfold match_unary in Heq_anonymous.
  subst.
  now destruct l.
Qed.
Next Obligation.
  unfold match_unary in Heq_anonymous.
  subst.
  now destruct l.
Qed.
Next Obligation.
  unfold match_unary in Heq_anonymous.
  subst.

  destruct l.
  - easy.
  - simpl.

    rewrite haxint_lt_is_spec.
    epose Hpre.
    rewrite haxint_lt_is_spec in e.

    apply N.ltb_lt.
    apply N.ltb_lt in e.
    apply N.succ_lt_mono.
    unfold len ; rewrite <- !Nnat.Nat2N.inj_succ.
    apply e.
Qed.
Fail Next Obligation.

Definition get_index `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) (i : t_HaxInt) {Hpre : haxint_lt (i) (len s) = true} : v_T :=
  get_index__get_index_unary (Hpre := ltac:(now rewrite Nnat.N2Nat.id)) (s) (unary_from_int (i)).

Fixpoint repeat__repeat_unary `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (n : t_Unary) (v : v_T) : t_Seq ((v_T)) :=
  match match_unary (n) with
  | UNARY_ZERO =>
    nil (* (tt) *)
  | UNARY_SUCC (m) =>
    cons (repeat__repeat_unary (m) (Clone_f_clone (v))) v
  end.

Definition repeat `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (n : t_HaxInt) (v : v_T) : t_Seq ((v_T)) :=
  repeat__repeat_unary (unary_from_int (n)) (v).

Fixpoint rev__rev_accum `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) (accum : t_Seq ((v_T))) : t_Seq ((v_T)) :=
  match match_list (s) with
  | LIST_NIL =>
    accum
  | LIST_CONS (hd) (tl) =>
    rev__rev_accum (tl) (cons (accum) (hd))
  end.

Definition rev `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) : t_Seq ((v_T)) :=
  rev__rev_accum (s) (nil (* (tt) *)).

Program Fixpoint set_index__set_index_unary `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (x : t_Seq ((v_T))) (i : t_Unary) (v : v_T) `{Hpre : haxint_lt(unary_to_int i) (len x) = true} : t_Seq ((v_T)) :=
  match match_list (x) with
  | LIST_NIL =>
    never_to_any (set_index__set_index_unary__panic_cold_explicit (tt) _)
  | LIST_CONS (hd) (tl) =>
    match match_unary (i) with
    | UNARY_ZERO =>
      cons (tl) (v)
    | UNARY_SUCC (n) =>
      cons (set_index__set_index_unary (tl) (n) (v)) (hd)
    end
  end.
Next Obligation.
  unfold match_list in Heq_anonymous.
  subst.
  now destruct i.
Qed.
Next Obligation.
  unfold match_unary in Heq_anonymous.
  subst.
  unfold match_list in Heq_anonymous0.
  subst.


  rewrite haxint_lt_is_spec.
  rewrite haxint_lt_is_spec in Hpre.

  apply N.ltb_lt.
  apply N.ltb_lt in Hpre.
  apply N.succ_lt_mono.
  unfold len ; rewrite <- !Nnat.Nat2N.inj_succ.
  apply Hpre.
Qed.
Fail Next Obligation.

Definition set_index `{v_T : Type} `{t_Sized (v_T)} `{t_Clone (v_T)} (s : t_Seq ((v_T))) (i : t_HaxInt) (v : v_T) `{haxint_lt (i) (len (s)) = true} : t_Seq ((v_T)) :=
  set_index__set_index_unary (s)  (Hpre := ltac:(now rewrite Nnat.N2Nat.id)) (unary_from_int (i)) (v).
