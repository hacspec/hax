Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".
(*** Integers *)
From Coq Require Import ZArith List.
Import ListNotations.
(* Require Import IntTypes. *)

(* Require Import MachineIntegers. *) From compcert Require Import Integers.
From Coqprime Require GZnZ.

Require Import Lia.

Declare Scope hacspec_scope.

Set Default Goal Selector "!".

(*** Positive util *)

Fixpoint binary_representation_pre (n : nat) {struct n}: positive :=
  match n with
  | O => 1
  | S O => 1
  | S n => Pos.succ (binary_representation_pre n)
  end%positive.
Definition binary_representation (n : nat) `(n <> O) := binary_representation_pre n.

Theorem positive_is_succs : forall n, forall (H : n <> O) (K : S n <> O),
    @binary_representation (S n) K = Pos.succ (@binary_representation n H).
Proof. induction n ; [contradiction | reflexivity]. Qed.

(* Conversion of positive to binary Int8.representation *)
Theorem positive_to_positive_succs : forall p, binary_representation (Pos.to_nat p) (Nat.neq_sym _ _ (Nat.lt_neq _ _ (Pos2Nat.is_pos p))) = p.
Proof.
  intros p.
  generalize dependent (Nat.neq_sym 0 (Pos.to_nat p) (Nat.lt_neq 0 (Pos.to_nat p) (Pos2Nat.is_pos p))).

  destruct Pos.to_nat eqn:ptno.
  - contradiction.
  - generalize dependent p.
    induction n ; intros.
    + cbn.
      apply Pos2Nat.inj.
      symmetry.
      apply ptno.
    + rewrite positive_is_succs with (H := Nat.neq_succ_0 n).
      rewrite IHn with (p := Pos.of_nat (S n)).
      * rewrite <- Nat2Pos.inj_succ by apply Nat.neq_succ_0.
        rewrite <- ptno.
        apply Pos2Nat.id.
      * apply Nat2Pos.id.
        apply Nat.neq_succ_0.
Qed.

(*** Hacspec Integers *)

Class MyAdd (A : Type) := myadd : A -> A -> A.
Infix ".+" := (myadd) (at level 77) : hacspec_scope.

Module HacspecIntegers (WS : WORDSIZE).
  Include (Make WS).
  (**** Public integers *)

  Definition pub (n : Z) : int := repr n.

  (**** Operations *)

  (* Should maybe use size of s instead? *)
  Definition rotate_left (u: int) (s: int) : int := rol u s.

  Definition pub_uint_wrapping_add (x y: int) : int := add x y.

  Definition shift_left_ (i : int) (j : int) :=
    shl i j.

  Definition shift_right_ (i : int) (j : int) :=
    shr i j.

  Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
  Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

  Instance MyAddInstance : MyAdd int := add.
  
  Infix "%%" := Z.rem (at level 40, left associativity) : Z_scope.
  (* Infix ".+" := (add) (at level 77) : hacspec_scope. *)
  Infix ".-" := (sub) (at level 77) : hacspec_scope.
  Notation "-" := (neg) (at level 77) : hacspec_scope.
  Infix ".*" := (mul) (at level 77) : hacspec_scope.
  Infix "./" := (divs) (at level 77) : hacspec_scope.
  Infix ".%" := (mods) (at level 77) : hacspec_scope.
  Infix ".^" := (xor) (at level 77) : hacspec_scope.
  Infix ".&" := (and) (at level 77) : hacspec_scope.
  Infix ".|" := (or) (at level 77) : hacspec_scope.
  Infix "==" := (eq) (at level 32) : hacspec_scope.
  (* Definition one := (@one WORDSIZE32). *)
  (* Definition zero := (@zero WORDSIZE32). *)
  Notation "A × B" := (prod A B) (at level 79, left associativity) : hacspec_scope.

  (*** Uint size util *)

  (* If a natural number is in bound then a smaller natural number is still in bound *)
  Lemma range_of_nat_succ :
    forall i, (Z.pred 0 < Z.of_nat (S i) < modulus)%Z -> (Z.pred 0 < Z.of_nat i < modulus)%Z.
  Proof. lia. Qed.

  (* Conversion to equivalent bound *)
  Lemma modulus_range_helper :
    forall i, (Z.pred 0 < i < modulus)%Z -> (0 <= i <= max_unsigned)%Z.
  Proof. unfold max_unsigned. lia. Qed.

  Definition unsigned_repr_alt (a : Z) `((Z.pred 0 < a < modulus)%Z) : unsigned (repr a) = a :=
    unsigned_repr a (modulus_range_helper a H).

  Theorem zero_always_modulus  : (Z.pred 0 < 0 < modulus)%Z.
  Proof. easy. Qed.

  (* any uint_size can be .represented as a natural number and a bound *)
  (* this is easier for proofs, however less efficient for computation *)
  (* as Z uses a binary .representation *)
  Theorem int_as_nat :
    forall (us: int),
      { n : nat |
        us = repr (Z.of_nat n) /\ (Z.pred 0 < Z.of_nat n < modulus)%Z}.
  Proof.
    destruct us as [intval intrange].
    exists (Z.to_nat intval).
    rewrite Z2Nat.id by (apply Z.lt_pred_le ; apply intrange).

    split.
    - apply mkint_eq.
      rewrite Z_mod_modulus_eq.
      rewrite Z.mod_small.
      + reflexivity.
      + lia.
    - apply intrange.
  Qed.

  (* destruct int as you would a natural number *)
  Definition destruct_int_as_nat  (a : int) : forall (P : int -> Prop),
    forall (zero_case : P (repr 0)),
    forall (succ_case : forall (n : nat), (Z.pred 0 < Z.of_nat n < modulus)%Z -> P (repr (Z.of_nat n))),
      P a.
  Proof.
    intros.
    destruct (int_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    destruct n.
    - apply zero_case.
    - apply succ_case.
      apply yb.
  Qed.

  Ltac destruct_int_as_nat a :=
    generalize dependent a ;
    intros a ;
    apply (destruct_int_as_nat a) ; [ pose proof (@unsigned_repr_alt 0 zero_always_modulus) | let n := fresh in let H := fresh in intros n H ; pose proof (@unsigned_repr_alt _ H)] ; intros.

  (* induction for int as you would do for a natural number *)
  Definition induction_int_as_nat :
    forall (P : int -> Prop),
      (P (repr 0)) ->
      (forall n,
          (Z.pred 0 < Z.succ (Z.of_nat n) < @modulus)%Z ->
          P (repr (Z.of_nat n)) ->
          P (repr (Z.succ (Z.of_nat n)))) ->
      forall (a : int), P a.
  Proof.
    intros P H_zero H_ind a.
    destruct (int_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    induction n.
    - apply H_zero.
    - rewrite Nat2Z.inj_succ.
      apply H_ind.
      + rewrite <- Nat2Z.inj_succ.
        apply yb.
      + apply IHn.
        lia.
  Qed.

  Ltac induction_int_as_nat var :=
    generalize dependent var ;
    intros var ;
    apply induction_int_as_nat with (a := var) ; [ pose proof (@unsigned_repr_alt 0 zero_always_modulus) | let n := fresh in let IH := fresh in intros n IH ; pose proof (@unsigned_repr_alt _ IH)] ; intros.

  (* conversion of usize to positive or zero and the respective bound *)
  Theorem int_as_positive :
    forall (us: int),
      { pu : unit + positive |
        match pu with inl u => us = repr Z0 | inr p => us = repr (Z.pos p) /\ (Z.pred 0 < Z.pos p < @modulus)%Z end
      }.
  Proof.
    destruct us as [intval intrange].
    destruct intval.
    - exists (inl tt). apply mkint_eq. reflexivity.
    - exists (inr p).
      split.
      + apply mkint_eq.
        rewrite Z_mod_modulus_eq.
        symmetry.
        apply Zmod_small.
        lia.
      + apply intrange.
    - exfalso.
      lia.
  Defined.

  (* destruction of int as positive *)
  Definition destruct_int_as_positive  (a : int) : forall (P : int -> Prop),
      (P (repr 0)) ->
      (forall b, (Z.pred 0 < Z.pos b < @modulus)%Z -> P (repr (Z.pos b))) ->
      P a.
  Proof.
    intros P H_zero H_succ.
    destruct (int_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
    - apply H_zero.
    - apply H_succ.
      apply yb.
  Qed.

  Ltac destruct_int_as_positive a :=
    generalize dependent a ;
    intros a ;
    apply (destruct_int_as_positive a) ; intros.

  (* induction of int as positive *)
  Definition induction_int_as_positive :
    forall (P : int -> Prop),
      (P (repr 0)) ->
      (P (repr 1)) ->
      (forall b,
          (Z.pred 0 < Z.succ (Z.pos b) < @modulus)%Z ->
          P (repr (Z.pos b)) ->
          P (repr (Z.succ (Z.pos b)))) ->
      forall (a : int), P a.
  Proof.
    intros P H_zero H_one H_ind a.

    destruct (int_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
    - apply H_zero.
    - pose proof (pos_succ_b := positive_to_positive_succs b)
      ; symmetry in pos_succ_b
      ; rewrite pos_succ_b in *
      ; clear pos_succ_b.

      generalize dependent (Nat.neq_sym 0 (Pos.to_nat b) (Nat.lt_neq 0 (Pos.to_nat b) (Pos2Nat.is_pos b))).

      induction (Pos.to_nat b).
      + contradiction.
      + intros n_neq yb.
        destruct n.
        * apply H_one.
        * rewrite (positive_is_succs _  (Nat.neq_succ_0 n) n_neq) in *.
          rewrite Pos2Z.inj_succ in *.
          apply H_ind.
          -- apply yb.
          -- apply IHn.
             lia.
  Qed.

  Ltac induction_int_as_positive var :=
    generalize dependent var ;
    intros var ;
    apply induction_int_as_positive with (a := var) ; intros ; [ | | ].

End HacspecIntegers.

Module Wordsize_16 : WORDSIZE.
  Definition wordsize := 16.
  Theorem wordsize_not_zero : wordsize <> 0%nat. easy. Qed.
End Wordsize_16.

Module Wordsize_128 : WORDSIZE.
  Definition wordsize := 128.
  Theorem wordsize_not_zero : wordsize <> 0%nat. easy. Qed.
End Wordsize_128.

Module Int8 := HacspecIntegers Wordsize_8.
Module Int16 := HacspecIntegers Wordsize_16.
Module Int32 := HacspecIntegers Wordsize_32.
Module Int64 := HacspecIntegers Wordsize_64.
Module Int128 := HacspecIntegers Wordsize_128.

Import Int128. Export Int128.
Import Int64. Export Int64.
Import Int32. Export Int32.
Import Int16. Export Int16.
Import Int8. Export Int8.

Definition int8 := Int8.int.
Definition int16 := Int16.int.
Definition int32 := Int32.int.
Definition int64 := Int64.int.
Definition int128 := Int128.int.

(* Instance int8_add : MyAdd int8 := Int8.add. *)
(* Instance int16_add : MyAdd int16 := Int16.add. *)
(* Instance int32_add : MyAdd int32 := Int32.add. *)
(* Instance int64_add : MyAdd int64 := Int64.add. *)
(* Instance int128_add : MyAdd int128 := Int128.add. *)

(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)
Definition uint8 := int8.
Definition uint16 := int16.
Definition uint32 := int32.
Definition uint64 := int64.
Definition uint128 := int128.

Definition uint_size := int32.
Definition int_size := int32.

Axiom declassify_usize_from_uint8 : uint8 -> uint_size.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizable (A : Type) := {
  usize : A -> uint_size;
  from_uint_size : uint_size -> A;
}.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Global Instance nat_uint_sizable : UInt_sizable nat := {
  usize n := Int32.repr (Z.of_nat n);
  from_uint_size n := Z.to_nat (Int32.unsigned n);
}.

Global Instance N_uint_sizable : UInt_sizable N := {
  usize n := Int32.repr (Z.of_N n);
  from_uint_size n := Z.to_N (Int32.unsigned n);
}.

Global Instance Z_uint_sizable : UInt_sizable Z := {
  usize n := Int32.repr n;
  from_uint_size n := Int32.unsigned n;
}.


(* Same, but for int_size *)
Class Int_sizable (A : Type) := {
  isize : A -> int_size;
  from_int_size : int_size -> A;
}.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizable : Int_sizable nat := {
  isize n := Int32.repr (Z.of_nat n);
  from_int_size n := Z.to_nat (Int32.signed n);
}.

Global Instance N_Int_sizable : Int_sizable N := {
  isize n := Int32.repr (Z.of_N n);
  from_int_size n := Z.to_N (Int32.signed n);
}.

Global Instance Z_Int_sizable : Int_sizable Z := {
  isize n := Int32.repr n;
  from_int_size n := Int32.signed n;
}.

Notation secret := id.
