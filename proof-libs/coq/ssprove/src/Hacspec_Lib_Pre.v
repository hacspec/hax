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

Require Import ChoiceEquality.

From mathcomp Require Import ssrZ word.
(* From Jasmin Require Import word. *)
From Crypt Require Import jasmin_word.


From Coq Require Import ZArith List.
Import ListNotations.

(*****************************************************)
(*   Implementation of all Hacspec library functions *)
(* for choice_type types.                         *)
(*****************************************************)

(*** Integers *)
Declare Scope hacspec_scope.

Open Scope list_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.

Require Import Hacspec_Lib_Comparable.

Import choice.Choice.Exports.

(* Section IntType. *)

  Notation int := chWord.

  Notation unsigned := wunsigned.
  Notation signed := wsigned.
  Notation repr := (fun WS x => wrepr WS x : int WS).

  Notation rol := (fun u s => wrol u (unsigned s)).
  Notation ror := (fun u s => wror u (unsigned s)).

  Notation int8 := (@int U8).
  Notation int16 := (@int U16).
  Notation int32 := (@int U32).
  Notation int64 := (@int U64).
  Notation int128 := (@int U128).

  Notation int_modi := wmodi.
  Definition int_add {WS} : @int WS -> @int WS -> @int WS := @add_word WS.
  Definition int_sub {WS} : @int WS -> @int WS -> @int WS := @sub_word WS.
  Definition int_opp {WS} : @int WS -> @int WS := @opp_word WS.
  Definition int_mul {WS} : @int WS -> @int WS -> @int WS := @mul_word WS.
  Notation int_div := wdiv.
  Notation int_mod := wmod.
  Notation int_xor := wxor.
  Notation int_and := wand.
  Notation int_or := wor.

  Definition int_not {WS : wsize} : (@int WS) -> (@int WS) := wnot.

  Definition zero {WS : wsize} : ((@int WS)) := @word0 WS.
  Definition one {WS : wsize} : ((@int WS)) := @word1 (pred WS).

  Lemma add_zero_l : forall {WS : wsize} n, int_add (@zero WS) n = n.
  Proof.
    intros.
    apply add0w.
  Defined.

  Lemma add_one_l : forall {WS : wsize} n, int_add one (repr WS n) = repr _ (Z.succ n).
  Proof.
    intros.
    setoid_rewrite wrepr_add.
    rewrite urepr_word.
    replace (urepr (@one WS)) with 1%Z by reflexivity.
    replace toword  with urepr by reflexivity.
    setoid_rewrite ureprK.
    rewrite ssralg.GRing.addrC.
    now setoid_rewrite mkword1E.
  Defined.

  Lemma repr0_is_zero : forall {WS : wsize}, repr WS 0%Z = zero.
  Proof.
    intros.
    now rewrite wrepr0.
  Qed.

  Lemma add_repr : forall {WS : wsize} (n m : Z), int_add (repr WS n) (repr WS m) = (repr WS (n + m)%Z).
  Proof. intros ; now rewrite wrepr_add. Qed.

(* End IntType. *)

Axiom secret : forall {WS : wsize},  ((@int WS)) -> ((@int WS)).

Infix ".%%" := int_modi (at level 40, left associativity) : Z_scope.
Infix ".+" := int_add (at level 77) : hacspec_scope.
Infix ".-" := int_sub (at level 77) : hacspec_scope.
Notation "-" := int_opp (at level 77) : hacspec_scope.
Infix ".*" := int_mul (at level 77) : hacspec_scope.
Infix "./" := int_div (at level 77) : hacspec_scope.
Infix ".%" := int_mod (at level 77) : hacspec_scope.
Infix ".^" := int_xor (at level 77) : hacspec_scope.
Infix ".&" := int_and (at level 77) : hacspec_scope.
Infix ".|" := int_or (at level 77) : hacspec_scope.

Notation "'not'" := int_not (at level 77) : hacspec_scope.

(* Comparisons, boolean equality, and notation *)

Global Program Instance nat_eqdec : EqDec nat := {
    eqb := Nat.eqb;
    eqb_leibniz := Nat.eqb_eq ;
  }.

Global Instance nat_comparable : Comparable nat := {
    ltb := Nat.ltb;
    leb := Nat.leb;
    gtb a b := Nat.ltb b a;
    geb a b := Nat.leb b a;
  }.

Global Instance N_eqdec : EqDec N := {
    eqb := N.eqb;
    eqb_leibniz := N.eqb_eq ;
  }.

Global Instance N_comparable : Comparable N := {
    ltb := N.ltb;
    leb := N.leb;
    gtb a b := N.ltb b a;
    geb a b := N.leb b a;
  }.

Global Instance Z_eqdec : EqDec Z := {
    eqb := Z.eqb;
    eqb_leibniz := Z.eqb_eq ;
  }.

Global Instance Z_comparable : Comparable Z := {
    ltb := Z.ltb;
    leb := Z.leb;
    gtb a b := Z.ltb b a;
    geb a b := Z.leb b a;
  }.

Lemma int_eqb_eq : forall {WS : wsize} (a b : (@int WS)), eqtype.eq_op a b = true <-> a = b.
Proof.
  symmetry ; exact (ssrbool.rwP (@eqtype.eqP _ a b)).
Qed.

Global Instance int_eqdec `{WS : wsize}: EqDec ((@int WS)) := {
    eqb := eqtype.eq_op;
    eqb_leibniz := int_eqb_eq ;
  }.

Global Instance int_comparable `{WS : wsize} : Comparable ((@int WS)) :=
  eq_dec_lt_Comparable (wlt Unsigned).

Axiom uint8_declassify : int8 -> int8.
Axiom int8_declassify : int8 -> int8.
Axiom uint16_declassify : int16 -> int16.
Axiom int16_declassify : int16 -> int16.
Axiom uint32_declassify : int32 -> int32.
Axiom int32_declassify : int32 -> int32.
Axiom uint64_declassify : int64 -> int64.
Axiom int64_declassify : int64 -> int64.
Axiom uint128_declassify : int128 -> int128.
Axiom int128_declassify : int128 -> int128.

Axiom uint8_classify : int8 -> int8.
Axiom int8_classify : int8 -> int8.
Axiom uint16_classify : int16 -> int16.
Axiom int16_classify : int16 -> int16.
Axiom uint32_classify : int32 -> int32.
Axiom int32_classify : int32 -> int32.
Axiom uint64_classify : int64 -> int64.
Axiom int64_classify : int64 -> int64.
Axiom uint128_classify : int128 -> int128.
Axiom int128_classify : int128 -> int128.


(* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
 *)

Notation uint8 := int8.
Notation uint32 := int32.
Notation uint64 := int64.
Notation uint128 := int128.

Definition uint_size : choice_type := int32.
Definition int_size : choice_type := int32.

Axiom declassify_usize_from_uint8 : uint8 -> uint_size.
Axiom declassify_u32_from_uint32 : uint32 -> uint32.

(* Represents any type that can be converted to uint_size and back *)
Class UInt_sizeable (A : Type) := {
    usize : A -> uint_size;
    from_uint_size :> uint_size -> A;
  }.
Arguments usize {_} {_}.
Arguments from_uint_size {_} {_}.

Definition from_uint_size_int (x : uint_size) : @int U32 := x.
Coercion from_uint_size_int : choice.Choice.sort >-> choice.Choice.sort.

Global Instance nat_uint_sizeable : UInt_sizeable nat := {
    usize n := repr _ (Z.of_nat n);
    from_uint_size n := Z.to_nat (unsigned n);
  }.

Global Instance N_uint_sizeable : UInt_sizeable N := {
    usize n := repr _ (Z.of_N n);
    from_uint_size n := Z.to_N (unsigned n);
  }.

Global Instance Z_uint_sizeable : UInt_sizeable Z := {
    usize n := repr _ n;
    from_uint_size n := unsigned n;
  }.


(* Same, but for int_size *)
Class Int_sizeable (A : Type) := {
    isize : A -> int_size;
    from_int_size : int_size -> A;
  }.

Arguments isize {_} {_}.
Arguments from_int_size {_} {_}.

Global Instance nat_Int_sizeable : Int_sizeable nat := {
    isize n := repr _ (Z.of_nat n);
    from_int_size n := Z.to_nat (signed n);
  }.

Global Instance N_Int_sizeable : Int_sizeable N := {
    isize n := repr _ (Z.of_N n);
    from_int_size n := Z.to_N (signed n);
  }.

Global Instance Z_Int_sizeable : Int_sizeable Z := {
    isize n := repr _ n;
    from_int_size n := signed n;
  }.

(**** Public integers *)

Definition pub_u8 (n : uint_size) : int8 := repr _ (unsigned n).
Definition pub_i8 (n : uint_size) : int8 := repr _ (unsigned n).
Definition pub_u16 (n : uint_size) : int16 := repr _ (unsigned n).
Definition pub_i16 (n : uint_size) : int16 := repr _ (unsigned n).
Definition pub_u32 (n : uint_size) : int32 := repr _ (unsigned n).
Definition pub_i32 (n : uint_size) : int32 := repr _ (unsigned n).
Definition pub_u64 (n : uint_size) : int64 := repr _ (unsigned n).
Definition pub_i64 (n : uint_size) : int64 := repr _ (unsigned n).
Definition pub_u128 (n : uint_size) : int128 := repr _ (unsigned n).
Definition pub_i128 (n : uint_size) : int128 := repr _ (unsigned n).

(**** Operations *)

Definition uint8_rotate_left (u: int8) (s: int8) : int8 := rol u s.

Definition uint8_rotate_right (u: int8) (s: int8) : int8 := ror u s.

Definition uint16_rotate_left (u: int16) (s: int16) : int16 :=
  rol u s.

Definition uint16_rotate_right (u: int16) (s: int16) : int16 :=
  ror u s.

Definition uint32_rotate_left (u: int32) (s: int32) : int32 :=
  rol u s.

Definition uint32_rotate_right (u: int32) (s: int32) : int32 :=
  ror u s.

Definition uint64_rotate_left (u: int64) (s: int64) : int64 :=
  rol u s.

Definition uint64_rotate_right (u: int64) (s: int64) : int64 :=
  ror u s.

Definition uint128_rotate_left (u: int128) (s: int128) : int128 :=
  rol u s.

Definition uint128_rotate_right (u: int128) (s: int128) : int128 :=
  ror u s.

Definition usize_shift_right (u: uint_size) (s: int32) : uint_size :=
  wshr u (unsigned (@repr U32 (from_uint_size s))).
Infix "usize_shift_right" := (usize_shift_right) (at level 77) : hacspec_scope.

Definition usize_shift_left (u: uint_size) (s: int32) : uint_size :=
  (rol u s).
Infix "usize_shift_left" := (usize_shift_left) (at level 77) : hacspec_scope.

Definition pub_uint128_wrapping_add (x y: int128) : int128 :=
  x .+ y.

Definition shift_left_ `{WS : wsize} (i : (@int WS)) (j : uint_size) : (@int WS) :=
  wshl i (unsigned (@repr WS (from_uint_size j))).

Definition shift_right_ `{WS : wsize} (i : (@int WS)) (j : uint_size) : (@int WS):=
  wshr i (unsigned (@repr WS (from_uint_size j))) .

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.

(*** Positive util *)

Section Util.

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

  (* Conversion of positive to binary representation *)
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

  (*** Uint size util *)

  (* If a natural number is in bound then a smaller natural number is still in bound *)
  Lemma range_of_nat_succ :
    forall {WS : wsize},
    forall i, (Z.pred 0 < Z.of_nat (S i) < modulus WS)%Z -> (Z.pred 0 < Z.of_nat i < modulus WS)%Z.
  Proof. lia. Qed.

  (* Conversion to equivalent bound *)
  Lemma modulus_range_helper :
    forall {WS : wsize},
    forall i, (Z.pred 0 < i < modulus WS)%Z -> (0 <= i <= wmax_unsigned WS)%Z.
  Proof.
    intros.
    unfold wmax_unsigned.
    unfold wbase.
    unfold nat_of_wsize in H.
    lia.
  Qed.

  Definition unsigned_repr_alt {WS : wsize} (a : Z) `((Z.pred 0 < a < modulus WS)%Z) :
    unsigned (@repr WS a) = a.
  Proof.
    apply wunsigned_repr_small.
    intros.
    unfold wbase.
    unfold nat_of_wsize in H.
    lia.
  Qed.

  Theorem zero_always_modulus {WS : wsize} : (Z.pred 0 < 0 < modulus WS)%Z.
  Proof. easy. Qed.

  (* any uint_size can be represented as a natural number and a bound *)
  (* this is easier for proofs, however less efficient for computation *)
  (* as Z uses a binary representation *)

  Theorem uint_size_as_nat :
    forall (us: uint_size),
      { n : nat |
        us = repr _ (Z.of_nat n) /\ (Z.pred 0 < Z.of_nat n < @modulus U32)%Z}.
  Proof.
    intros.
    exists (Z.to_nat (unsigned us)).
    rewrite Z2Nat.id by apply (ssrbool.elimT (word_ssrZ.leZP _ _) (urepr_ge0 us)).
    split.
    - rewrite wrepr_unsigned.
      reflexivity.
    - pose (wunsigned_range us).
      unfold wbase in a.
      unfold nat_of_wsize.
      cbn in *.
      lia.
  Qed.

  (* destruct uint_size as you would a natural number *)
  Definition destruct_uint_size_as_nat  (a : uint_size) : forall (P : uint_size -> Prop),
    forall (zero_case : P (repr _ 0%Z)),
    forall (succ_case : forall (n : nat), (Z.pred 0 < Z.of_nat n < @modulus U32)%Z -> P (repr _ (Z.of_nat n))),
      P a.
  Proof.
    intros.
    destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    destruct n.
    - apply zero_case.
    - apply succ_case.
      apply yb.
  Qed.


  (* induction for uint_size as you would do for a natural number *)
  Definition induction_uint_size_as_nat :
    forall (P : uint_size -> Prop),
      (P (repr _ 0%Z)) ->
      (forall n,
          (Z.pred 0 < Z.succ (Z.of_nat n) < @modulus U32)%Z ->
          P (repr _ (Z.of_nat n)) ->
          P (repr _ (Z.succ (Z.of_nat n)))) ->
      forall (a : uint_size), P a.
  Proof.
    intros P H_zero H_ind a.
    destruct (uint_size_as_nat a) as [ n y ] ; destruct y as [ya yb] ; subst.
    induction n.
    - apply H_zero.
    - rewrite Nat2Z.inj_succ.
      apply H_ind.
      + rewrite <- Nat2Z.inj_succ.
        apply yb.
      + apply IHn.
        lia.
  Qed.

  (* conversion of usize to positive or zero and the respective bound *)
  Theorem uint_size_as_positive :
    forall (us: uint_size),
      { pu : unit + positive |
        match pu with
        | inl u => us = repr _ Z0
        | inr p => us = repr _ (Z.pos p) /\ (Z.pred 0 < Z.pos p < @modulus U32)%Z
        end
      }.
  Proof.
    intros.

    destruct us as [val H_].
    pose proof (H := H_).
    apply Bool.andb_true_iff in H as [lt gt].
    apply (ssrbool.elimT (word_ssrZ.leZP _ _)) in lt.
    apply (ssrbool.elimT (word_ssrZ.ltZP _ _)) in gt.

    destruct val.
    - exists (inl tt). apply word_ext. reflexivity.
    - exists (inr p).
      split.
      + apply word_ext.
        rewrite Zmod_small by (unfold nat_of_wsize in gt ; lia).
        reflexivity.
      + cbn in gt.
        unfold nat_of_wsize.
        simpl.
        lia.
    - contradiction.
  Defined.

  (* destruction of uint_size as positive *)
  Definition destruct_uint_size_as_positive  (a : uint_size) : forall (P : uint_size -> Prop),
      (P (repr _ 0%Z)) ->
      (forall b, (Z.pred 0 < Z.pos b < @modulus U32)%Z -> P (repr _ (Z.pos b))) ->
      P a.
  Proof.
    intros P H_zero H_succ.
    destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
    - apply H_zero.
    - apply H_succ.
      apply yb.
  Qed.

  (* induction of uint_size as positive *)
  Definition induction_uint_size_as_positive :
    forall (P : uint_size -> Prop),
      (P (repr _ 0%Z)) ->
      (P (repr _ 1%Z)) ->
      (forall b,
          (Z.pred 0 < Z.succ (Z.pos b) < @modulus U32)%Z ->
          P (repr _ (Z.pos b)) ->
          P (repr _ (Z.succ (Z.pos b)))) ->
      forall (a : uint_size), P a.
  Proof.
    intros P H_zero H_one H_ind a.

    destruct (uint_size_as_positive a) as [ [ _ | b ] y ] ; [ subst | destruct y as [ya yb] ; subst ].
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

End Util.

Global Ltac destruct_uint_size_as_nat_named a H_zero H_succ :=
  generalize dependent a ;
  intros a ;
  apply (destruct_uint_size_as_nat a) ; [ pose proof (H_zero := @unsigned_repr_alt U32 0 zero_always_modulus) | let n := fresh in let H := fresh in intros n H ; pose proof (H_succ := @unsigned_repr_alt U32 _ H)] ; intros.

Global Ltac destruct_uint_size_as_nat a :=
  let H_zero := fresh in
  let H_succ := fresh in
  destruct_uint_size_as_nat_named a H_zero H_succ.

Global Ltac induction_uint_size_as_nat var :=
  generalize dependent var ;
  intros var ;
  apply induction_uint_size_as_nat with (a := var) ; [ pose proof (@unsigned_repr_alt U32 0 zero_always_modulus) | let n := fresh in let IH := fresh in intros n IH ; pose proof (@unsigned_repr_alt U32 _ IH)] ; intros.



(*** Loops *)

Open Scope nat_scope.
Fixpoint foldi_
         {acc : Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | 0 => cur
  | S n' => foldi_ n' (i .+ one) f (f i cur)
  end.
Close Scope nat_scope.
Definition foldi
           {acc: Type}
           (lo: uint_size)
           (hi: uint_size) (* {lo <= hi} *)
           (f: (uint_size) -> acc -> acc) (* {i < hi} *)
           (init: acc)
  : acc :=
  match Z.sub (unsigned hi) (unsigned lo) with
  | Z0 => init
  | Zneg p => init
  | Zpos p => foldi_ (Pos.to_nat p) lo f init
  end.

(* Fold done using natural numbers for bounds *)
Fixpoint foldi_nat_
         {acc : Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | O => cur
  | S n' => foldi_nat_ n' (S i) f (f i cur)
  end.


Fixpoint for_loop_
         {acc : Type}
         (fuel : nat)
         (f : nat -> acc -> acc)
         (cur : acc) : acc :=
  match fuel with
  | O => cur
  | S n' => f n' (for_loop_ n' f cur)
  end.

Definition foldi_nat
           {acc: Type}
           (lo: nat)
           (hi: nat) (* {lo <= hi} *)
           (f: nat -> acc -> acc) (* {i < hi} *)
           (init: acc) : acc :=
  match Nat.sub hi lo with
  | O => init
  | S n' => foldi_nat_ (S n') lo f init
  end.

Definition for_loop_range
           {acc: Type}
           (lo: nat)
           (hi: nat) (* {lo <= hi} *)
           (f: nat -> acc -> acc) (* {i < hi} *)
           (init: acc) : acc :=
  match Nat.sub hi lo with
  | O => init
  | S n' => for_loop_ (S n') (fun x => f (x + lo)%nat)  init
  end.

Definition for_loop_usize {acc : Type} (lo hi : uint_size) (f : uint_size -> acc -> acc) init : acc :=
  for_loop_range (from_uint_size lo) (from_uint_size hi) (fun x => f (usize x)) init.


Lemma foldi__move_S :
  forall {acc: Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc),
    foldi_ fuel (i .+ one) f (f i cur) = foldi_ (S fuel) i f cur.
Proof. reflexivity. Qed.

Lemma foldi__nat_move_S :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    foldi_nat_ fuel (S i) f (f i cur) = foldi_nat_ (S fuel) i f cur.
Proof. reflexivity. Qed.

Lemma foldi__nat_move_S_append :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    f (i + fuel)%nat (foldi_nat_ fuel i f cur) = foldi_nat_ (S fuel) i f cur.
Proof.
  induction fuel ; intros.
  - rewrite <- foldi__nat_move_S.
    unfold foldi_nat_.
    rewrite Nat.add_0_r.
    reflexivity.
  - rewrite <- foldi__nat_move_S.
    rewrite <- foldi__nat_move_S.
    replace (i + S fuel)%nat with (S i + fuel)%nat by lia.
    rewrite IHfuel.
    reflexivity.
Qed.

Theorem foldi_for_loop_eq :
  forall {acc} fuel f (cur : acc),
    foldi_nat_ fuel 0 f cur
    =
      for_loop_ fuel f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - unfold for_loop_ ; fold (@for_loop_ acc).
    rewrite <- foldi__nat_move_S_append.
    rewrite <- IHfuel.
    reflexivity.
Qed.

Lemma foldi__nat_move_to_function :
  forall {acc: choice_type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    foldi_nat_ fuel i (fun x => f (S x)) (cur) = foldi_nat_ fuel (S i) f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - cbn.
    rewrite IHfuel.
    reflexivity.
Qed.

Lemma foldi__nat_move_to_function_add :
  forall {acc: choice_type}
         (fuel : nat)
         (i j : nat)
         (f : nat -> acc ->  acc)
         (cur : acc),
    foldi_nat_ fuel i (fun x => f (x + j)%nat) (cur) = foldi_nat_ fuel (i + j) f cur.
Proof.
  intros acc fuel i j. generalize dependent i.
  induction j ; intros.
  - rewrite Nat.add_0_r.
    replace (fun x : nat => f (x + 0)%nat) with f.
    reflexivity.
    apply functional_extensionality.
    intros.
    now rewrite Nat.add_0_r.
  - replace (i + S j)%nat with (S i + j)%nat by lia.
    rewrite <- IHj.
    rewrite <- foldi__nat_move_to_function.
    f_equal.
    apply functional_extensionality.
    intros.
    f_equal.
    lia.
Qed.

Theorem foldi_for_loop_range_eq :
  forall {acc : choice_type} lo hi f (cur : acc),
    foldi_nat lo hi f cur
    =
      for_loop_range lo hi f cur.
Proof.
  unfold foldi_nat.
  unfold for_loop_range.
  intros.

  destruct (hi - lo)%nat.
  - reflexivity.
  - rewrite <- foldi_for_loop_eq.
    induction lo.
    + f_equal.
      apply functional_extensionality.
      intros.
      now rewrite Nat.add_0_r.
    + replace (fun x : nat => f (x + S lo)%nat) with (fun x : nat => f (S (x + lo))%nat).
      2:{
        apply functional_extensionality.
        intros.
        f_equal.
        lia.
      }

      rewrite (foldi__nat_move_to_function (S n) 0 (fun x => f (x + lo)%nat)).
      rewrite foldi__nat_move_to_function_add.
      reflexivity.
Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__move_S_fuel :
  forall {acc: Type}
         (fuel : nat)
         (i : uint_size)
         (f : uint_size -> acc -> acc)
         (cur : acc),
    (0 <= Z.of_nat fuel <= wmax_unsigned U32)%Z ->
    f ((repr _ (Z.of_nat fuel)) .+ i) (foldi_ (fuel) i f cur) = foldi_ (S (fuel)) i f cur.
Proof.
  intros acc fuel.
  induction fuel ; intros.
  - cbn.
    replace (repr _ 0%Z) with (@zero U32) by (rewrite wrepr0 ; reflexivity).
    rewrite add_zero_l.
    reflexivity.
  - do 2 rewrite <- foldi__move_S.
    replace (int_add (repr _ (Z.of_nat (S fuel))) i)
      with (int_add (repr _ (Z.of_nat fuel)) (int_add i one)).
    2 : {
      unfold int_add.
      setoid_rewrite addwA.
      rewrite addwC.
      rewrite addwA.
      f_equal.

      rewrite Nat2Z.inj_succ.
      (* unfold repr. *)
      unfold add_word.
      unfold wrepr.
      f_equal.
      rewrite urepr_word.

      replace (@toword (nat_of_wsize U32) (@one U32))%Z with 1%Z by reflexivity.
      (* unfold urepr. *)
      (* unfold eqtype.val. *)
      (* (* unfold word_subType. *) *)
      (* unfold toword. *)
      (* unfold mkword. *)
      
      rewrite Z.add_1_l.
      f_equal.
      rewrite mkwordK.
      rewrite Zmod_small.
        
      reflexivity.

      clear -H.
      unfold modulus.
      unfold two_power_nat.
      cbn in *.
      lia.
    }
    rewrite IHfuel.
    reflexivity.
    lia.
Qed.

(* You can do one iteration of the fold by burning a unit of fuel *)
Lemma foldi__nat_move_S_fuel :
  forall {acc: Type}
         (fuel : nat)
         (i : nat)
         (f : nat -> acc -> acc)
         (cur : acc),
    (0 <= Z.of_nat fuel <= @wmax_unsigned U32)%Z ->
    f (fuel + i)%nat (foldi_nat_ fuel i f cur) = foldi_nat_ (S fuel) i f cur.
Proof.
  induction fuel ; intros.
  - reflexivity.
  - do 2 rewrite <- foldi__nat_move_S.
    replace (S fuel + i)%nat with (fuel + (S i))%nat by (symmetry ; apply plus_Snm_nSm).
    rewrite IHfuel.
    + reflexivity.
    + lia.
Qed.

(* folds and natural number folds compute the same thing *)
Lemma foldi_to_foldi_nat :
  forall {acc: Type}
         (lo: uint_size)
         (hi: uint_size) (* {lo <= hi} *)
         (f: (uint_size) -> acc -> acc) (* {i < hi} *)
         (init: acc),
    (unsigned lo <= unsigned hi)%Z ->
    foldi lo hi f init = foldi_nat (Z.to_nat (unsigned lo)) (Z.to_nat (unsigned hi)) (fun x => f (repr _ (Z.of_nat x))) init.
Proof.
  intros.

  unfold foldi.
  unfold foldi_nat.

  destruct (uint_size_as_nat hi) as [ hi_n [ hi_eq hi_H ] ] ; subst.
  rewrite (@unsigned_repr_alt U32 _ hi_H) in *.
  rewrite Nat2Z.id.

  destruct (uint_size_as_nat lo) as [ lo_n [ lo_eq lo_H ] ] ; subst.
  rewrite (@unsigned_repr_alt U32 _ lo_H) in *.
  rewrite Nat2Z.id.

  remember (hi_n - lo_n)%nat as n.
  apply f_equal with (f := Z.of_nat) in Heqn.
  rewrite (Nat2Z.inj_sub) in Heqn by (apply Nat2Z.inj_le ; apply H).
  rewrite <- Heqn.

  assert (H_bound : (Z.pred 0 < Z.of_nat n < @modulus U32)%Z) by lia.

  clear Heqn.
  induction n.
  - reflexivity.
  - pose proof (H_max_bound := modulus_range_helper _ (range_of_nat_succ _ H_bound)).
    rewrite <- foldi__nat_move_S_fuel by apply H_max_bound.
    cbn.
    rewrite SuccNat2Pos.id_succ.
    rewrite <- foldi__move_S_fuel by apply H_max_bound.

    destruct n.
    + cbn.
      replace (repr _ 0%Z) with (@zero U32) by (rewrite wrepr0 ; reflexivity).
      rewrite add_zero_l.
      reflexivity.
    + cbn in *.
      assert (H_bound_pred: (Z.pred 0 < Z.pos (Pos.of_succ_nat n) < @modulus U32)%Z) by lia.
      rewrite <- (IHn H_bound_pred) ; clear IHn.
      f_equal.
      * rewrite add_repr.
        do 2 rewrite Zpos_P_of_succ_nat.
        rewrite Z.add_succ_l.
        rewrite Nat2Z.inj_add.
        reflexivity.
      * rewrite SuccNat2Pos.id_succ.
        rewrite foldi__move_S.
        reflexivity.
Qed.

(* folds can be computed by doing one iteration and incrementing the lower bound *)
Lemma foldi_nat_split_S :
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
    (lo < hi)%nat ->
    foldi_nat lo hi f init = foldi_nat (S lo) hi f (foldi_nat lo (S lo) f init).
Proof.
  unfold foldi_nat.
  intros.

  assert (succ_sub_diag : forall n, (S n - n = 1)%nat) by lia.
  rewrite (succ_sub_diag lo).

  induction hi ; [ lia | ].
  destruct (S hi =? S lo)%nat eqn:hi_eq_lo.
  - apply Nat.eqb_eq in hi_eq_lo ; rewrite hi_eq_lo in *.
    rewrite (succ_sub_diag lo).
    rewrite Nat.sub_diag.
    reflexivity.
  - apply Nat.eqb_neq in hi_eq_lo.
    apply Nat.lt_gt_cases in hi_eq_lo.
    destruct hi_eq_lo.
    + lia.
    + rewrite (Nat.sub_succ_l (S lo)) by apply (Nat.lt_le_pred _ _ H0).
      rewrite Nat.sub_succ_l by apply (Nat.lt_le_pred _ _ H).
      replace ((S (hi - S lo))) with (hi - lo)%nat by lia.
      reflexivity.
Qed.

(* folds can be split at some valid offset from lower bound *)
Lemma foldi_nat_split_add :
  forall (k : nat),
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (lo + k <= hi)%nat},
    foldi_nat lo hi f init = foldi_nat (k + lo) hi f (foldi_nat lo (k + lo) f init).
Proof.
  induction k ; intros.
  - cbn.
    unfold foldi_nat.
    rewrite Nat.sub_diag.
    reflexivity.
  - rewrite foldi_nat_split_S by lia.
    replace (S k + lo)%nat with (k + S lo)%nat by lia.
    specialize (IHk acc (S lo) hi f (foldi_nat lo (S lo) f init)).
    rewrite IHk by lia.
    f_equal.
    rewrite <- foldi_nat_split_S by lia.
    reflexivity.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_nat_split :
  forall (mid : nat), (* {lo <= mid <= hi} *)
  forall {acc: Type}
         (lo: nat)
         (hi: nat) (* {lo <= hi} *)
         (f: nat -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (lo <= mid <= hi)%nat},
    foldi_nat lo hi f init = foldi_nat mid hi f (foldi_nat lo mid f init).
Proof.
  intros.
  assert (mid_is_low_plus_constant : {k : nat | (mid = lo + k)%nat})  by (exists (mid - lo)%nat ; lia).
  destruct mid_is_low_plus_constant ; subst.
  rewrite Nat.add_comm.
  apply foldi_nat_split_add.
  apply guarantee.
Qed.

(* folds can be split at some midpoint *)
Lemma foldi_split :
  forall (mid : uint_size), (* {lo <= mid <= hi} *)
  forall {acc: Type}
         (lo: uint_size)
         (hi: uint_size) (* {lo <= hi} *)
         (f: uint_size -> acc -> acc) (* {i < hi} *)
         (init: acc),
  forall {guarantee: (unsigned lo <= unsigned mid <= unsigned hi)%Z},
    foldi lo hi f init = foldi mid hi f (foldi lo mid f init).
Proof.
  intros.
  do 3 rewrite foldi_to_foldi_nat by lia.
  apply foldi_nat_split ; lia.
Qed.

(*** Path / Sorted util *)

Lemma path_sorted_tl :
  forall {T : ordType} {A} {e} {fmval : list (T * A)},
  is_true (path.sorted e (seq.unzip1 fmval)) ->
  is_true (path.sorted e (seq.unzip1 (tl fmval))).
Proof.
  intros.
  destruct fmval.
  - easy.
  - cbn.
    cbn in H.
    destruct (seq.unzip1 fmval).
    + reflexivity.
    + cbn in H.
      now rewrite LocationUtility.is_true_split_and in H.
Qed.

Corollary path_path_tl :
  forall {T : ordType} {A} {e} {x : T} {fmval : list (T * A)},
    is_true (path.path e x (seq.unzip1 fmval)) ->
    is_true (path.sorted e (seq.unzip1 (fmval))).
Proof.
  intros.
  destruct fmval. reflexivity.
  apply (path_sorted_tl (fmval := (x, snd p) :: p :: fmval)).
  apply H.
Qed.

Lemma path_sorted_remove :
  forall {A : ordType} {B} {e} (x y : A * B) (l : list (A * B)),
    ssrbool.transitive e ->
  is_true
    (path.sorted e
        (seq.unzip1
           (x :: y :: l))) ->
  is_true
    (path.sorted e
        (seq.unzip1
           (x :: l))).
Proof.
  intros.
  cbn.
  induction l.
  reflexivity.
  cbn.
  cbn in *.
  rewrite !LocationUtility.is_true_split_and in H0.
  destruct H0 as [? []].
  rewrite H0 in IHl.

  rewrite !LocationUtility.is_true_split_and.
  split.
  - eapply H.
    apply H0.
    apply H1.
  - apply H2.
Qed.

Corollary path_path_remove :
  forall {A : ordType} {B} {e} (x : A) (y : A * B) (l : list (A * B)),
    ssrbool.transitive (T:=A) e ->
  is_true (path.path e (x) (seq.unzip1 (y :: l))) ->
  is_true (path.path e (x) (seq.unzip1 l)).
Proof.
  intros.
  apply (path_sorted_remove (x, snd y) y l H).
  apply H0.
Qed.

Lemma path_sorted_rev_last :
  forall {A : ordType} {B} {e} (a0 : A * B) (l : list (A * B)),
  is_true (path.sorted e (seq.unzip1 (seq.rev (a0 :: l)))) ->
  is_true (path.sorted e (seq.unzip1 (seq.rev l))).
Proof.
  intros.

  unfold seq.unzip1 ; rewrite seq.map_rev ; fold (seq.unzip1 l).
  rewrite path.rev_sorted.
  apply (path_sorted_tl (fmval := (a0 :: l))).
  rewrite <- path.rev_sorted.
  unfold seq.unzip1 ; rewrite <- seq.map_rev ; fold (seq.unzip1 (seq.rev (a0 :: l))).
  assumption.
Qed.

(*** Seq *)

Definition nseq_ (A: choice_type) (len : nat) : choice_type :=
  match len with
  | O => chUnit
  | S n => chMap ('fin (S n)) (A)
  end.
Notation "'nseq'" := (fun (A: choice_type) (len : choice.Choice.sort uint_size) => nseq_ A (from_uint_size (UInt_sizeable := nat_uint_sizeable) len)).

(* Definition nseq_type (A: choice_type) (len : nat) : Type := *)
(*   match len with *)
(*   | 0%nat => unit *)
(*   | S n => { fmap ('I_len) -> A } *)
(*   end. *)

Definition seq (A : choice_type) : choice_type := chMap 'nat (A).
(* Definition seq_type (A : choice_type) : Type := FMap.fmap_type nat_ordType (A). *)

Definition public_byte_seq := seq int8.
Definition byte_seq := seq int8.
Definition list_len := length.

Definition seq_index_nat {A: choice_type} (s: (seq A)) (i : nat) : A :=
  match getm s i with
  | Some a => a
  | None => chCanonical A
  end.

Definition seq_index {A: choice_type} (s: (seq A)) (i : uint_size) : A :=
  seq_index_nat s (from_uint_size i).

Definition seq_len_nat {A: choice_type} (s: (seq A)) : nat :=
  match (FMap.fmval s) with
  | [] => 0
  | (x :: xs) => S (fst (seq.last x xs))
  end.

Definition seq_len {A: choice_type} (s: (seq A)) : (uint_size) :=
  usize (seq_len_nat s).

Definition seq_to_list (A: choice_type) (s : (seq A)) : list (A) :=
  seq.map (fun n => seq_index_nat s n) (seq.iota 0 (seq_len_nat s)).

Definition seq_from_list (A : choice_type) (l : list (A)) : (seq A) :=
  fmap_of_seq l.

Lemma seq_from_list_cat : forall A l a, seq_from_list A (l ++ [a]) = setm (seq_from_list A l) (seq.size l) a.
Proof.
  clear ; intros.
  unfold seq_from_list.
  apply eq_fmap.

  intros i.
  rewrite fmap_of_seqE.
  rewrite setmE.

  destruct eqtype.eq_op eqn:i_size_l.
  - apply (ssrbool.elimT eqtype.eqP) in i_size_l.
    subst.

    rewrite (seq.nth_map a).
    2:{
      rewrite seq.size_cat.
      now rewrite ssrnat.addn1.
    }
    rewrite seq.nth_cat.
    rewrite ssrnat.ltnn.
    rewrite ssrnat.subnn.
    reflexivity.
  - rewrite fmap_of_seqE.
    destruct (ssrnat.leq (seq.size (l ++ [a])) i) eqn:i_in_l.
    + rewrite seq.nth_default.
      2:{
        rewrite seq.size_map.
        apply i_in_l.
      }
      rewrite seq.nth_default.
      2:{
        rewrite seq.size_map.
        eapply ssrnat.leq_trans.
        apply ssrnat.leqnSn.
        rewrite seq.size_cat in i_in_l.
        rewrite ssrnat.addn1 in i_in_l.
        apply i_in_l.
      }
      reflexivity.
    + assert (is_true (ssrnat.leq (S i) (seq.size l))).
      {
        rewrite ssrnat.leqNgt.
        rewrite ssrnat.ltnS.
        rewrite ssrnat.leq_eqVlt.
        rewrite Bool.negb_orb.
        rewrite eqtype.eq_sym.
        setoid_rewrite i_size_l.
        rewrite seq.size_cat in i_in_l.
        rewrite ssrnat.addn1 in i_in_l.
        rewrite i_in_l.
        reflexivity.
      }

      rewrite <- (@seq.nth_take (seq.size l) (option (A)) None i H (seq.map (fun x : A => Some x) (l ++ [a]))).
      rewrite <- seq.map_take.
      rewrite seq.take_size_cat ; [ | reflexivity ].
      reflexivity.
Qed.

Lemma sorted_last_leq :
  forall {A : ordType }{B} (a0 : A * B) (l : list (A * B)),
    is_true (path.sorted Ord.lt (seq.unzip1 (a0 :: l))) ->
    is_true (fst a0 <= (fst (seq.last a0 l)))%ord.
Proof.
  intros ? ? a0 fmval i.

  generalize dependent a0.
  induction fmval ; intros.
  - apply Ord.leqxx.
  - simpl.
    specialize (IHfmval a0 (path_sorted_remove (e := Ord.lt) _ _ _ (@Ord.lt_trans _) i)).
    erewrite Ord.leq_trans.
    reflexivity.
    apply IHfmval.
    destruct fmval.
    + simpl.
      simpl in i.
      rewrite Bool.andb_true_r in i.
      unfold Ord.lt in i.
      rewrite LocationUtility.is_true_split_and in i.
      apply i.
    + simpl.
      apply Ord.leqxx.
Qed.

Corollary sorted_last_nat_lt :
   forall {B} (a0 : nat * B) (l : list (nat * B)),
    is_true (path.sorted Ord.lt (seq.unzip1 (a0 :: l))) ->
    is_true (fst a0 < S (fst (seq.last a0 l)))%ord.
Proof.
  intros.
  pose (sorted_last_leq a0 l H).
  rewrite Ord.lt_neqAle.
  rewrite (Ord.leq_trans _ _ _ i) ; [ | easy ].

  destruct (eqtype.eq_op _ _) eqn:p_eq_last.
  - apply (ssrbool.elimT eqtype.eqP) in p_eq_last.
    setoid_rewrite p_eq_last in i.
    cbn in i.
    rewrite <- ssrnat.subnE in i.
    rewrite ssrnat.subSnn in i.
    discriminate.
  - easy.
Qed.

Theorem ord_lt_nleq_and_neq :
   forall {A : ordType} {a b : A},
     is_true (a < b)%ord -> (b < a)%ord = false /\ (eqtype.eq_op b a) = false.
Proof.
  intros.

  rewrite Ord.ltNge in H.
  rewrite Ord.leq_eqVlt in H.
  rewrite Bool.negb_orb in H.
  rewrite LocationUtility.is_true_split_and in H.
  destruct H.
  apply ssrbool.negbTE in H.
  apply ssrbool.negbTE in H0.
  rewrite H , H0 ; clear H H0.
  easy.
Qed.

Corollary sorted_last_is_last :
   forall {B} (a0 : nat * B) (l : list (nat * B)),
    is_true (path.sorted Ord.lt (seq.unzip1 (a0 :: l))) ->
        (S (fst (seq.last a0 l)) < fst a0)%ord = false /\
          (@eqtype.eq_op (nat : ordType) (S (fst (seq.last a0 l))) (fst a0) = false).
Proof.
  intros.

  pose (i0 := sorted_last_nat_lt a0 l H).
  destruct (ord_lt_nleq_and_neq i0).
  easy.
Qed.

Theorem ord_leq_lt_trans :
  forall {A : ordType} {a b c : A}, is_true (a <= b)%ord -> is_true (b < c)%ord -> is_true (a < c)%ord.
Proof.
  intros.
  pose proof (Ord.leq_trans _ _ _ H (Ord.ltW H0)).
  rewrite Ord.leq_eqVlt in H1.
  rewrite LocationUtility.is_true_split_or in H1.
  destruct H1.
  - apply (ssrbool.elimT eqtype.eqP) in H1.
    subst.
    rewrite Ord.leq_eqVlt in H.
    rewrite LocationUtility.is_true_split_or in H.
    destruct H.
    + apply (ssrbool.elimT eqtype.eqP) in H.
      subst.
      now rewrite Ord.ltxx in H0.
    + pose proof (Ord.lt_trans H H0).
      now rewrite Ord.ltxx in H1.
  - apply H1.
Qed.

Theorem ord_lt_leq_trans :
  forall {A : ordType} {a b c : A}, is_true (a < b)%ord -> is_true (b <= c)%ord -> is_true (a < c)%ord.
Proof.
  intros.
  pose proof (Ord.leq_trans _ _ _ (Ord.ltW H) H0).
  rewrite Ord.leq_eqVlt in H1.
  rewrite LocationUtility.is_true_split_or in H1.
  destruct H1.
  - apply (ssrbool.elimT eqtype.eqP) in H1.
    subst.
    rewrite Ord.leq_eqVlt in H0.
    rewrite LocationUtility.is_true_split_or in H0.
    destruct H0.
    + apply (ssrbool.elimT eqtype.eqP) in H0.
      subst.
      now rewrite Ord.ltxx in H.
    + pose proof (Ord.lt_trans H H0).
      now rewrite Ord.ltxx in H1.
  - apply H1.
Qed.

Theorem ord_lt_is_leq :
  forall {a b : nat}, is_true (a < b)%ord -> is_true (S a <= b)%ord.
Proof.
  intros.
  generalize dependent a.
  induction b ; intros.
  - destruct a ; easy.
  - destruct a ; [ easy | ].
    cbn.
    cbn in IHb.
    apply IHb.
    apply H.
Qed.

Theorem seq_len_nat_setm : forall {A} (l : (seq A)) a,
    forall x, is_true (seq_len_nat l <= x)%ord ->
    seq_len_nat (setm l x a) = S x.
Proof.
  intros.
  destruct l.
  destruct fmval.
  -     reflexivity.
  - unfold seq_len_nat.
    simpl.
    destruct (ord_lt_nleq_and_neq (ord_lt_leq_trans (sorted_last_nat_lt p fmval i) H)).
    setoid_rewrite H0.
    setoid_rewrite H1.
    clear H0 H1.

    generalize dependent p.
    induction fmval ; intros.
    * reflexivity.
    * simpl.

      destruct (ord_lt_nleq_and_neq (ord_lt_leq_trans (sorted_last_nat_lt a0 fmval (path_sorted_tl i)) H)).
      setoid_rewrite H0.
      setoid_rewrite H1.
      clear H0 H1.
      simpl.

      rewrite (IHfmval a0 (path_sorted_tl i)).
      reflexivity.
      apply H.
Qed.

Corollary seq_len_nat_setm_len : forall {A} (l : (seq A)) a,
    seq_len_nat (setm l (seq_len_nat l) a) = S (seq_len_nat l).
Proof.
  intros.
  apply seq_len_nat_setm.
  easy.
Qed.

Theorem seq_from_list_size : forall A l,
    seq.size l = seq_len_nat (seq_from_list A l).
Proof.
  intros.
  rewrite <- (rev_involutive l).
  induction (rev l).
  - reflexivity.
  - simpl.
    rewrite seq_from_list_cat.
    rewrite seq.size_cat.
    rewrite IHl0 ; clear IHl0.
    rewrite ssrnat.addn1.

    now erewrite (seq_len_nat_setm (seq_from_list A (rev l0))).
Qed.


Lemma destruct_fmap_last :
  forall {A : ordType} {B} (a0 : A * B) (l : list (A * B)) i,
    (FMap.FMap (fmval:=seq.rev (a0 :: l)) i = setm (FMap.FMap (fmval:=seq.rev l) (path_sorted_rev_last a0 l i)) (fst a0) (snd a0)).
Proof.
  intros.
  apply eq_fmap.
  intros v.
  rewrite setmE.

  destruct (eqtype.eq_op v (fst a0)) eqn:v_eq_a0.
  - apply (ssrbool.elimT eqtype.eqP) in v_eq_a0.
    subst.

    generalize dependent l.
    intros l.
    rewrite seq.rev_cons.
    intros.
    unfold getm ; simpl.

    induction (seq.rev l).
    + simpl. now rewrite eqtype.eq_refl.
    + simpl.
      rewrite IHl0 ; clear IHl0.
      * simpl in i.
        unfold seq.unzip1 in i.
        rewrite seq.map_rcons in i.
        rewrite path.rcons_path in i.
        rewrite LocationUtility.is_true_split_and in i.
        destruct i.
        pose (H1 := sorted_last_leq a l0 H).
        rewrite seq.last_map in H0.
        epose (ord_leq_lt_trans H1 H0).
        rewrite Ord.lt_neqAle in i.
        rewrite LocationUtility.is_true_split_and in i.
        destruct i.
        apply ssrbool.negbTE in H2.
        rewrite eqtype.eq_sym.
        rewrite H2.
        reflexivity.

        destruct l0.
        -- reflexivity.
        -- simpl.
           simpl in i.
           rewrite LocationUtility.is_true_split_and in i.
           apply i.
      * unfold getm.
        simpl.
        unfold seq.rev at 1.
        simpl.
        rewrite seq.catrevE.
        induction (seq.rev l) ; simpl.
        -- now rewrite v_eq_a0.
        -- now rewrite IHl0.
Qed.

Lemma seq_to_list_setm : forall {A : choice_type} (l : (seq A)) a,
  seq_to_list A (setm l (seq_len_nat l) a) = seq_to_list A l ++ [a].
Proof.
  intros.

  unfold seq_to_list.
  rewrite seq_len_nat_setm.
  rewrite <- ssrnat.addn1.
  rewrite seq.iotaD.
  rewrite ssrnat.add0n.
  simpl.
  rewrite seq.map_cat.
  simpl.
  unfold seq_index_nat.
  rewrite setmE.
  rewrite eqtype.eq_refl.

  set (seq.map _ _).
  set (seq.map _ _).

  assert (l0 = l1) ; subst l0 l1.
  {
    set (seq_len_nat l) at 1.
    assert (seq_len_nat l <= n)%nat by reflexivity.
    generalize dependent n.
    induction (seq_len_nat l) ; intros.
    - reflexivity.
    - rewrite <- ssrnat.addn1.
      rewrite seq.iotaD.
      rewrite <- ssrnat.addn1.
      rewrite seq.iotaD.
      rewrite !ssrnat.add0n.
      rewrite !ssrnat.addn0.
      simpl.
      rewrite seq.map_cat.
      rewrite seq.map_cat.

      f_equal.
      {
        setoid_rewrite IHn.
        reflexivity.
        lia.
      }
      {
        simpl.
        rewrite setmE.
        replace (eqtype.eq_op _ _) with false.
        2:{
          clear -H.
          cbn.
          generalize dependent n0.
          induction n ; intros.
          - destruct n0 ; easy.
          - destruct n0 ; [ easy | ].
            simpl.
            specialize (IHn n0).
            rewrite IHn.
            reflexivity.
            lia.
        }
        reflexivity.
      }
  }

  now rewrite H.
  easy.
Qed.

Definition seq_from_list_id : forall {A : choice_type} (t : list (A)),
    seq_to_list  A (seq_from_list A t) = t.
Proof.
  intros.
  rewrite <- (seq.revK t).
  induction (seq.rev t).
  - reflexivity.
  - simpl.
    rewrite seq.rev_cons.
    set (h := seq.rev l) at 1 ; rewrite <- IHl ; subst h. clear IHl.
    rewrite <- !seq.cats1.
    rewrite seq_from_list_cat.
    rewrite seq_from_list_size.
    rewrite seq_to_list_setm.
    reflexivity.
Qed.

Definition seq_to_list_size :
  forall {A : choice_type} (t : (seq A)),
    seq.size (seq_to_list A t) = seq_len_nat t.
Proof.
  intros.
  destruct t.
  generalize dependent fmval.
  intros fmval.
  rewrite <- (seq.revK fmval).
  intros.

  induction (seq.rev fmval).
  - reflexivity.
  - rewrite destruct_fmap_last.

    intros.

    unfold seq_to_list in *.
    rewrite seq_len_nat_setm.

    rewrite <- ssrnat.addn1.
    rewrite seq.iotaD.
    rewrite ssrnat.add0n.
    simpl.
    rewrite seq.map_cat.
    simpl.

    rewrite ssrnat.addn1.

    unfold seq_index_nat.

    rewrite setmE.
    rewrite eqtype.eq_refl.

    rewrite seq.size_cat.
    rewrite seq.size_map.
    rewrite seq.size_iota.
    simpl.
    rewrite ssrnat.addn1.
    reflexivity.

    unfold seq_len_nat.
    simpl.

    clear -i.

    rewrite seq.rev_cons in i.
    rewrite <- seq.cats1 in i.

    (* set seq.rev in i ; unfold Ord.sort, nat_ordType in l0 ; subst l0. *)
    destruct (seq.rev _).
    + easy.
    + generalize dependent p.
      induction l0 ; intros.
      * simpl.
        simpl in i.
        rewrite Bool.andb_true_r in i.
        now apply ord_lt_is_leq.
      * simpl.
        apply IHl0.
        apply (path_sorted_tl i).
Qed.

Definition seq_new_ {A: choice_type} (init : A) (len: uint_size) : (seq A) :=
  fmap_of_seq (repeat init (Z.to_nat (unsigned len))).

Definition seq_new {A: choice_type} (len: uint_size) : (seq A) :=
  seq_new_ (chCanonical A) len.

Definition seq_create {A: choice_type} (len: uint_size) : (seq A) :=
  seq_new len.

Definition repr_Z_succ : forall WS z, @repr WS (Z.succ z) = (repr _ z .+ one).
Proof.
  intros.
  replace one with (@repr WS 1%Z) by (unfold one ; now rewrite word1_zmodE).
  now rewrite add_repr.
Qed.

Lemma lt_succ_diag_r_sub : forall x k, (x - k < S x)%nat.
Proof.
  intros.
  generalize dependent x.
  induction k ; intros.
  - rewrite Nat.sub_0_r.
    apply Nat.lt_succ_diag_r.
  - destruct x.
    + apply Nat.lt_succ_diag_r.
    + cbn.
      apply Nat.lt_lt_succ_r.
      apply (IHk x).
Qed.

Definition setm_leave_default {T : ordType} {S : choice_type}
       (m : {fmap T -> S}) (i : T) (e : S) : {fmap T -> S} :=
  if eqtype.eq_op e (chCanonical S)
  then m
  else setm m i e.

Equations array_from_list_helper {A: choice_type} (x : A) (xs: list (A)) (k : nat) : (nseq_ A (S k)) :=
  array_from_list_helper x [] k :=
    setm
      emptym
      (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k O)))
      x ;
  array_from_list_helper x (y :: ys) k :=
    setm
      (array_from_list_helper y ys k)
      (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k (length (y :: ys)))))
      x.

Definition array_from_list {A: choice_type} (l: list (A))
  : (nseq_ A (length l)) :=
  match l with
    nil => tt
  | (x :: xs) => array_from_list_helper x xs (length xs)
  end.

Definition resize_to_k {A : choice_type} (l : list A) k := List.rev (seq.drop (length l - k) (List.rev l)) ++ (List.repeat (chCanonical A) (k - length l)).

Theorem length_resize_to_k : forall {A : choice_type} (l : list A) k, List.length (resize_to_k l k) = k.
Proof.
  intros.
  unfold resize_to_k.
  rewrite List.app_length.
  rewrite List.rev_length.
  rewrite seq.size_drop.
  rewrite List.repeat_length.
  rewrite List.rev_length.
  Lia.lia.
Defined.

Theorem resize_to_length_idemp : forall {A : choice_type} (l : list A), l = resize_to_k l (length l).
Proof.
  intros.
  induction l.
  - reflexivity.
  - unfold resize_to_k.
    rewrite (Nat.sub_diag).
    rewrite seq.drop0.
    rewrite List.rev_involutive.
    now rewrite List.app_nil_r.
Qed.

Definition array_from_list' {A: choice_type}  (l: list (A)) (k : nat)
  : (nseq_ A k) :=
  match k with
  | O => (tt : (nseq_ A O))
  | S k' =>
      match resize_to_k l (S k') with
        nil => fmap.emptym
      | (x :: xs) => array_from_list_helper x xs k'
      end
  end.

Definition lift_ordinal n (x : 'I_n) : 'I_(S n).
Proof.
  destruct x.
  apply (Ordinal (m := S m)).
  apply i.
Defined.

Equations lift_fval {A : choice_type} {n} (a : list ('I_(S n) * (A))) : list ('I_(S(S n)) * (A)) :=
  lift_fval [] := [] ;
  lift_fval (x :: xs) :=
    (lift_ordinal (S n) (fst x) , snd x) :: lift_fval xs.

Lemma lift_is_sorted : forall  {A : choice_type} {n} (a : {fmap 'I_(S n) -> (A)}), is_true (path.sorted Ord.lt (seq.unzip1 (lift_fval a))).
Proof.
  intros.
  destruct a.
  simpl.

  induction fmval.
  - reflexivity.
  - destruct a.
    simpl.
    intros.
    rewrite lift_fval_equation_2 ; simpl.
    destruct fmval.
    + reflexivity.
    + pose proof i.
      rewrite lift_fval_equation_2 ; simpl.

      simpl in H.
      rewrite LocationUtility.is_true_split_and in H.
      destruct H.

      rewrite LocationUtility.is_true_split_and.
      split ; [ | ].
      2:{
        apply IHfmval.
        apply H0.
      }

      unfold lift_ordinal.
      destruct s.
      destruct (fst _).
      apply H.
Qed.

Definition lift_nseq {A: choice_type} {len : nat} (x: nseq_ A len) : (nseq_ A (S len)) :=
  match len as k return nseq_ A k -> nseq_ A (S k) with
  | O => fun _ => emptym
  | S n =>
      fun x => @FMap.FMap _ _ (lift_fval (FMap.fmval x)) (lift_is_sorted x)
  end x.

Definition setm_option {T : ordType} {S : choice_type}
       (m : {fmap T -> S}) (i : T) (e : chOption S) : {fmap T -> S} :=
  match e with
  | Some x => setm m i x
  | None => m
  end.

Equations array_from_option_list_helper {A: choice_type} (x : chOption A) (xs: list (chOption A)) (k : nat) : (nseq_ A (S k)) :=
  array_from_option_list_helper x (y :: ys) O :=
      emptym ;
  array_from_option_list_helper x [] k :=
    setm_option
      emptym
      (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k O)))
      x ;
  array_from_option_list_helper x (y :: ys) (S k) :=
    setm_option
      (lift_nseq (array_from_option_list_helper y ys k))
      (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub (S k) (length (y :: ys)))))
      x.
Fail Next Obligation.

Definition array_from_option_list' {A: choice_type}  (l: list (chOption A)) (k : nat)
  : (nseq_ A k) :=
  match k with
  | O => (tt : (nseq_ A O))
  | S k' =>
      match resize_to_k l (S k') with
        nil => fmap.emptym
      | (x :: xs) => array_from_option_list_helper x xs k'
      end
  end.

Theorem list_rev_is_seq_rev : forall T (x : list T), List.rev x = seq.rev x.
Proof.
  intros.
  induction x.
  - reflexivity.
  - simpl.
    rewrite IHx.
    replace (a :: nil) with (seq.rev (a :: nil)) by reflexivity.
    now rewrite <- seq.rev_cat.
Qed.

Theorem simple0_array_from_list : forall (A : choice_type) (x : list A), array_from_list' x (List.length x) = array_from_list x.
Proof.
  intros.
  subst.
  simpl.
  induction x.
  - reflexivity.
  - simpl.
    unfold resize_to_k.
    simpl.
    rewrite (Nat.sub_diag (length x)).
    setoid_rewrite seq.drop0.
    change (List.rev _ ++ _ :: nil) with (List.rev (a :: x)).
    rewrite List.rev_involutive.
    now rewrite List.app_nil_r.
Defined.

Theorem simple_array_from_list : forall (A : choice_type) (x : list A) len (H : List.length x = len), array_from_list' x len = (eq_rect (length x) (fun n : nat => nseq_ A n) (array_from_list x) len H).
Proof.
  intros.
  subst.
  apply simple0_array_from_list.
Defined.

(**** Array manipulation *)

Definition array_new_ {A: choice_type} (init:A) (len: nat) : (nseq_ A len) :=
  match len with
    O => (tt : (nseq_ A 0))
  | (S n') => array_from_list_helper init (repeat init n') n'
  end.

Equations array_index {A: choice_type} {len : nat} (s: (nseq_ A len)) {WS} (i: (@int WS)) : A :=
  array_index (len := 0) s i := (chCanonical A) ;
  array_index (len := (S n)) s i with le_lt_dec (S n) (Z.to_nat (unsigned i)) := {
    | right a with (@getm _ _ s (fintype.Ordinal (n := S n) (m := Z.to_nat (unsigned i)) ((ssrbool.introT ssrnat.ltP a)))) => {
      | Some f => f
      | None => (chCanonical A)
      }
    | left b => (chCanonical A)
    }.

Equations array_upd {A: choice_type} {len : nat} (s: (nseq_ A len)) {WS} (i: (@int WS)) (new_v: A) : (nseq_ A len) :=
  array_upd s i new_v with len :=
    {
      array_upd s i new_v n with lt_dec (Z.to_nat (unsigned i)) n := {
        array_upd s i new_v O (left l)  => ltac:(apply Nat.ltb_lt in l ; discriminate) ;
        array_upd s i new_v (S n) (left l)  => (setm s (fintype.Ordinal (n := S n) (m := Z.to_nat (unsigned i)) (ssrbool.introT ssrnat.ltP l)) new_v) ;
        array_upd s i new_v n (right _) => s
      }
    }.

Definition array_upd2 {A: choice_type} {len : nat} (s: (nseq_ A len)) {WS} (i: (@int WS)) (new_v: A) : (nseq_ A len).
Proof.
  destruct (Z.to_nat (unsigned i) <? len)%nat eqn:v.
  (* If i < len, update normally *)
  - apply Nat.ltb_lt in v.
    destruct len. { lia. }
    apply (setm s (fintype.Ordinal (m := Z.to_nat (unsigned i)) (ssrbool.introT ssrnat.ltP v)) new_v).
  (* otherwise return original array *)
  - exact s.
Defined.

(* substitutes a sequence (nseq) into an array (nseq), given index interval  *)
Definition update_sub {A : choice_type} {len slen} (v : (nseq_ A len)) (i : nat) (n : nat) (sub : (nseq_ A slen)) : (nseq_ A len) :=
  let fix rec x acc :=
    match x with
    | 0%nat => acc
    | S x => rec x (array_upd acc (usize (i+x)%nat) (array_index sub (usize x)))
    end in
  rec (n - i + 1)%nat v.

Definition array_from_seq
           {A: choice_type}
           (out_len:nat)
           (input: (seq A))
  : (nseq_ A out_len) :=
  let out := array_new_ (chCanonical A) out_len in
  update_sub out 0 (out_len - 1) (@array_from_list A (@seq_to_list A input)).

Definition slice {A} (l : list A) (i j : nat) : list A :=
  if (j <=? i)%nat then [] else firstn (j-i+1) (skipn i l).

Definition lower_ordinal n (x : 'I_(S n)) (H: is_true (ord0 < x)%ord) : 'I_n.
Proof.
  destruct x.
  apply (Ordinal (m := Nat.pred m)).
  apply ssrnat.ltnSE.
  rewrite (Nat.lt_succ_pred 0).
  - apply i.
  - destruct m.
    + discriminate.
    + lia.
Defined.



Equations lower_fval {A : choice_type} {n} (a : list ('I_(S(S n)) * (A))) (H : forall x, In x a -> is_true (ord0 < fst x)%ord ) : list ('I_(S n) * (A)) :=
  lower_fval [] H := [] ;
  lower_fval (x :: xs) H :=
    (lower_ordinal (S n) (fst x) (H x (or_introl eq_refl)) , snd x)
      :: lower_fval xs (fun y H0 => H y (in_cons x y xs H0)).

Lemma lower_keeps_value : forall  {A : choice_type} {n} (a : {fmap 'I_(S(S n)) -> (A)}) H, (seq.map snd a = seq.map snd (lower_fval a H)).
Proof.
  intros.
  destruct a.
  simpl in *.
  induction fmval.
  - cbn.
    reflexivity.
  - destruct a.
    rewrite seq.map_cons.
    erewrite IHfmval.
    rewrite lower_fval_equation_2 ; simpl.
    f_equal.
    apply (path_sorted_tl i).
Qed.

Lemma lower_is_sorted : forall  {A : choice_type} {n} (a : {fmap 'I_(S(S n)) -> (A)}) H, is_true (path.sorted Ord.lt (seq.unzip1 (lower_fval a H))).
Proof.
  intros.
  destruct a.
  simpl.
  induction fmval.
  - reflexivity.
  - destruct a.
    simpl.
    intros.
    rewrite lower_fval_equation_2 ; simpl.
    destruct fmval.
    + reflexivity.
    + pose proof i.
      rewrite lower_fval_equation_2 ; simpl.
      simpl in H0 |- *.
      rewrite LocationUtility.is_true_split_and in H0 |- *.

      destruct H0.
      split ; [ | ].
      destruct p.
      simpl.
      destruct s, s1.

      pose proof (H (Ordinal (n:=S (S n)) (m:=m) i0, s0) (or_introl eq_refl)).
      pose proof (H (Ordinal (n:=S (S n)) (m:=m0) i1, s2)
          (in_cons (Ordinal (n:=S (S n)) (m:=m) i0, s0)
             (Ordinal (n:=S (S n)) (m:=m0) i1, s2)
             ((Ordinal (n:=S (S n)) (m:=m0) i1, s2) :: fmval)
             (or_introl eq_refl))).

      unfold Ord.lt in H0 |- *.
      unfold Ord.leq in H0 |- *.
      cbn.

      clear -H0 H2 H3.
      rewrite LocationUtility.is_true_split_and in H0 |- *.
      destruct H0.
      cbn in H , H0.
      destruct m, m0 ; easy.

      specialize (IHfmval (path_sorted_tl i) ( fun x H2 => H x (in_cons _ _ _  H2))).
      rewrite lower_fval_equation_2 in IHfmval ; simpl in IHfmval.
      simpl.
      apply IHfmval.
Qed.

Corollary lower_list_is_sorted : forall  {A : choice_type} {n} (a : list ('I_(S(S n)) * (A))) H, is_true (path.sorted Ord.lt (seq.unzip1 a)) -> is_true (path.sorted Ord.lt (seq.unzip1 (lower_fval a H))).
Proof.
  intros.
  refine (lower_is_sorted (@FMap.FMap _ _ a _) _).
  apply H0.
Qed.

Lemma ord_ext : forall {n} m0 m1 {H1 H2}, m0 = m1 <-> Ordinal (n := S n) (m := m0) H1 = Ordinal (n := S n) (m := m1) H2.
Proof.
  intros.
  rewrite <- (inord_val (Ordinal H1)).
  rewrite <- (inord_val (Ordinal H2)).
  split. intros. subst. reflexivity.
  intros. cbn in H.
  unfold inord in H.
  unfold eqtype.insubd in H.
  unfold eqtype.insub in H.
  destruct ssrbool.idP in H.
  destruct ssrbool.idP in H.
  cbn in H.
  inversion H.
  reflexivity.
  contradiction.
  contradiction.
Qed.

Lemma lower_fval_ext : forall  {A : choice_type} {n} (a b : {fmap 'I_(S(S n)) -> A}) H1 H2, a = b <-> lower_fval a H1 = lower_fval b H2.
Proof.
  intros.
  split.
  - intros.
    subst.
    destruct b.
    simpl.
    induction fmval.
    + reflexivity.
    + simpl.
      destruct a, s.
      rewrite !lower_fval_equation_2.
      f_equal.
      * f_equal.
        apply ord_ext. reflexivity.
      * apply IHfmval.
        apply (path_sorted_tl i).
  - intros.
    apply eq_fmap.
    intros i.

    destruct a.
    destruct b.
    cbn in H.
    cbn.

    f_equal.

    generalize dependent fmval0.
    induction fmval as [ | p ] ; intros ; destruct fmval0 as [ | p0 ] ; try rewrite !lower_fval_equation_2 in H ; try rewrite !lower_fval_equation_1 in H ; try easy.

    inversion H.
    epose (H1 p (or_introl eq_refl)).
    epose (H2 p0 (or_introl eq_refl)).

    destruct p.
    destruct p0.
    cbn in H4.
    subst.
    destruct s.
    destruct s1.
    apply ord_ext in H3.
    f_equal.
    {
      f_equal.
      apply ord_ext.
      destruct m, m0 ; try discriminate.
      cbn in H3.
      now rewrite H3.
    }
    {
      eapply IHfmval.
      apply H5.

      Unshelve.
      apply (path_sorted_tl i0).
      apply (path_sorted_tl i1).
    }
Qed.


Lemma lower_fval_ext_list : forall  {A : choice_type} {n} (a b : list ('I_(S(S n)) * (A))) (Ha : is_true (path.sorted Ord.lt (seq.unzip1 a))) (Hb : is_true (path.sorted Ord.lt (seq.unzip1 b))) H1 H2, a = b <-> lower_fval a H1 = lower_fval b H2.
Proof.
  intros.
  epose (lower_fval_ext (@FMap.FMap _ _ a Ha) (@FMap.FMap _ _ b Hb) H1 H2).
  simpl in i.
  rewrite <- i.
  split.
  intros.
  apply fmap.eq_fmap.
  intros x.
  subst.
  reflexivity.
  intros.
  now inversion H.
Qed.


Lemma gt_smallest_sorted : forall {A} {n} {p : 'I_n * A} {fmval}, is_true (path.sorted Ord.lt (seq.unzip1 (p :: fmval))) -> (forall x, In x fmval -> is_true (fst p < fst x)%ord).
  intros.
  induction fmval.
  - contradiction.
  - cbn in H.
    rewrite LocationUtility.is_true_split_and in H.
    destruct H.
    destruct H0.
    + subst.
      apply H.
    + apply IHfmval.
      cbn.
      eapply path.path_le.
      apply (@Ord.lt_trans _).
      apply H.
      apply H1.
      apply H0.
Qed.

Corollary tl_gt_0_sorted : forall {A} {n} {p : 'I_(S n) * A} {fmval}, is_true (path.sorted Ord.lt (seq.unzip1 (p :: fmval))) -> (forall x, In x fmval -> is_true (ord0 < fst x)%ord).
  intros.
  induction fmval ; [ easy | ].
  pose proof H.
  simpl in H1.
  rewrite LocationUtility.is_true_split_and in H1.
  destruct H1.
  destruct H0.
  - subst.
    destruct p, o.
    destruct m.
    + apply H1.
    + eapply Ord.lt_trans. 2: apply (gt_smallest_sorted H) ; now left.
      easy.
  - refine (IHfmval _ H0).
    cbn.
    eapply path.path_le.
    apply Ord.lt_trans.
    apply H1.
    apply H2.
Qed.

Lemma in_nseq_tl_gt_zero {A} {n} {m'} {i3} {k} fmval (i :
  is_true (path.path Ord.lt (fst (@Ordinal _ (S m') i3, k)) (seq.unzip1 fmval))) :
  (forall x : 'I_(S (S n)) * A,
   In x ((@Ordinal _ (S m') i3, k) :: fmval) ->
   is_true (ord0 < fst x)%ord).
Proof.
  intros.
  destruct H.
  - subst. reflexivity.
  - eapply tl_gt_0_sorted.
    apply i.
    apply H.
Qed.

Equations tl_fmap {A : choice_type} {n} (a : {fmap 'I_(S(S n)) -> A}) : {fmap 'I_(S n) -> A} :=
  tl_fmap (@FMap.FMap _ _ [] i) := emptym ;
  tl_fmap (@FMap.FMap _ _ ((@Ordinal _ 0 i3, k) :: fmval) i) :=
    @FMap.FMap _ _ (lower_fval fmval (gt_smallest_sorted i)) (lower_list_is_sorted _ _ (path_path_tl i)) ;
  tl_fmap (@FMap.FMap _ _ ((@Ordinal _ (S m') i3, k) :: fmval) i) :=
    @FMap.FMap _ _ (lower_fval ((Ordinal (n:=S (S n)) (m:=S m') i3, k) :: fmval) (in_nseq_tl_gt_zero fmval i)) (lower_list_is_sorted _ _ i).
Fail Next Obligation.

Definition nseq_hd {A : choice_type} {n} (a : (nseq_ A (S n))) : A :=
  match a with
  | @FMap.FMap _ _ [] _ => (chCanonical A)
  | @FMap.FMap _ _ (p :: _) _ =>
      match nat_of_ord (fst p) with
      | O => snd p
      | S _ => (chCanonical A)
      end
  end.

Definition nseq_hd_option {A : choice_type} {n} (a : (nseq_ A (S n))) : chOption A :=
  match a with
  | @FMap.FMap _ _ [] _ => None
  | @FMap.FMap _ _ (p :: _) _ =>
      match nat_of_ord (fst p) with
      | O => Some (snd p)
      | S _ => None
      end
  end.

Definition nseq_tl {A : choice_type} {n} (a : (nseq_ A (S n))) : (nseq_ A n).
Proof. destruct n ; [exact tt | apply (tl_fmap a) ]. Defined.

Definition split_nseq_ {A : choice_type} {n} (a : (nseq_ A (S n))) : A * (nseq_ A n) := (nseq_hd a, nseq_tl a).


Lemma lower_fval_smaller_length {A : choice_type} {n} (a : {fmap 'I_(S(S n)) -> A}) : (length (FMap.fmval a) <= S (length (FMap.fmval (tl_fmap a))))%nat.
Proof.
  destruct a.
  induction fmval.
  - cbn ; lia.
  - simpl.
    simpl in IHfmval.
    destruct a, s. destruct m.
    + apply Nat.eq_le_incl.
      f_equal.
      rewrite tl_fmap_equation_2.
      (* rewrite mkfmapK ; [ | apply (lower_is_sorted (@FMap.FMap _ _ fmval (path_sorted_tl i)))]. *)
      epose (lower_keeps_value (FMap.FMap (T:=fintype_ordinal__canonical__Ord_Ord (S (S n))) (fmval:=fmval) (path_sorted_tl i))).
      simpl in e.
      rewrite <- (map_length snd).
      rewrite <- (map_length snd).
      assert (forall {A B} (f : A -> B) (l : list A), seq.map f l = map f l).
      {
        clear ; intros.
        induction l.
        - reflexivity.
        - cbn.
          f_equal.
      }
      setoid_rewrite <- H.
      erewrite e.
      reflexivity.
    + rewrite tl_fmap_equation_3.
      apply le_n_S.
      eapply le_trans ; [ apply (IHfmval (path_sorted_tl i)) | ].
      apply Nat.eq_le_incl.
      (* rewrite mkfmapK ; [ | apply (lower_is_sorted (@FMap.FMap _ _ ((Ordinal (n:=S (S n)) (m:=S m) i0, s0) :: fmval) i)) ]. *)
      simpl.
      f_equal.
      f_equal.
      clear.

      induction fmval.
      * reflexivity.
      * destruct a, s.
        destruct m0 ; [ discriminate | ].
        rewrite tl_fmap_equation_3.
        simpl.
        erewrite (proj1 (lower_fval_ext (@FMap.FMap _ _ ((Ordinal (n:=S (S n)) (m:=S m0) i1, s1) :: fmval) (path_sorted_tl i)) _ _ _) eq_refl).
        reflexivity.
Qed.


Lemma ord_gt : (forall {A : ordType} {x y : A}, ((x < y)%ord = false) -> eqtype.eq_op x y = false -> is_true (y < x)%ord).
Proof.
  clear ; intros.
  rewrite Ord.ltNge in H.
  apply ssrbool.negbFE in H.
  rewrite Ord.leq_eqVlt in H.
  rewrite LocationUtility.is_true_split_or in H.

  rewrite eqtype.eq_sym in H0.
  cbn in H.
  cbn in H0.
  rewrite H0 in H.
  destruct H ; [ discriminate | ].
  apply H.
Qed.

Lemma path_path_setm_move_lowerbound :
  forall {A : ordType} B v (y z : A * B) (l : list (A * B)),
  is_true (fst y < fst z)%ord ->
  is_true
    (path.sorted Ord.lt (seq.unzip1 (y :: l))) ->
  is_true
    (path.sorted Ord.lt (seq.unzip1 ((setm_def l (fst z) v)))) ->
  is_true
    (path.sorted Ord.lt (seq.unzip1 (y :: (setm_def l (fst z) v)))).
Proof.
  intros.
  generalize dependent y.
  destruct l ; intros.
  - cbn.
    now rewrite H.
  - cbn.
    cbn in H1.
    pose proof (path_sorted_tl H1).
    cbn in H1.
    set (fst z < fst p)%ord in *.
    destruct b eqn:b_lt ; subst b ; cbn in H1.
    + cbn.
      rewrite H.
      rewrite b_lt.
      cbn.
      rewrite H2.
      reflexivity.
    + destruct eqtype.eq_op eqn:b_eq ; cbn in H1.
      * cbn.
        rewrite H.
        cbn.
        rewrite H1.
        reflexivity.
      * pose proof (ord_gt b_lt b_eq).
        clear b_lt b_eq.
        cbn.
        rewrite H1.

        cbn in H0.
        rewrite LocationUtility.is_true_split_and in H0.
        destruct H0.
        rewrite H0.
        reflexivity.
Qed.

Lemma setm_def_cons :
  forall (A : ordType) B (a : A * B) s (k : A) v,
  setm_def (a :: s) k v = ((if (fst a < k)%ord
                           then a
                           else (k, v)
   ) :: if (k < fst a)%ord
       then a :: s
       else
         if eqtype.eq_op k (fst a)
         then s
         else setm_def (T:=A) s k v).
Proof.
  intros.
  cbn.
  destruct (k < fst a)%ord eqn:k_lt_a.
  - unfold Ord.lt in k_lt_a.
    apply (ssrbool.rwP ssrbool.andP) in k_lt_a.
    destruct k_lt_a.
    rewrite Ord.leqNgt in H.
    apply ssrbool.negbTE in H.
    rewrite H.
    reflexivity.
  - destruct eqtype.eq_op eqn:k_eq_a.
    + unfold Ord.lt.
      rewrite eqtype.eq_sym in k_eq_a.
      rewrite k_eq_a.
      cbn.
      rewrite Bool.andb_false_r.
      reflexivity.
    + rewrite Ord.ltNge in k_lt_a.
      apply ssrbool.negbFE in k_lt_a.
      unfold Ord.lt.
      rewrite k_lt_a.
      rewrite eqtype.eq_sym in k_eq_a.
      rewrite k_eq_a.
      reflexivity.
Qed.

Lemma setm_cons :
  forall (A : ordType) B (a : A * B) s (k : A) v H,
    setm (FMap.FMap (fmval:=(a :: s)) H) k v =
      setm (setm (FMap.FMap (fmval:=s) (path_sorted_tl H)) (fst a) (snd a)) k v.
Proof.
  intros.
  apply eq_fmap.
  intros t.
  rewrite !setmE.
  reflexivity.
Qed.

Lemma array_is_max_length {A : choice_type} {n} (a : (nseq_ A (S n))) : (length (FMap.fmval a) <= S n)%nat.
Proof.
  induction n.
  - destruct a.
    cbn.
    destruct fmval.
    + cbn. lia.
    + destruct fmval.
      * cbn. lia.
      * cbn in i.
        destruct p , p0.
        destruct s , s1.
        cbn in i.
        destruct m , m0 ; discriminate.
  - cbn in *.
    specialize (IHn (tl_fmap a)).
    apply le_n_S in IHn.
    refine (le_trans (length (FMap.fmval a)) _ (S (S n)) _ IHn).
    apply lower_fval_smaller_length.
Qed.


Definition nth_nseq_ {A : choice_type} {n} (a : (nseq_ A (S n))) (i : nat) (H : (i <= n)%nat) : A.
Proof.
  generalize dependent i.
  induction n ; intros.
  - apply (nseq_hd a).
  - destruct i.
    + apply (nseq_hd a).
    + apply (IHn (nseq_tl a) i).
      apply le_S_n.
      apply H.
Defined.

Equations array_to_list {A : choice_type} {n} (f : (nseq_ A n)) : list (A) :=
  array_to_list (n:=O%nat) f := [] ;
  array_to_list (n:=S _%nat) f := nseq_hd f :: array_to_list (nseq_tl f).
Fail Next Obligation.

Theorem array_to_length_list_is_len : forall (A : choice_type) len (x : nseq_ A len), List.length (array_to_list x) = len.
Proof.
  intros.
  induction len.
  - reflexivity.
  - rewrite array_to_list_equation_2.
    simpl.
    rewrite IHlen.
    reflexivity.
Defined.

Equations array_to_option_list {A : choice_type} {n} (f : (nseq_ A n)) : list (chOption A) :=
  array_to_option_list (n:=O%nat) f := [] ;
  array_to_option_list (n:=S _%nat) f := nseq_hd_option f :: array_to_option_list (nseq_tl f).
Fail Next Obligation.

Theorem array_to_length_option_list_is_len : forall (A : choice_type) len (x : nseq_ A len), List.length (array_to_option_list x) = len.
Proof.
  intros.
  induction len.
  - reflexivity.
  - rewrite array_to_option_list_equation_2.
    simpl.
    rewrite IHlen.
    reflexivity.
Defined.

Lemma nseq_hd_ord0 :
  forall A n (a : (nseq_ A (S n))) (x : A),
    @nseq_hd A (n) (setm a ord0 x) = x.
Proof.
  intros.
  cbn.
  destruct a.
  destruct fmval.
  + reflexivity.
  + cbn.
    destruct negb eqn:O_p.
    * reflexivity.
    * apply ssrbool.negbFE in O_p.
      rewrite O_p.
      reflexivity.
Qed.

Lemma nseq_tl_ord0 :
  forall A n (a : (nseq_ A (S n))) (x : A),
    @nseq_tl A n (setm a ord0 x) = nseq_tl a.
Proof.
  intros.
  destruct n.
  + reflexivity.
  + destruct a.
    induction fmval as [ | p ].
    * apply eq_fmap. intros ?.
      reflexivity.
    * destruct p, s.
      unfold setm.
      unfold fmap.
      unfold ord0.
      cbn.
      destruct m.

      -- cbn.
         rewrite !tl_fmap_equation_2.
         apply eq_fmap. intros ?.
         cbn.
         f_equal.
         now erewrite (proj1 (lower_fval_ext (@FMap.FMap _ _ fmval (path_sorted_tl i)) _ _ _) eq_refl).
      -- cbn.
         rewrite tl_fmap_equation_2.
         rewrite tl_fmap_equation_3.
         apply eq_fmap. intros ?.
         cbn.
         f_equal.
         now erewrite (proj1 (lower_fval_ext (@FMap.FMap _ _ ((Ordinal (n:=S (S n)) (m:=S m) i0, s0) :: fmval) i) _ _ _) eq_refl).
Qed.

Lemma array_to_list_ord0 :
  forall A n (a : (nseq_ A (S n))) (x : A),
    @array_to_list A (S n) (setm a ord0 x) = x :: array_to_list (nseq_tl a).
Proof.
  intros.
  rewrite array_to_list_equation_2.
  f_equal.
  - apply nseq_hd_ord0.
  - f_equal.
    apply nseq_tl_ord0.
Qed.

Lemma split_nseq_correct {A : choice_type} {n} (a : (nseq_ A (S n))) : nseq_hd a :: array_to_list (nseq_tl a) = array_to_list a.
Proof.
  reflexivity.
Qed.

Definition array_to_seq {A : choice_type} {n} (f : (nseq_ A n)) : (seq A) :=
  seq_from_list _ (array_to_list f).

Definition positive_slice {A : choice_type} {n} `{H: Positive n} (l : (nseq_ A n)) (i j : nat) `{H1: (i < j)%nat} `{(j - i < length (array_to_list l) - i)%nat} : Positive (length (slice (array_to_list l) i j)).
Proof.
  unfold slice.
  rewrite (proj2 (Nat.leb_gt j i) H1).
  rewrite firstn_length_le.
  - unfold Positive.
    apply (ssrbool.introT ssrnat.ltP).
    lia.
  - rewrite skipn_length.
    apply lt_n_Sm_le.
    lia.
Defined.

Theorem slice_length :
  forall A (l : list A) (i j : nat),
    length (slice l i j) =
      if (j <=? i)%nat then @length A ([]) else length (firstn (j - i + 1) (skipn i l)).
Proof.
  intros.
  unfold slice.
  destruct (j <=? i)%nat.
  - reflexivity.
  - reflexivity.
Qed.

Definition lseq_slice {A : choice_type} {n} (l : (nseq_ A n)) (i j : nat) :
  (@nseq_ A (length (slice (array_to_list l) (i) (j)))) :=
  array_from_list (slice (array_to_list l) (i) (j)).

Definition seq_sub {A : choice_type} (s : seq A) (start n : nat) :=
  lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) start (start + n)%nat.

Definition array_update_slice
           {A : choice_type}
           {l : nat}
           (out: ((nseq_ A l)))
           (start_out: uint_size)
           (input: seq A)
           (start_in: uint_size)
           (len: nat)
  : nseq_ A l :=
  update_sub out (from_uint_size start_out) (len) (seq_sub input (from_uint_size start_in) len).

Definition array_from_slice
           {A: choice_type}
           (default_value: A)
           (out_len: nat)
           (input: (seq A))
           (start: nat)
           (slice_len: nat)
  : (nseq_ A out_len) :=
  let out := array_new_ default_value out_len in
  array_from_seq out_len input.

Definition array_slice
           {A: choice_type}
           (input: (seq A))
           (start: nat)
           (slice_len: nat)
  : (nseq_ A slice_len) :=
  array_from_slice (chCanonical A) (slice_len) input (slice_len) (slice_len).

Definition array_from_slice_range
           {a: choice_type}
           (default_value: a)
           (out_len: nat)
           (input: (seq a))
           (start_fin: (uint_size * uint_size))
  : (nseq_ a out_len).
Proof.
  pose (out := array_new_ default_value (out_len)).
  destruct start_fin as [start fin].
  refine (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) _).

  apply (@lseq_slice a ((from_uint_size fin) - (from_uint_size start)) (array_from_seq ((from_uint_size fin) - (from_uint_size start)) input) (from_uint_size start) (from_uint_size fin)).
Defined.

Definition array_slice_range
           {a: choice_type}
           {len : nat}
           (input: (nseq_ a len))
           (start_fin:(uint_size * uint_size))
  : (seq a) :=
  array_to_seq (lseq_slice input (from_uint_size (fst start_fin)) (from_uint_size (snd start_fin))).

Definition array_update
           {a: choice_type}
           {len: nat}
           (s: (nseq_ a len))
           (start : uint_size)
           (start_s: (seq a))
  : (nseq_ a len) :=
  update_sub s (from_uint_size start) (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) (start_s)).

Definition array_update_start
           {a: choice_type}
           {len: nat}
           (s: (nseq_ a len))
           (start_s: (seq a))
  : (nseq_ a len) :=
  update_sub s 0 (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) start_s).


Definition array_len  {a: choice_type} {len: nat} (s: (nseq_ a len)) : uint_size := usize len.
(* May also come up as 'length' instead of 'len' *)
Definition array_length  {a: choice_type} {len: nat} (s: (nseq_ a len)) : uint_size := usize len.

(**** Seq manipulation *)

Definition seq_slice
           {a: choice_type}
           (s: ((seq a)))
           (start: (uint_size))
           (len: (uint_size))
  : (seq a) :=
  array_to_seq (lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) (from_uint_size start) ((from_uint_size start) + (from_uint_size len))).

Definition seq_slice_range
           {a: choice_type}
           (input: ((seq a)))
           (start_fin:(((uint_size)) * ((uint_size))))
  : ((seq a)) :=
  seq_slice input (fst start_fin) (snd start_fin).



Equations seq_update_sub {A : choice_type} (v : (seq A)) (i : nat) (n : nat) (sub : (seq A)) : (seq A) :=
  seq_update_sub v i 0 sub := v ;
  seq_update_sub v i (S n) sub :=
      seq_update_sub (setm v (i+n)%nat match getm sub n with
                                           | Some y => y
                                           | None => (chCanonical A)
                                           end) i n sub.

(* updating a subsequence in a sequence *)
Definition seq_update
           {a: choice_type}
           (s: ((seq a)))
           (start: uint_size)
           (input: ((seq a)))
  : ((seq a)) :=
  seq_update_sub s (from_uint_size start) (from_uint_size (seq_len input)) input.

Definition old_seq_update
  {a: choice_type}
           (s: ((seq a)))
           (start: uint_size)
           (input: ((seq a)))
  : ((seq a)) :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) (from_uint_size start) (from_uint_size (seq_len input)) (array_from_seq (from_uint_size (seq_len input)) input)).

(* updating only a single value in a sequence*)
Definition seq_upd
           {a: choice_type}
           (s: ((seq a)))
           (start: uint_size)
           (v: ((a)))
  : ((seq a)) :=
  seq_update s start (setm emptym 0%nat v).

Definition seq_update_start
           {a: choice_type}
           (s: ((seq a)))
           (start_s: ((seq a)))
  : ((seq a)) :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) 0 (from_uint_size (seq_len start_s)) (array_from_seq (from_uint_size (seq_len start_s)) start_s)).

Definition seq_update_slice
           {A : choice_type}
           (out: seq A)
           (start_out: nat)
           (input: seq A)
           (start_in: nat)
           (len: nat)
  : ((seq A))
  :=
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len out)) out) start_out len (seq_sub input start_in len)).

Definition seq_concat
           {A : choice_type}
           (s1 :seq A)
           (s2: seq A)
  : ((seq A)) :=
  seq_from_list _ (seq_to_list _ s1 ++ seq_to_list _ s2).

Definition seq_concat_owned
           {A : choice_type}
           (s1 :seq A)
           (s2: seq A)
  : ((seq A)) := seq_concat s1 s2.

Definition seq_push
           {A : choice_type}
           (s1 :seq A)
           (s2: ((A)))
  : ((seq A)) :=
  setm s1 (seq_len_nat s1) s2.

Theorem seq_push_list_app : forall {A : choice_type} (t : (seq A)) (s : A),
    (seq_to_list A (Hacspec_Lib_Pre.seq_push t s) = seq_to_list A t ++ [s]).
Proof.
  intros.

  unfold seq_push.
  rewrite seq_to_list_setm.
  reflexivity.
Qed.

Definition seq_push_owned
           {a : choice_type}
           (s1 :((seq a)))
           (s2: ((a)))
  : ((seq a)) := seq_push s1 s2.

Definition seq_from_slice
           {A: choice_type}
           (input: ((seq A)))
           (start_fin: (((uint_size)) * ((uint_size))))
  : ((seq A)) :=
  let out := array_new_ ((chCanonical A)) (from_uint_size (seq_len input)) in
  let (start, fin) := start_fin in
  array_to_seq (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) ((lseq_slice (array_from_seq (from_uint_size (seq_len input)) input) (from_uint_size start) (from_uint_size fin)))).

Definition seq_from_slice_range
           {A: choice_type}
           (input: ((seq A)))
           (start_fin: (((uint_size)) * ((uint_size))))
  : ((seq A)) :=
  let out := array_new_ (chCanonical A) (from_uint_size (seq_len input)) in
  let (start, fin) := start_fin in
  array_to_seq (update_sub out 0 ((from_uint_size fin) - (from_uint_size start)) ((lseq_slice (array_from_seq (from_uint_size (seq_len input)) input) (from_uint_size start) (from_uint_size fin)))).

Definition seq_from_seq {A} (l : (seq A)) : (seq A) := l.

(**** Chunking *)

Definition seq_num_chunks {a: choice_type} (s: ((seq a))) (chunk_len: uint_size) : uint_size :=
  ((seq_len s .+ chunk_len .- one) ./ chunk_len)%nat.

Definition seq_chunk_len
           {a: choice_type}
           (s: ((seq a)))
           (chunk_len: nat)
           (chunk_num: nat)
  : 'nat :=
  let idx_start := (chunk_len * chunk_num)%nat in
  if ((from_uint_size (seq_len s)) <.? (idx_start + chunk_len))%nat then
    ((from_uint_size (seq_len s)) - idx_start)%nat
  else
    chunk_len.

Definition seq_get_chunk
           {a: choice_type}
           (s: ((seq a)))
           (chunk_len: uint_size)
           (chunk_num: uint_size)
  : (((uint_size × seq a)))
  :=
  let idx_start := (from_uint_size chunk_len * from_uint_size chunk_num)%nat in
  let out_len := seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num) in
  (usize out_len, array_to_seq (lseq_slice (array_from_seq (from_uint_size (seq_len s)) s) idx_start (idx_start + seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num)))).

Definition seq_set_chunk
           {a: choice_type}
           (s: ((seq a)))
           (chunk_len: uint_size)
           (chunk_num: uint_size)
           (chunk: ((seq a)) ) : ((seq a)) :=
  let idx_start := (from_uint_size chunk_len * from_uint_size chunk_num)%nat in
  let out_len := seq_chunk_len s (from_uint_size chunk_len) (from_uint_size chunk_num) in
  array_to_seq (update_sub (array_from_seq (from_uint_size (seq_len s)) s) idx_start out_len (array_from_seq (from_uint_size (seq_len chunk)) chunk)).


Definition seq_num_exact_chunks {a} (l : ((seq a))) (chunk_size : ((uint_size))) : ((uint_size)) :=
  (repr _ (Z.of_nat (length l))) ./ chunk_size.

Definition seq_get_exact_chunk {a : choice_type} (l : ((seq a))) (chunk_size chunk_num: ((uint_size))) : ((seq a)) :=
  let '(len, chunk) := seq_get_chunk l chunk_size chunk_num in
  if eqtype.eq_op len chunk_size then emptym else chunk.

Definition seq_set_exact_chunk {A : choice_type} :=
  @seq_set_chunk A.

Definition seq_get_remainder_chunk {a : choice_type} (l : (seq a)) (chunk_size : uint_size) : (seq a) :=
  let chunks := seq_num_chunks l chunk_size in
  let last_chunk := if (zero <.? chunks)
                    then (chunks .- one)%nat
                    else zero in
  let (len, chunk) := seq_get_chunk l chunk_size last_chunk in
  if eqtype.eq_op len chunk_size
  then emptym
  else chunk.

Fixpoint list_xor_ {WS} (x y : list ((@int WS))) : list ((@int WS)) :=
  match x, y with
  | (x :: xs), (y :: ys) => (int_xor x y) :: (list_xor_ xs ys)
  | [] , _ => y
  | _, [] => x
  end.

Definition seq_xor_ {WS} (x y : (seq (@int WS))) : (seq (@int WS)) :=
  seq_from_list _ (list_xor_ (seq_to_list _ x) (seq_to_list _ y)).
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

Fixpoint list_truncate {a} (x : list a) (n : nat) : list a :=
  match x, n with
  | _, O => []
  | [], _ => []
  | (x :: xs), S n' => x :: (list_truncate xs n')
  end.
Definition seq_truncate {a : choice_type} (x : (seq a)) (n : nat) : (seq a) :=
  seq_from_list _ (list_truncate (seq_to_list _ x) n).

(**** Numeric operations *)

(* takes two nseq's and joins them using a function op : a -> a -> a *)
Definition array_join_map
           {a: choice_type}
           {len: nat}
           (op: ((a)) -> ((a)) -> ((a)))
           (s1: ((nseq_ a len)))
           (s2 : ((nseq_ a len))) :=
  let out := s1 in
  foldi (usize 0%nat) (usize len) (fun i out =>
                                       array_upd out i (op (array_index s1 i) (array_index s2 i))
                                    ) out.

Infix "array_xor" := (array_join_map (a := int _) int_xor) (at level 33) : hacspec_scope.
Infix "array_add" := (array_join_map (a := int _) int_add) (at level 33) : hacspec_scope.
Infix "array_minus" := (array_join_map (a := int _) int_sub) (at level 33) : hacspec_scope.

Infix "array_mul" := (array_join_map (a := int _) int_mul) (at level 33) : hacspec_scope.
Infix "array_div" := (array_join_map (a := int _) int_div) (at level 33) : hacspec_scope.
Infix "array_or" := (array_join_map (a := int _) int_or) (at level 33) : hacspec_scope.
Infix "array_and" := (array_join_map (a := int _) int_and) (at level 33) : hacspec_scope.

Fixpoint array_eq_
         {a: choice_type}
         {len: nat}
         (eq: ((a)) -> ((a)) -> bool)
         (s1: ((nseq_ a len)))
         (s2 : ((nseq_ a len)))
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

Infix "array_eq" := (array_eq_ eq) (at level 33) : hacspec_scope.
Infix "array_neq" := (fun s1 s2 => negb (array_eq_ eq s1 s2)) (at level 33) : hacspec_scope.




(*** Nats *)


Definition nat_mod (p : Z) : choice_type := 'fin (S (Init.Nat.pred (Z.to_nat p))).
(* Definition nat_mod_type {p : Z} : Type := 'I_(S (Init.Nat.pred (Z.to_nat p))). *)
Definition mk_natmod {p} (z : Z) : (nat_mod p) := @zmodp.inZp (Init.Nat.pred (Z.to_nat p)) (Z.to_nat z).

Definition nat_mod_equal {p} (a b : (nat_mod p)) : bool :=
  @eqtype.eq_op (fintype_ordinal__canonical__eqtype_Equality (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (@nat_mod_equal p a b) :=
  @eqtype.eqP (fintype_ordinal__canonical__eqtype_Equality (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_zero {p} : (nat_mod p) := zmodp.Zp0.
Definition nat_mod_one {p} : (nat_mod p) := zmodp.Zp1.
Definition nat_mod_two {p} : (nat_mod p) := zmodp.inZp 2.

Definition nat_mod_add {n : Z} (a : (nat_mod n)) (b : (nat_mod n)) : (nat_mod n) := zmodp.Zp_add a b.

Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.

Definition nat_mod_mul {n : Z} (a:(nat_mod n)) (b:(nat_mod n)) : (nat_mod n) := zmodp.Zp_mul a b.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.

Definition nat_mod_sub {n : Z} (a:(nat_mod n)) (b:(nat_mod n)) : (nat_mod n) := zmodp.Zp_add a (zmodp.Zp_opp b).
Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope.

Definition nat_mod_div {n : Z} (a:(nat_mod n)) (b:(nat_mod n)) : (nat_mod n) := zmodp.Zp_mul a (zmodp.Zp_inv b).
Infix "/%" := nat_mod_div (at level 33) : hacspec_scope.

Definition nat_mod_neg {n : Z} (a:(nat_mod n)) : (nat_mod n) := zmodp.Zp_opp a.

Definition nat_mod_inv {n : Z} (a:(nat_mod n)) : (nat_mod n) := zmodp.Zp_inv a.

Definition nat_mod_exp_def {p : Z} (a:(nat_mod p)) (n : nat) : (nat_mod p) :=
  let fix exp_ (e : (nat_mod p)) (n : nat) :=
    match n with
    | 0%nat => nat_mod_one
    | S n => nat_mod_mul a (exp_ a n)
    end in
  exp_ a n.

Definition nat_mod_exp {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_felem {p} a n := @nat_mod_exp_def p a (Z.to_nat (from_uint_size n)).
Definition nat_mod_pow_self {p} a n := @nat_mod_pow_felem p a n.

Close Scope nat_scope.

Definition nat_mod_from_secret_literal {m : Z} (x:int128) : (nat_mod m) := @zmodp.inZp (Init.Nat.pred (Z.to_nat m)) (Z.to_nat (unsigned x)).

Definition nat_mod_from_literal (m : Z) (x:int128) : (nat_mod m) := nat_mod_from_secret_literal x.

Axiom nat_mod_to_byte_seq_le : forall {n : Z}, (nat_mod n) -> (seq int8).
Axiom nat_mod_to_byte_seq_be : forall {n : Z}, (nat_mod n) -> (seq int8).
Axiom nat_mod_to_public_byte_seq_le : forall (n : Z), (nat_mod n) -> (seq int8).
Axiom nat_mod_to_public_byte_seq_be : forall (n : Z), (nat_mod n) -> (seq int8).

Definition nat_mod_val (p : Z) (a : (nat_mod p)) : Z := Z.of_nat (nat_of_ord a).

Definition nat_mod_bit {n : Z} (a : (nat_mod n)) (i : uint_size) : 'bool :=
  Z.testbit (nat_mod_val _ a) (from_uint_size i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : (nat_mod p)) := nat_mod_bit a.
Definition nat_mod_get_bit {p} (a : (nat_mod p)) n :=
  if (nat_mod_bit a n)
  then @nat_mod_one p
  else @nat_mod_zero p.

Axiom array_declassify_eq : forall  {A l}, (nseq_ A l) -> (nseq_ A l) -> 'bool.
Axiom array_to_le_uint32s : forall {A l}, (nseq_ A l) -> (seq uint32).
Axiom array_to_be_uint32s : forall {l}, (nseq_ uint8 l) -> (seq uint32).
Axiom array_to_le_uint64s : forall {A l}, (nseq_ A l) -> (seq uint64).
Axiom array_to_be_uint64s : forall {l}, (nseq_ uint8 l) -> (seq uint64).
Axiom array_to_le_uint128s : forall {A l}, (nseq_ A l) -> (seq uint128).
Axiom array_to_be_uint128s : forall {l}, (nseq_ uint8 l) -> (seq uint128).
Axiom array_to_le_bytes : forall {A l}, (nseq_ A l) -> (seq uint8).
Axiom array_to_be_bytes : forall {A l}, (nseq_ A l) -> (seq uint8).
Axiom nat_mod_from_byte_seq_le : forall  {A n}, (seq A) -> (nat_mod n).
Axiom most_significant_bit : forall {m}, (nat_mod m) -> uint_size -> uint_size.


(* We assume 2^x < m *)
Definition nat_mod_pow2 (m : Z) (x : N) : (nat_mod m) := mk_natmod (Z.pow 2 (Z.of_N x)).


Section Casting.

  (* Type casts, as defined in Section 4.5 in https://arxiv.org/pdf/1106.3448.pdf *)
  Class Cast A B := cast : A -> B.

  Arguments cast {_} _ {_}.

  Notation "' x" := (cast _ x) (at level 20) : hacspec_scope.

  (* Casting to self is always possible *)
  Global Instance cast_self {A} : Cast A A := {
      cast a := a
    }.

  Global Instance cast_transitive {A B C} `{Hab: Cast A B} `{Hbc: Cast B C} : Cast A C := {
      cast a := Hbc (Hab a)
    }.

  Global Instance cast_prod {A B C D} `{Cast A B} `{Cast C D} : Cast (A * C) (B * D) := {
      cast '(a, c) := (cast _ a, cast _ c)
    }.

  Global Instance cast_option {A B} `{Cast A B} : Cast (option A) (option B) := {
      cast a := match a with Some a => Some (cast _ a) | None => None end
    }.

  Global Instance cast_option_b {A B} `{Cast A B} : Cast A (option B) := {
      cast a := Some (cast _ a)
    }.

  (* Global Instances for common types *)

  Global Instance cast_nat_to_N : Cast nat N := {
      cast := N.of_nat
    }.

  Global Instance cast_N_to_Z : Cast N Z := {
      cast := Z.of_N
    }.

  Global Instance cast_Z_to_int {WORDSIZE} : Cast Z ((@int WORDSIZE)) := {
      cast n := repr _ n
    }.

  Global Instance cast_natmod_to_Z {p} : Cast ((nat_mod p)) Z := {
      cast n := nat_mod_val _ n
    }.

  (* Note: should be aware of typeclass resolution with int/uint since they are just aliases of each other currently *)
  Global Instance cast_int8_to_uint32 : Cast (int8) (uint32) := {
      cast n := repr _ (unsigned n)
    }.
  Global Instance cast_int8_to_int32 : Cast (int8) (int32) := {
      cast n := repr _ (signed n)
    }.

  Global Instance cast_uint8_to_uint32 : Cast (uint8) (uint32) := {
      cast n := repr _ (unsigned n)
    }.

  Global Instance cast_int_to_nat `{WS : wsize} : Cast (int _) nat := {
      cast n := Z.to_nat (@signed WS n)
    }.

  Close Scope hacspec_scope.
End Casting.


Global Arguments pair {_ _} & _ _.

Section Coercions.
  (* First, in order to have automatic coercions for tuples, we add bidirectionality hints: *)

  Global Coercion N.to_nat : N >-> nat.
  Global Coercion Z.of_N : N >-> Z.

  Definition Z_to_int `{WS : wsize} (n : Z) : (int WS) := repr _ n.
  Global Coercion  Z_to_int : Z >-> choice.Choice.sort.

  Definition Z_to_uint_size (n : Z) : uint_size := repr _ n.
  Global Coercion Z_to_uint_size : Z >-> choice.Choice.sort.
  Definition Z_to_int_size (n : Z) : int_size := repr _ n.
  Global Coercion Z_to_int_size : Z >-> choice.Choice.sort.

  Definition N_to_int `{WS : wsize} (n : N) : (@int WS) := repr _ (Z.of_N n).
  Global Coercion N.of_nat : nat >-> N.
  Global Coercion N_to_int : N >-> choice.Choice.sort.
  Definition N_to_uint_size (n : Z) : uint_size := repr _ n.
  Global Coercion N_to_uint_size : Z >-> choice.Choice.sort.
  Definition nat_to_int `{WS : wsize} (n : nat) : (@int WS) := repr _ (Z.of_nat n).
  Global Coercion nat_to_int : nat >-> choice.Choice.sort.

  Definition uint_size_to_nat (n : uint_size) : nat := from_uint_size n.
  Global Coercion uint_size_to_nat : choice.Choice.sort >-> nat.

  Definition uint_size_to_Z (n : uint_size) : Z := from_uint_size n.
  Global Coercion uint_size_to_Z : choice.Choice.sort >-> Z.

  Definition uint32_to_nat (n : uint32) : nat := Z.to_nat (unsigned n).
  Global Coercion uint32_to_nat : choice.Choice.sort >-> nat.

  Definition int8_to_nat (n : int8) : nat := Z.to_nat (unsigned n).
  Global Coercion int8_to_nat : choice.Choice.sort >-> nat.
  Definition int16_to_nat (n : int16) : nat := Z.to_nat (unsigned n).
  Global Coercion int16_to_nat : choice.Choice.sort >-> nat.
  Definition int32_to_nat (n : int32) : nat := Z.to_nat (unsigned n).
  Global Coercion int32_to_nat : choice.Choice.sort >-> nat.
  Definition int64_to_nat (n : int64) : nat := Z.to_nat (unsigned n).
  Global Coercion int64_to_nat : choice.Choice.sort >-> nat.
  Definition int128_to_nat (n : int128) : nat := Z.to_nat (unsigned n).
  Global Coercion int128_to_nat : choice.Choice.sort >-> nat.

  Definition int8_to_int16 (n : int8) : int16 := (repr _ (unsigned n)).
  Global Coercion int8_to_int16 : choice.Choice.sort >-> choice.Choice.sort.

  Definition int8_to_int32 (n : int8) : int32 := repr _ (unsigned n).
  Global Coercion int8_to_int32 : choice.Choice.sort >-> choice.Choice.sort.

  Definition int16_to_int32 (n : int16) : int32 := repr _ (unsigned n).
  Global Coercion int16_to_int32 : choice.Choice.sort >-> choice.Choice.sort.

  Definition int32_to_int64 (n : int32) : int64 := repr _ (unsigned n).
  Global Coercion int32_to_int64 : choice.Choice.sort >-> choice.Choice.sort.

  Definition int64_to_int128 (n : int64) : int128 := repr _ (unsigned n).
  Global Coercion int64_to_int128 : choice.Choice.sort >-> choice.Choice.sort.

  Definition int32_to_int128 (n : int32) : int128 := repr _ (unsigned n).
  Global Coercion int32_to_int128 : choice.Choice.sort >-> choice.Choice.sort.

  Definition uint_size_to_int64 (n : uint_size) : int64 := repr _ (unsigned n).
  Global Coercion uint_size_to_int64 : choice.Choice.sort >-> choice.Choice.sort.

  Definition Z_in_nat_mod {m : Z} (x:Z) : (@nat_mod m) := @mk_natmod m x.

  Definition int_in_nat_mod {m : Z} `{WS : wsize} (x:(@int WS)) : (@nat_mod m) := mk_natmod (unsigned x).
  Global Coercion int_in_nat_mod : choice.Choice.sort >-> choice.Choice.sort.

  Definition nat_mod_in_int {m : Z} `{WS : wsize} (x:(@nat_mod m)) : (@int WS) := (repr _ (nat_mod_val _ x)).
  Global Coercion nat_mod_in_int : choice.Choice.sort >-> choice.Choice.sort.

  Definition nat_mod_in_Z {m : Z} `{WS : wsize} (x:(@nat_mod m)) : Z := (nat_mod_val _ x).
  Global Coercion nat_mod_in_Z : choice.Choice.sort >-> Z.

  Definition uint_size_in_nat_mod (n : uint_size) : (@nat_mod 16) := (int_in_nat_mod n).
  Global Coercion uint_size_in_nat_mod : choice.Choice.sort >-> choice.Choice.sort.

End Coercions.


(*** Casting *)

Definition uint128_from_usize (n : uint_size) : int128 := repr _ (unsigned n).
Definition uint64_from_usize (n : uint_size) : int64 := repr _ (unsigned n).
Definition uint32_from_usize (n : uint_size) : int32 := repr _ (unsigned n).
Definition uint16_from_usize (n : uint_size) : int16 := repr _ (unsigned n).
Definition uint8_from_usize (n : uint_size) : int8 := repr _ (unsigned n).

Definition uint128_from_uint8 (n : int8) : int128 := repr _ (unsigned n).
Definition uint64_from_uint8 (n : int8) : int64 := repr _ (unsigned n).
Definition uint32_from_uint8 (n : int8) : int32 := repr _ (unsigned n).
Definition uint16_from_uint8 (n : int8) : int16 := repr _ (unsigned n).
Definition usize_from_uint8 (n : int8) : uint_size := repr _ (unsigned n).

Definition uint128_from_uint16 (n : int16) : int128 := repr _ (unsigned n).
Definition uint64_from_uint16 (n : int16) : int64 := repr _ (unsigned n).
Definition uint32_from_uint16 (n : int16) : int32 := repr _ (unsigned n).
Definition uint8_from_uint16 (n : int16) : int8 := repr _ (unsigned n).
Definition usize_from_uint16 (n : int16) : uint_size := repr _ (unsigned n).

Definition uint128_from_uint32 (n : int32) : int128 := repr _ (unsigned n).
Definition uint64_from_uint32 (n : int32) : int64 := repr _ (unsigned n).
Definition uint16_from_uint32 (n : int32) : int16 := repr _ (unsigned n).
Definition uint8_from_uint32 (n : int32) : int8 := repr _ (unsigned n).
Definition usize_from_uint32 (n : int32) : uint_size := repr _ (unsigned n).

Definition uint128_from_uint64 (n : int64) : int128 := repr _ (unsigned n).
Definition uint32_from_uint64 (n : int64) : int32 := repr _ (unsigned n).
Definition uint16_from_uint64 (n : int64) : int16 := repr _ (unsigned n).
Definition uint8_from_uint64 (n : int64) : int8 := repr _ (unsigned n).
Definition usize_from_uint64 (n : int64) : uint_size := repr _ (unsigned n).

Definition uint64_from_uint128 (n : int128) : int64 := repr _ (unsigned n).
Definition uint32_from_uint128 (n : int128) : int32 := repr _ (unsigned n).
Definition uint16_from_uint128 (n : int128) : int16 := repr _ (unsigned n).
Definition uint8_from_uint128 (n : int128) : int8 := repr _ (unsigned n).
Definition usize_from_uint128 (n : int128) : uint_size := repr _ (unsigned n).


Definition uint8_equal : int8 -> int8 -> bool := eqb.

Theorem nat_mod_eqb_spec : forall {p} (a b : (nat_mod p)), nat_mod_equal a b = true <-> a = b.
Proof.
  symmetry ; exact (ssrbool.rwP nat_mod_equal_reflect).
Qed.

Global Instance nat_mod_eqdec {p} : EqDec ((nat_mod p)) := {
    eqb := nat_mod_equal ;
    eqb_leibniz := nat_mod_eqb_spec;
  }.

Global Instance nat_mod_comparable `{p : Z} : Comparable ((nat_mod p)) := {
    ltb a b := Z.ltb (nat_mod_val p a) (nat_mod_val p b);
    leb a b := if Zeq_bool (nat_mod_val p a) (nat_mod_val p b) then true else Z.ltb (nat_mod_val p a) (nat_mod_val p b) ;
    gtb a b := Z.ltb (nat_mod_val p b) (nat_mod_val p a);
    geb a b := if Zeq_bool (nat_mod_val p b) (nat_mod_val p a) then true else Z.ltb (nat_mod_val p b) (nat_mod_val p a) ;
  }.

Fixpoint nat_mod_rem_aux {n : Z} (a:(nat_mod n)) (b:(nat_mod n)) (f : nat) {struct f} : (nat_mod n) :=
  match f with
  | O => a
  | S f' =>
      if geb a b
      then nat_mod_rem_aux (nat_mod_sub a b) b f'
      else a
  end.

Definition nat_mod_rem {n : Z} (a:(nat_mod n)) (b:(nat_mod n)) : (nat_mod n) :=
  if nat_mod_equal b nat_mod_zero
  then nat_mod_one
  else nat_mod_rem_aux a b (S (Z.to_nat (nat_mod_val n (nat_mod_div a b)))).

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

Global Program Instance Dec_eq_prod (A B : Type) `{EqDec A} `{EqDec B} : EqDec (A * B) := {
    eqb '(a0, b0) '(a1, b1) := andb (eqb a0 a1) (eqb b0 b1)
  }.
Next Obligation.
  split ; intros ; destruct x ; destruct y.
  - rewrite LocationUtility.is_true_split_and in H1. destruct H1.
    rewrite (eqb_leibniz) in H1.
    rewrite (eqb_leibniz) in H2.
    rewrite H1. rewrite H2. reflexivity.
  - inversion_clear H1. now do 2 rewrite eqb_refl.
Defined.

(*** Be Bytes *)


Fixpoint nat_be_range_at_position (k : nat) (z : Z) (n : Z) : list bool :=
  match k with
  | O => []
  | S k' => Z.testbit z (n + k') :: nat_be_range_at_position k' z n
  end.

Fixpoint nat_be_range_to_position_ (z : list bool) (val : Z) : Z :=
  match z with
  | [] => val
  | x :: xs => nat_be_range_to_position_ xs ((if x then 2 ^ List.length xs else 0) + val)
  end.

Definition nat_be_range_to_position (k : nat) (z : list bool) (n : Z) : Z :=
  (nat_be_range_to_position_ z 0 * 2^(k * n)).

Definition nat_be_range' (k : nat) (z : Z) (n : nat) : Z :=
  nat_be_range_to_position_ (nat_be_range_at_position k z (n * k)) 0.

Definition nat_be_range (k : nat) (z : Z) (n : nat) :=
  ((z / 2 ^ (n * k)%Z) mod 2 ^ k)%Z.

Definition to_be_bytes' {WS} : Z -> list Z :=
  (fun (k : Z) =>
     (map
        (fun i : nat => nat_be_range 8 k i)
        (seq.iota 0 (nat_of_wsize WS / 8)))).

Definition to_be_bytes'' {WS} : Z -> list Z :=
  (fun (k : Z) =>
     (map
        (fun i : nat => nat_be_range' 8 k i)
        (seq.iota 0 (nat_of_wsize WS / 8)))).

Definition to_be_bytes {WS} : (@int WS) -> (nseq_ int8 (WS / 8)) :=
  (fun (k : int _) =>
     eq_rect
       (seq.size (seq.iota 0 (nat_of_wsize WS / 8)))
       (fun n : nat => (nseq_ uint8 n))
       (eq_rect _ (fun n : nat => (nseq_ uint8 n))
                (array_from_list
                                 (map
                                    (fun i : nat => repr _ (nat_be_range 8 (toword k) i) : int _)
                                    (seq.iota 0 (nat_of_wsize WS / 8))))
                (length (seq.iota 0 (nat_of_wsize WS / 8)))
                (map_length
                   (fun i : nat =>
                      repr _ (nat_be_range 8 (toword k) i))
                   (seq.iota 0 (nat_of_wsize WS / 8))))
       (nat_of_wsize WS / 8)%nat
       (seq.size_iota 0 (nat_of_wsize WS / 8))).

Definition from_be_bytes_fold_fun {WS} (i : int8) (s : ('nat × @int WS)) : ('nat × @int WS) :=
  let (n,v) := s in
  (S n, v .+ (repr WS (int8_to_nat i * (2 ^ (8 * Z.of_nat n)))%Z)).

Definition from_be_bytes {WS : wsize} : (nseq_ int8 (WS / 8)) -> (@int WS) :=
   (fun v => snd (List.fold_right from_be_bytes_fold_fun (0%nat, @repr WS 0%Z) (array_to_list v))).

Definition to_le_bytes' {WS} : Z -> list Z :=
  (fun (k : Z) =>
     (map
        (fun i : nat => nat_be_range 8 k i)
        (rev (seq.iota 0 (nat_of_wsize WS / 8))))).

Definition to_le_bytes'' {WS} : Z -> list Z :=
  (fun (k : Z) =>
     (map
        (fun i : nat => nat_be_range' 8 k i)
        (rev (seq.iota 0 (nat_of_wsize WS / 8))))).

Definition to_le_bytes {WS} : (@int WS) -> (nseq_ int8 (WS / 8)) :=
  fun (k : int _) =>
   eq_rect (seq.size (seq.iota 0 (nat_of_wsize WS / 8))) (fun n : nat => (nseq_ uint8 n))
     (eq_rect (length (rev (seq.iota 0 (nat_of_wsize WS / 8))))
     (fun n : nat => (nseq_ uint8 n)) (eq_rect
     (length
        (map
           (fun i : nat =>
            repr _ (nat_be_range 8 (toword k) i))
           (rev (seq.iota 0 (nat_of_wsize WS / 8)))))
     (fun n : nat => (nseq_ uint8 n)) (array_from_list
     (map
        (fun i : nat =>
         repr _ (nat_be_range 8 (toword k) i))
        (rev (seq.iota 0 (nat_of_wsize WS / 8)))))
     (length (rev (seq.iota 0 (nat_of_wsize WS / 8))))
     (map_length
        (fun i : nat =>
         repr _ (nat_be_range 8 (toword k) i))
        (rev (seq.iota 0 (nat_of_wsize WS / 8))))) (length (seq.iota 0 (nat_of_wsize WS / 8)))
     (rev_length (seq.iota 0 (nat_of_wsize WS / 8)))) (nat_of_wsize WS / 8)%nat (seq.size_iota 0 (nat_of_wsize WS / 8)).

Definition from_le_bytes_fold_fun {WS} (i : int8) (s : ('nat × @int WS)) : ('nat × @int WS) :=
  let (n,v) := s in
  (Nat.pred n, v .+ (@repr WS ((int8_to_nat i) * 2 ^ (8 * Z.of_nat n))%Z)).

Definition from_le_bytes {WS : wsize} : (nseq_ int8 (WS / 8)) -> (@int WS) :=
   (fun v => snd (List.fold_right from_be_bytes_fold_fun (((WS / 8) - 1)%nat, @repr WS 0%Z) (array_to_list v))).

(**** Integers to arrays *)
Definition uint32_to_le_bytes : int32 -> (nseq_ int8 4) := @to_le_bytes U32.
Definition uint32_to_be_bytes : int32 -> (nseq_ int8 4) := @to_be_bytes U32.
Definition uint32_from_le_bytes : (nseq_ int8 4) -> int32 := @from_le_bytes U32.
Definition uint32_from_be_bytes : (nseq_ int8 4) -> int32 := @from_be_bytes U32.

Definition uint64_to_le_bytes : int64 -> (nseq_ int8 8) := @to_le_bytes U64.
Definition uint64_to_be_bytes : int64 -> (nseq_ int8 8) := @to_be_bytes U64.
Definition uint64_from_le_bytes : (nseq_ int8 8) -> int64 := @from_le_bytes U64.
Definition uint64_from_be_bytes : (nseq_ int8 8) -> int64 := @from_be_bytes U64.

Definition uint128_to_le_bytes : int128 -> (nseq_ int8 16) := @to_le_bytes U128.
Definition uint128_to_be_bytes : int128 -> (nseq_ int8 16) := @to_be_bytes U128.
Definition uint128_from_le_bytes : (nseq_ int8 16) -> int128 := @from_le_bytes U128.
Definition uint128_from_be_bytes : (nseq_ int8 16) -> int128 := @from_be_bytes U128.

Definition u32_to_be_bytes : int32 -> (nseq_ int8 4) := @to_be_bytes U32.
Definition u32_from_be_bytes : (nseq_ int8 4) -> int32 := @from_be_bytes U32.
Definition u32_to_le_bytes : int32 -> (nseq_ int8 4) := @to_le_bytes U32.
Definition u32_from_le_bytes : (nseq_ int8 4) -> int32 := @from_le_bytes U32.

Definition u64_to_be_bytes : int64 -> (nseq_ int8 8) := @to_be_bytes U64.
Definition u64_from_be_bytes : (nseq_ int8 8) -> int64 := @from_be_bytes U64.
Definition u64_to_le_bytes : int64 -> (nseq_ int8 8) := @to_le_bytes U64.
Definition u64_from_le_bytes : (nseq_ int8 8) -> int64 := @from_le_bytes U64.

Definition u128_to_be_bytes : int128 -> (nseq_ int8 16) := @to_be_bytes U128.
Definition u128_from_be_bytes : (nseq_ int8 16) -> int128 := @from_be_bytes U128.
Definition u128_to_le_bytes : int128 -> (nseq_ int8 16) := @to_le_bytes U128.
Definition u128_from_le_bytes : (nseq_ int8 16) -> int128 := @from_le_bytes U128.

(*** Result *)

Definition result (b a : choice_type) := chSum a b.
(* #[global] #[refine] Instance result (b a : choice_type) : choice_type := *)
(*   {| ct := chSum a b ; := (a + b)%type |}. *)
(* Proof. *)
(*   intros. *)
(*   cbn. *)
(*   do 2 rewrite ChoiceEq. *)
(*   reflexivity. *)
(* Defined. *)

Definition Ok {a b : choice_type} : a -> (result b a) := @inl (a) (b).
Definition Err {a b : choice_type} : b -> (result b a) := @inr (a) (b).

Arguments Ok {_ _}.
Arguments Err {_ _}.

Definition result_unwrap_safe {a b} (x : (result b a)) `{match x with inl _ => True | inr _ => False end} : a.
  destruct x.
  apply s.
  contradiction.
Defined.
Axiom falso : False. Ltac admit_falso := destruct falso.
Definition result_unwrap {a b} (x : (result b a)) : a :=
  result_unwrap_safe x (H := ltac:(admit_falso)).

Definition option := chOption.
(* Program Definition option_choice_type (a : choice_type) := *)
(*   {| ct := chOption a ; := option a ; |}. *)
(* Next Obligation. *)
(*   intros. *)
(*   rewrite ChoiceEq. *)
(*   reflexivity. *)
(* Qed. *)

(*** Monad / Bind *)

Module choice_typeMonad.
  Class CEMonad : Type :=
    {
      M :> choice_type -> choice_type ;
      bind {A B : choice_type} (x : (M A)) (f : A -> (M B)) : (M B) ;
      ret {A : choice_type} (x : A) : (M A) ;
      monad_law1 : forall {A B : choice_type} a (f : A -> M B),
        bind (ret a) f = f a ;
      monad_law2 : forall {A : choice_type} c, bind c (@ret A) = c ;
      monad_law3 : forall {A B C : choice_type} c (f : A -> M B) (g : B -> M C),
          bind (bind c f) g
          = bind c (fun a => bind (f a) g)
    }.

  (* Class CEMonad2 (M : choice_type -> choice_type) : Type := *)
  (*   { *)
  (*     unit {A : choice_type} (x : A) : (M A) ; *)
  (*     fmap {A B : choice_type} (f : A -> B) (x : (M A)) : (M B) ; *)
  (*     join {A : choice_type} (x : (M (M A))) : (M A) ; *)
  (*   }. *)

  (* #[global] Instance CEMonadToCEMonad2 `{CEMonad} : CEMonad2 M := *)
  (*   {| *)
  (*     unit A := @ret M _ A ; *)
  (*     fmap A B f x := bind x (fun y => ret (f y)) ; *)
  (*     join A x := bind x id *)
  (*   |}. *)

  (* #[global] Instance CEMonad2ToCEMonad `{CEMonad2} : CEMonad M := *)
  (*   {| *)
  (*     ret A := @unit M _ A ; *)
  (*     bind A B x f := join (fmap f x) *)
  (*   |}. *)

  (* Class CEMonad_prod (M M0 : choice_type -> choice_type) := *)
  (*   { prod : forall A, (M0 (M (M0 A))) -> (M (M0 A)) }. *)

  (* #[global] Program Instance ComposeProd2 `{CEMonad2} `{CEMonad2} `{@CEMonad_prod M M0} : CEMonad2 (fun x => M (M0 x)) := *)
  (*   {| *)
  (*     unit A x := unit (A := M0 A) (unit x) ; *)
  (*     fmap A B f x := fmap (A := M0 A) (B := M0 B) (fmap f) x ; *)
  (*     join A x := join (A := M0 A) (fmap (@prod M M0 _ A) x) *)
  (*   |}. *)

  (* #[global] Instance ComposeProd `{CEMonad} `{CEMonad} `(@CEMonad_prod M M0) : CEMonad (fun x => M (M0 x)) := (@CEMonad2ToCEMonad _ ComposeProd2). *)

  (* Definition bind_prod `{CEMonad} `{CEMonad} `{@CEMonad_prod M M0} *)
  (*            {A B} (x : (M (M0 A))) (f : A -> (M (M0 B))) *)
  (*   : (M (M0 B)) := *)
  (*   (@bind (fun x => M (M0 x)) (ComposeProd _) A B x f). *)


  (* Class CEMonad_swap (M M0 : choice_type -> choice_type) := *)
  (*   { swap : forall A, (M0 (M A)) -> (M (M0 A)) }. *)

  (* #[global] Program Instance ComposeSwap2 `{CEMonad2 } `{CEMonad2} `{@CEMonad_swap M M0} : CEMonad2 (fun x => M (M0 x)) := *)
  (*   {| *)
  (*     unit A x := unit (A := M0 A) (unit x) ; *)
  (*     fmap A B f x := fmap (A := M0 A) (B := M0 B) (fmap f) x ; *)
  (*     join A x := fmap (join (M := M0)) (join (fmap (@swap M M0 _ (M0 A)) x)) *)
  (*   |}. *)

  (* #[global] Instance ComposeSwap `{CEMonad} `{CEMonad} `(@CEMonad_swap M M0) : CEMonad (fun x => M (M0 x)) := (@CEMonad2ToCEMonad _ ComposeSwap2). *)

  (* Definition bind_swap `{CEMonad} `{CEMonad} `{@CEMonad_swap M M0} *)
  (*            A B (x : (M (M0 A))) (f : A -> (M (M0 B))) : (M (M0 B)) := *)
  (*   (@bind _ (@ComposeSwap M _ M0 _ _) A B x f). *)


  Section ResultMonad.
    Definition result_bind {C A B} (r : (result C A)) (f : A -> (result C B)) : (result C B) :=
      match r with
      | inl a => f a
      | inr e => (@Err B C e)
      end.

    Definition result_ret {C A : choice_type} (a : A) : (result C A) := Ok a.

    Global Program Instance result_monad {C : choice_type} : CEMonad :=
      {|
        M := result C ;
        bind := @result_bind C ;
        ret := @result_ret C ;
      |}.
    Solve All Obligations with now destruct c.
    Arguments result_monad {_} &.

  End ResultMonad.

  Definition option_bind {A B} (r : (option A)) (f : A -> (option B)) : (option B) :=
    match r with
      Some (a) => f a
    | None => None
    end.

  Definition option_ret {A : choice_type} (a : A) : (option A) := Some a.

  Global Program Instance option_monad : CEMonad :=
    Build_CEMonad option (@option_bind) (@option_ret) _ _ _.
  Solve All Obligations with now destruct c.

  Definition option_is_none {A} (x : (option A)) : bool :=
    match x with
    | None => true
    | _ => false
    end.

End choice_typeMonad.

(* #[global] Notation "x 'm(' v ')' ⇠ c1 ;; c2" := *)
(*   (choice_typeMonad.bind (M := v) c1 (fun x => c2)) *)
(*     (at level 100, c1 at next level, right associativity, *)
(*       format "x  'm(' v ')'  ⇠  c1  ;;  '//' c2") *)
(*     : hacspec_scope. *)

(* #[global] Notation " ' x 'm(' v ')' ⇠ c1 ;; c2" := *)
(*   (choice_typeMonad.bind (M := v) c1 (fun x => c2)) *)
(*     (at level 100, c1 at next level, x pattern, right associativity, *)
(*       format " ' x  'm(' v ')'  ⇠  c1  ;;  '//' c2") *)
(*     : hacspec_scope. *)

Definition foldi_bind {A : choice_type} `{mnd : choice_typeMonad.CEMonad} (a : uint_size) (b : uint_size) (f : uint_size -> A -> (choice_typeMonad.M A)) (init : (choice_typeMonad.M A)) : (choice_typeMonad.M A) :=
  @foldi ((choice_typeMonad.M A)) a b (fun x y => choice_typeMonad.bind y (f x)) init.

(*** Notation *)

Notation "'ifbnd' b 'then' x 'else' y '>>' f" := (if b then f x else f y) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'thenbnd' x 'else' y '>>' f" := (if b then (choice_typeMonad.bind x) f else f y) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'then' x 'elsebnd' y '>>' f" := (if b then f x else (choice_typeMonad.bind y) f) (at level 200) : hacspec_scope.
Notation "'ifbnd' b 'thenbnd' x 'elsebnd' y '>>' f" := (if b then choice_typeMonad.bind x f else choice_typeMonad.bind y f) (at level 200).

Notation "'foldibnd' s 'to' e 'M(' v ')' 'for' z '>>' f" :=
  (Hacspec_Lib_Pre.foldi s e (choice_typeMonad.ret z) (fun x y => choice_typeMonad.bind y (f x))) (at level 50) : hacspec_scope.

Axiom nat_mod_from_byte_seq_be : forall  {A n}, (seq A) -> (nat_mod n).

