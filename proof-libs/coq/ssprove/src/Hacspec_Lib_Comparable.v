From Coq Require Import ZArith List.
From Crypt Require Import Package.

(************************************************)
(*   Implementation of comparision functions    *)
(************************************************)

(* Typeclass handling of default elements, for use in sequences/arrays.
   We provide instances for the library integer types *)
Class Default (A : Type) := {
  default : A
}.
Global Arguments default {_} {_}.

Class EqDec (A : Type) :=
  { eqb : A -> A -> bool ;
    eqb_leibniz : forall x y, is_true (eqb x y) <-> x = y }.

Infix "=.?" := eqb (at level 40) : hacspec_scope.
Infix "!=.?" := (fun a b => negb (eqb a b)) (at level 40) : hacspec_scope.

Class Comparable (A : Type) := {
  ltb : A -> A -> bool;
  leb : A -> A -> bool;
  gtb : A -> A -> bool;
  geb : A -> A -> bool;
}.
Infix "<.?" := ltb (at level 42) : hacspec_scope.
Infix "<=.?" := leb (at level 42) : hacspec_scope.
Infix ">.?" := gtb (at level 42) : hacspec_scope.
Infix ">=.?" := geb (at level 42) : hacspec_scope.

Instance eq_dec_lt_Comparable {A : Type} `{EqDec A} (ltb : A -> A -> bool) : Comparable A := {
    ltb := ltb;
    leb a b := if eqb a b then true else ltb a b ;
    gtb a b := ltb b a;
    geb a b := if eqb a b then true else ltb b a;
  }.

Instance eq_dec_le_Comparable {A : Type} `{EqDec A} (leb : A -> A -> bool) : Comparable A := {
    ltb a b := if eqb a b then false else leb a b;
    leb := leb ;
    gtb a b := if eqb a b then false else leb b a;
    geb a b := leb b a;
  }.

Theorem eqb_refl : forall {A} {H : EqDec A} (x : A), (@eqb A H x x) = true.
Proof.
  intros.
  now apply eqb_leibniz.
Qed.

Theorem eqbP : forall {A} {H : EqDec A} (x y : A), ssrbool.reflect (x = y) (@eqb A H x y).
Proof.
  intros.
  apply Bool.iff_reflect.
  rewrite <- eqb_leibniz.
  reflexivity.
Qed.

Theorem neqb_leibniz : forall {A} {H : EqDec A} x y, eqb x y = false <-> x <> y .
Proof.
  intros.
  rewrite (ssrbool.rwP ssrbool.negPf).
  rewrite <- (ssrbool.rwP (@ssrbool.negP (eqb x y))).
  apply not_iff_compat.
  apply eqb_leibniz.
Qed.


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
