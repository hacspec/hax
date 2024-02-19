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

(*** Nats *)


Section Todosection.

Definition nat_mod_equal {p} (a b : nat_mod p) : both 'bool :=
  ret_both (@eqtype.eq_op (fintype_ordinal__canonical__eqtype_Equality (S (Init.Nat.pred (Z.to_nat p)))) a b : 'bool).

Definition nat_mod_equal_reflect {p} {a b} : Bool.reflect (a = b) (is_pure (@nat_mod_equal p a b)) :=
  @eqtype.eqP (fintype_ordinal__canonical__eqtype_Equality (S (Init.Nat.pred (Z.to_nat p)))) a b.

Definition nat_mod_zero {p} : both ((nat_mod p)) := ret_both (nat_mod_zero).
Definition nat_mod_one {p} : both ((nat_mod p)) := ret_both (nat_mod_one).
Definition nat_mod_two {p} : both ((nat_mod p)) := ret_both (nat_mod_two).

Definition nat_mod_add {n : Z} (a : nat_mod n) (b : nat_mod n) : both (nat_mod n) := ret_both (nat_mod_add a b).
Definition nat_mod_mul {n : Z} (a:nat_mod n) (b:nat_mod n) : both (nat_mod n) := ret_both (nat_mod_mul a b).
Definition nat_mod_sub {n : Z} (a:nat_mod n) (b:nat_mod n) : both (nat_mod n) := ret_both (nat_mod_sub a b).
Definition nat_mod_div {n : Z} (a:nat_mod n) (b:nat_mod n) : both (nat_mod n) := ret_both (nat_mod_div a b).

Definition nat_mod_neg {n : Z} (a:nat_mod n) : both (nat_mod n) := ret_both (nat_mod_neg a).

Definition nat_mod_inv {n : Z} (a:nat_mod n) : both (nat_mod n) := ret_both (nat_mod_inv a).

Definition nat_mod_exp_def {p : Z} (a:nat_mod p) (n : nat) : both (nat_mod p) :=
  ret_both (nat_mod_exp_def a n).

Definition nat_mod_exp {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow {WS} {p} a n := @nat_mod_exp_def p a (Z.to_nat (@unsigned WS n)).
Definition nat_mod_pow_felem {p} (a n : nat_mod p) := @nat_mod_exp_def p a (Z.to_nat (nat_of_ord n)).
Definition nat_mod_pow_self {p} (a n : nat_mod p) := nat_mod_pow_felem a n.

Close Scope nat_scope.

Definition nat_mod_from_secret_literal {m : Z} (x:int128) : both (nat_mod m) :=
 ret_both (@nat_mod_from_secret_literal m x).

Definition nat_mod_from_literal (m : Z) (x:int128) : both ((nat_mod m)) := nat_mod_from_secret_literal x.

Definition nat_mod_to_byte_seq_le {n : Z} (m : nat_mod n) : both (seq int8) := ret_both (nat_mod_to_byte_seq_le m).
Definition nat_mod_to_byte_seq_be {n : Z} (m : nat_mod n) : both (seq int8) := ret_both (nat_mod_to_byte_seq_be m).
Definition nat_mod_to_public_byte_seq_le (n : Z) (m : nat_mod n) : both (seq int8) := ret_both (nat_mod_to_public_byte_seq_le n m).
Definition nat_mod_to_public_byte_seq_be (n : Z) (m : nat_mod n) : both (seq int8) := ret_both (nat_mod_to_public_byte_seq_be n m).

Definition nat_mod_bit {n : Z} (a : nat_mod n) (i : uint_size) : both 'bool :=
  ret_both (nat_mod_bit a i).

(* Alias for nat_mod_bit *)
Definition nat_get_mod_bit {p} (a : nat_mod p) (i : uint_size) : both 'bool := ret_both (nat_get_mod_bit a i).
Definition nat_mod_get_bit {p} (a : nat_mod p) n : both (nat_mod p) :=
  ret_both (nat_mod_get_bit a n).

Definition array_declassify_eq {A l} (x : nseq_ A l) (y : nseq_ A l) : both 'bool := ret_both (array_declassify_eq x y).
Definition array_to_le_uint32s {A l} (x : nseq_ A l) : both (seq uint32) := ret_both (array_to_le_uint32s x).
Definition array_to_be_uint32s {l} (x : nseq_ uint8 l) : both (seq uint32) := ret_both (array_to_be_uint32s x).
Definition array_to_le_uint64s {A l} (x : nseq_ A l) : both (seq uint64) := ret_both (array_to_le_uint64s x).
Definition array_to_be_uint64s {l} (x : nseq_ uint8 l) : both (seq uint64) := ret_both (array_to_be_uint64s x).
Definition array_to_le_uint128s {A l} (x : nseq_ A l) : both (seq uint128) := ret_both (array_to_le_uint128s x).
Definition array_to_be_uint128s {l} (x : nseq_ uint8 l) : both (seq uint128) := ret_both (array_to_be_uint128s x).
Definition array_to_le_bytes {A l} (x : nseq_ A l) : both (seq uint8) := ret_both (array_to_le_bytes x).
Definition array_to_be_bytes {A l} (x : nseq_ A l) : both (seq uint8) := ret_both (array_to_be_bytes x).
Definition nat_mod_from_byte_seq_le {A n} (x : seq A) : both (nat_mod n) := ret_both (nat_mod_from_byte_seq_le x).
Definition most_significant_bit {m} (x : nat_mod m) (n : uint_size) : both (uint_size) := ret_both (most_significant_bit x n).


(* We assume 2^x < m *)

Definition nat_mod_pow2 (m : Z) {WS} (x : (@int WS)) : both ((nat_mod m)) :=
  ret_both (nat_mod_pow2 m (Z.to_nat (unsigned x))).

End Todosection.

Infix "+%" := nat_mod_add (at level 33) : hacspec_scope.
Infix "*%" := nat_mod_mul (at level 33) : hacspec_scope.
Infix "-%" := nat_mod_sub (at level 33) : hacspec_scope.
Infix "/%" := nat_mod_div (at level 33) : hacspec_scope.
