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

From Core Require Import Core_Marker.

From Core Require Import Core_Convert.

From Core Require Import Core_Base_interface_Int.

From Core Require Import Core_Result.

Inductive t_ControlFlow a b :=
| ControlFlow_Continue : a -> t_ControlFlow a b
| ControlFlow_Break : b -> t_ControlFlow a b.
Arguments ControlFlow_Continue {a} {b}.
Arguments ControlFlow_Break {a} {b}.

(* Run exception *)
Definition run {a} (x : t_ControlFlow a a) : a :=
  match x with
  | ControlFlow_Continue x => x
  | ControlFlow_Break x => x
  end.

Definition bind_exception {a c}
  (x : t_ControlFlow a c)
  (f : forall (k : a) `{x = ControlFlow_Continue k}, t_ControlFlow a c) : t_ControlFlow a c :=
  match x as k return x = k -> _ with
  | ControlFlow_Continue o => fun k => f (H := k) o
  | ControlFlow_Break o => fun _ => ControlFlow_Break o
  end eq_refl.

Notation "'letb' p ':=' e 'in' rhs" :=
  (bind_exception e (fun p _ => rhs)) (at level 100).