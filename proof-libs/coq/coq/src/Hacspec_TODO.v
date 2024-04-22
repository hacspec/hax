Global Set Warnings "-ambiguous-paths".
Global Set Warnings "-uniform-inheritance".
Global Set Warnings "-auto-template".
Global Set Warnings "-disj-pattern-notation".

From Coq Require Import ZArith List.
Import ListNotations.
(* Require Import IntTypes. *)

(* Require Import MachineIntegers. *) From compcert Require Import Integers.
From Coqprime Require GZnZ.

Require Import Lia.

(*** TODO *)

Declare Scope hacspec_scope.
Definition never_to_any {A} (f : False) : A. contradiction. Defined.
Definition panic_fmt {A} (x : A): False. Admitted.
Notation impl_2__new_const := id.
Notation unsize := id.
