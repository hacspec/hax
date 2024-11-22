(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Record t_Range (Idx : _) : Type := {
  f_start : Idx;
  f_end : Idx;
}.