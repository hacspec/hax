(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Class t_From (Self : _) := {
  f_from : (T -> Self) ;
}.

#[global] Instance T_t_From (T : _) : t_From T T := {
  f_from (t : T) := t;
}.

Class t_Into (Self : _) := {
  f_into : (Self -> T) ;
}.

#[global] Instance T_t_Into (T : _) (U : _) : t_Into T U := {
  f_into (self : T) := f_from self;
}.