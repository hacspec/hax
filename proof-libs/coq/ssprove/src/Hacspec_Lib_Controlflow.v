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

From Hacspec Require Import Hacspec_Lib_Integers.
From Hacspec Require Import Hacspec_Lib_Loops.
From Hacspec Require Import Hacspec_Lib_Monad.
From Hacspec Require Import Hacspec_Lib_Ltac.

(* Handle products of size 1 - 4 for foldi_both' *)
Notation "'ssp' ( 'fun' a => f )" :=
  (((fun (a : both _) => f))) (at level 100, f at next level, a at next level).

Notation "'ssp' ( 'fun' ' ( a , b ) => f )" :=
  (fun (temp : both (_ × _)) => lift_n 1 temp (fun '(a, b) => f)) (at level 100, f at next level, a at next level, b at next level).

Notation "'ssp' ( 'fun' ' ( a , b , c ) => f )" :=
  (fun (temp : both (_ × _ × _)) => lift_n 2 temp (fun '(a, b, c) => f)) (at level 100, f at next level, a at next level, b at next level, c at next level).

Notation "'ssp' ( 'fun' ' ( a , b , c , d ) => f )" :=
  (fun (temp : both (_ × _ × _ × _)) => lift_n 3 temp (fun '(a, b, c, d) => f)) (at level 100, f at next level, a at next level, b at next level, c at next level, d at next level).

(* eq_fset *)
(* finmap.finSet *)
(* https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/aac-tactics.2C.20fset.20automation.2C.20universes *)
(* Display map / exponenetial maps *)

Equations foldi_both
        {acc: choice_type}
        (lo_hi: both uint_size * both uint_size)
        (f: both uint_size ->
            both acc ->
            both acc)
        (init: both acc)
         : both (acc) :=
  foldi_both lo_hi f init :=
    foldi (fst lo_hi) (snd lo_hi) (@f) (init).
Solve All Obligations with intros ; solve_fsubset_trans.
Fail Next Obligation.

Equations foldi_both_list
           {acc B: choice_type}
        (l : both (chList B))
        (f: both B ->
            both acc ->
            both acc)
        (init: both acc)
  : both (acc) :=
  foldi_both_list l f init :=
  bind_both l (fun l' => List.fold_left (fun x y => solve_lift @f (solve_lift ret_both y) (x) : both _) l' (solve_lift init)).
Solve All Obligations with intros ; solve_fsubset_trans.
Solve All Obligations with intros ; solve_ssprove_obligations.
Fail Next Obligation.

Program Definition if_both {A} (c : both 'bool) (e_then : both A) (e_else : both A) : both A :=
  bind_both c (fun b => if b then lift_both e_then else lift_both e_else).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'ifb' b 'then' et 'else' ee" :=
  (if_both b et ee) (at level 100).

Equations match_both_option {A B} (x : both (option A)) (fa : both A -> both B) (fb : both B) : both B :=
  match_both_option x fa fb :=
  bind_both x (fun y => match y with
                     | Some a => solve_lift (fa (solve_lift (ret_both a)))
                     | None => solve_lift fb
                     end).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'matchb' x 'with' '|' 'Option_Some' a '=>' va '|' 'Option_None' '=>' vb 'end'" :=
  (match_both_option x (fun a => va) vb).

Notation "'matchb' x 'with' '|' 'Option_Some' a '=>' va '|' '_' '=>' vb 'end'" :=
  (match_both_option x (fun a => va) vb).

Program Definition foldi_both0_
        {acc : choice_type}
        (fuel : nat)
        (i : both uint_size)
        (f: both (uint_size) -> both acc -> both (acc))
        (cur : both acc) : both (acc) :=
  foldi_ fuel i (@f) (lift_both cur).
Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
Fail Next Obligation.

Equations foldi0
          {acc: choice_type}
          (lo: both uint_size)
          (hi: both uint_size) (* {lo <= hi} *)
          (f: both (uint_size) -> both acc -> both (acc)) (* {i < hi} *)
          (init: both acc) : both (acc) :=
  foldi0 lo hi f init :=
    bind_both lo (fun lo =>
                    bind_both hi (fun hi =>
                                    match Z.sub (unsigned hi) (unsigned lo) with
                                    | Z0 => lift_both init
                                    | Zneg p => lift_both init
                                    | Zpos p => foldi_both0_ (Pos.to_nat p) (solve_lift (ret_both lo)) (@f) init
                                    end))
.
Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
Fail Next Obligation.

Definition foldi_both0
        {acc: choice_type}
        (lo_hi: both uint_size * both uint_size)
        (f: both uint_size -> both acc -> both (acc)) (* {i < hi} *)
        (init: both acc)
  : both (acc) :=
  foldi0 (fst lo_hi) (snd lo_hi) f init.

Equations foldi_both0_list
           {acc B: choice_type}
        (l : both (chList B))
        (f: both B -> both acc -> both (acc)) (* {i < hi} *)
        (init: both acc)
  : both (acc) :=
  foldi_both0_list l f init :=
    bind_both l (fun l' => List.fold_left (fun x y => solve_lift @f (solve_lift ret_both y) (x) : both _) l' (solve_lift init : both _)).
Fail Next Obligation.

Notation "'f_fold'" :=
  (fun lo_hi init f => foldi_both_list lo_hi f init).

Program Definition if_both0 {A} (c : both 'bool) (e_then : both A) (e_else : both A) : both A :=
  bind_both c (fun b => if b then lift_both e_then else lift_both  e_else).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'ifb0' b 'then' et 'else' ee" :=
  (if_both0 b et ee) (at level 100).

Notation "'letm[' bind_code_mnd ']' x ':=' y 'in' z" := (choice_typeMonad.monad_bind_both (BindCode := bind_code_mnd) y (fun x => z)) (at level 100, x pattern).
Notation "'letm[' bind_code_mnd ']' ( x : t ) ':=' y 'in' z" := (choice_typeMonad.monad_bind_both (BindCode := bind_code_mnd) y (fun x => z)) (at level 100, x pattern).
