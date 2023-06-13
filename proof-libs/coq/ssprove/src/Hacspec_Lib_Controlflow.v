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

From Hacspec Require Import Hacspec_Lib_Integers.
From Hacspec Require Import Hacspec_Lib_Loops.
(* Require Import Hacspec_Lib_Seq. *)
(* Require Import Hacspec_Lib_Natmod. *)
(* Require Import Hacspec_Lib_Coercions. *)
(* Require Import Hacspec_Lib_Eq. *)
From Hacspec Require Import Hacspec_Lib_Monad.
From Hacspec Require Import Hacspec_Lib_Ltac.

(* Handle products of size 1 - 4 for foldi_both' *)
Notation "'ssp' ( 'fun' a => f )" :=
  (((fun (a : both _ _ _) => f)) (* : both _ _ uint_size -> both _ _ _ -> both _ _ _ *)) (at level 100, f at next level, a at next level).

Notation "'ssp' ( 'fun' ' ( a , b ) => f )" :=
  (fun (temp : both _ _ (_ × _)) => lift_n 1 temp (fun '(a, b) => f)) (at level 100, f at next level, a at next level, b at next level).

Notation "'ssp' ( 'fun' ' ( a , b , c ) => f )" :=
  (fun (temp : both _ _ (_ × _ × _)) => lift_n 2 temp (fun '(a, b, c) => f)) (at level 100, f at next level, a at next level, b at next level, c at next level).

Notation "'ssp' ( 'fun' ' ( a , b , c , d ) => f )" :=
  (fun (temp : both _ _ (_ × _ × _ × _)) => lift_n 3 temp (fun '(a, b, c, d) => f)) (at level 100, f at next level, a at next level, b at next level, c at next level, d at next level).

(* eq_fset *)
(* finmap.finSet *)
(* https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/aac-tactics.2C.20fset.20automation.2C.20universes *)
(* Display map / exponenetial maps *)

Equations foldi_both
        {acc: choice_type}
        {L1 L2 L3 I1 I2 I3}
        (lo_hi: both L2 I2 uint_size * both L3 I3 uint_size)
        {L I}
        (f: both (L2 :|: L3) (I2 :|: I3) uint_size ->
            both L I acc ->
            both L I acc)
        (init: both L1 I1 acc)
        `{is_true (fsubset (L1 :|: L2 :|: L3) L)} `{is_true (fsubset (I1 :|: I2 :|: I3) I)}
         : both L I (acc) :=
  foldi_both lo_hi f init :=
    foldi (fst lo_hi) (snd lo_hi) (@f) (init).
Solve All Obligations with intros ; solve_fsubset_trans.
Fail Next Obligation.

Notation "'fold'" :=
  (fun lo_hi init f => foldi_both (L1 := _) (L2 := _) (L3 := _) (I1 := _) (I2 := _) (I3 := _) lo_hi f init).

Equations foldi_both_list
           {acc B: choice_type}
        {L1 L2 I1 I2}
        (l : both L2 I2 (chList B))
        {L I}
        (f: both (L2) (I2) B ->
            both L I acc ->
            both L I acc)
        (init: both L1 I1 acc)
        `{is_true (fsubset (L1 :|: L2) L)} `{is_true (fsubset (I1 :|: I2) I)}
  : both L I (acc) :=
  foldi_both_list l f init :=
  bind_both l (fun l' => List.fold_left (fun x y => solve_lift @f (solve_lift ret_both y) (x) : both L I _) l' (solve_lift init)).
Solve All Obligations with intros ; solve_fsubset_trans.
Solve All Obligations with intros ; solve_ssprove_obligations.
Fail Next Obligation.

(* Equations foldi_both_list *)
(*            {acc B: choice_type} *)
(*            `{H : Default B} *)
(*         {L1 L2 I1 I2} *)
(*         (l : both L2 I2 (chList B)) *)
(*         (f: forall {L I} `{fsubset_loc : is_true (fsubset L1 L)} `{fsubset_opsig : is_true (fsubset I1 I)}, both (L2) (I2) B -> both L I acc -> both (L :|: (L2)) (I :|: (I2)) (acc)) (* {i < hi} *) *)
(*         (init: both L1 I1 acc) *)
(*   : both (L1 :|: (L2)) (I1 :|: (I2)) (acc) := *)
(*   foldi_both_list l f init := *)
(*     (solve_lift bind_both l (fun l' => (foldi (ret_both (repr _ 0)) (solve_lift ret_both (repr _ (length l')) : both L2 I2 _) (fun {L I H0 H1} => fun i v => solve_lift bind_both i (fun i' => @f _ _ _ _ (solve_lift ret_both (List.nth (Z.to_nat (unsigned i')) l' default)) v)) init))). *)
(* Solve Obligations with intros ; (assumption || solve_in_fset). *)
(* Fail Next Obligation. *)

Program Definition if_both {L1 L2 L3 I1 I2 I3} {A} (c : both L1 I1 'bool) (e_then : both L2 I2 A) (e_else : both L3 I3 A) : both (L1 :|: L2 :|: L3) (I1 :|: I2 :|: I3) A :=
  bind_both (fsubset_loc := _) (fsubset_opsig := _) c (fun b => if b then lift_both (fsubset_loc := _) (fsubset_opsig := _) e_then else lift_both  (fsubset_loc := _) (fsubset_opsig := _) e_else).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'ifb' b 'then' et 'else' ee" :=
  (if_both b et ee) (at level 100).

Equations match_both_option {L1 L2 L3 I1 I2 I3} {A B} (x : both L3 I3 (option A)) (fa : both L3 I3 A -> both L1 I1 B) (fb : both L2 I2 B) `{fsubset_loc1 : is_true (fsubset L3 L1)}  `{fsubset_loc2 : is_true (fsubset L3 L2)}  `{fsubset_opsig1 : is_true (fsubset I3 I1)}  `{fsubset_opsig2 : is_true (fsubset I3 I2)} : both (L1 :|: L2) (I1 :|: I2) B :=
  match_both_option x fa fb :=
  bind_both x (fun y => match y with
                     | Some a => solve_lift (fa (solve_lift (ret_both a)))
                     | None => solve_lift fb
                     end).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'matchb' x 'with' '|' 'Option_Some' a '=>' va '|' 'Option_None' '=>' vb 'end'" :=
  (match_both_option x (fun a => va) vb (fsubset_loc1 := _) (fsubset_loc2 := _) (fsubset_opsig1 := _) (fsubset_opsig2 := _)).

Notation "'matchb' x 'with' '|' 'Option_Some' a '=>' va '|' '_' '=>' vb 'end'" :=
  (match_both_option x (fun a => va) vb (fsubset_loc1 := _) (fsubset_loc2 := _) (fsubset_opsig1 := _) (fsubset_opsig2 := _)).

Program Definition foldi_both0_
        {acc : choice_type}
        (fuel : nat)
        (i : both (fset []) (fset []) uint_size)
        (f: both (fset []) (fset []) (uint_size) -> both (fset []) (fset []) acc -> both (fset []) (fset []) (acc))
        (cur : both (fset []) (fset []) acc) : both (fset []) (fset []) (acc) :=
  foldi_ fuel i (@f) (lift_both cur (fsubset_loc := _) (fsubset_opsig := _)) (fsubset_loc := _) (fsubset_opsig := _).
Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
Fail Next Obligation.

Equations foldi0
          {acc: choice_type}
          (lo: both (fset []) (fset []) uint_size)
          (hi: both (fset []) (fset []) uint_size) (* {lo <= hi} *)
          (f: both (fset []) (fset []) (uint_size) -> both (fset []) (fset []) acc -> both (fset []) (fset []) (acc)) (* {i < hi} *)
          (init: both (fset []) (fset []) acc) : both (fset []) (fset []) (acc) :=
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
        (lo_hi: both (fset []) (fset []) uint_size * both (fset []) (fset []) uint_size)
        (f: both (fset []) (fset []) uint_size -> both (fset []) (fset []) acc -> both (fset []) (fset []) (acc)) (* {i < hi} *)
        (init: both (fset []) (fset []) acc)
  : both (fset []) (fset []) (acc) :=
  foldi0 (fst lo_hi) (snd lo_hi) f init.

Equations foldi_both0_list
           {acc B: choice_type}
        (l : both (fset []) (fset []) (chList B))
        (f: both ((fset [])) ((fset [])) B -> both(fset []) (fset []) acc -> both (fset []) (fset []) (acc)) (* {i < hi} *)
        (init: both (fset []) (fset []) acc)
  : both (fset []) (fset []) (acc) :=
  foldi_both0_list l f init :=
    bind_both l (fun l' => List.fold_left (fun x y => solve_lift @f (solve_lift ret_both y) (x) : both (fset []) (fset []) _) l' (solve_lift init : both (fset []) (fset []) _)).
Solve Obligations with intros ; (assumption || solve_in_fset).
Fail Next Obligation.


Program Definition if_both0 {A} (c : both (fset []) (fset []) 'bool) (e_then : both (fset []) (fset []) A) (e_else : both (fset []) (fset []) A) : both (fset []) (fset []) A :=
  bind_both (fsubset_loc := _) (fsubset_opsig := _) c (fun b => if b then lift_both (fsubset_loc := _) (fsubset_opsig := _) e_then else lift_both  (fsubset_loc := _) (fsubset_opsig := _) e_else).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Notation "'ifb0' b 'then' et 'else' ee" :=
  (if_both0 b et ee) (at level 100).

(* Definition Exception t  := (@choice_typeMonad.result_monad t). *)

Notation "'letm[' bind_code_mnd ']' x ':=' y 'in' z" := (choice_typeMonad.monad_bind_both (BindCode := bind_code_mnd) y (fun x => z)) (at level 100, x pattern).
Notation "'letm[' bind_code_mnd ']' ( x : t ) ':=' y 'in' z" := (choice_typeMonad.monad_bind_both (BindCode := bind_code_mnd) y (fun x => z)) (at level 100, x pattern).

(* Check letm[ @choice_typeMonad.result_bind_code ('bool) ] y := solve_lift ret_both (choice_typeMonad.ret _) in _. *)
