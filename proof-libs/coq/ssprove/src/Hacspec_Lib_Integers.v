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

(*** Integers *)

Declare Scope hacspec_scope.

From Hacspec Require Import ChoiceEquality.
From Hacspec Require Import LocationUtility.
From Hacspec Require Import Hacspec_Lib_Comparable.
From Hacspec Require Import Hacspec_Lib_Pre.

Open Scope bool_scope.
Open Scope hacspec_scope.
Open Scope nat_scope.
Open Scope list_scope.

Import choice.Choice.Exports.

(* Definition lift3_both_ {A B C D : choice_type} {L} {I} (f : A -> B -> C -> D) (x : both L I A) (y : both L I B) (z : both L I C) := *)
(*   bind_both_ x (fun x' => *)
(*   bind_both_ y (fun y' => *)
(*   bind_both_ z (fun z' => *)
(*   ret_both (f x' y' z')))). *)

Equations int_add {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
  int_add := lift2_both (Hacspec_Lib_Pre.int_add).
  Fail Next Obligation.

  Equations int_sub {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_sub := (lift2_both (Hacspec_Lib_Pre.int_sub)).
  Fail Next Obligation.

  Equations int_opp {L (* L2 *) : {fset Location}} {I (* I2 *) : Interface} {WS}
           (x : both L I (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L L2)} `{H_opsig_incl_x : is_true (fsubset I I2)} *) : both L I (int WS) :=
    int_opp := (lift1_both (Hacspec_Lib_Pre.int_opp)).
  Fail Next Obligation.

  Equations int_mul {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_mul := (lift2_both (Hacspec_Lib_Pre.int_mul)).
  Fail Next Obligation.

  Equations int_div {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_div := (lift2_both (Hacspec_Lib_Pre.int_div : int _ -> int _ -> int _)).
  Fail Next Obligation.

  Equations int_mod {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_mod := (lift2_both (Hacspec_Lib_Pre.int_mod : int _ -> int _ -> int _)).
  Fail Next Obligation.

  Equations int_xor {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_xor := (lift2_both (Hacspec_Lib_Pre.int_xor : int _ -> int _ -> int _)).
  Fail Next Obligation.

  Equations int_and {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_and := (lift2_both (Hacspec_Lib_Pre.int_and : int _ -> int _ -> int _)).
    Fail Next Obligation.

    Equations int_or {L1 L2 (* L3 *) : {fset Location}} {I1 I2 (* I3 *) : Interface} {WS}
           (x : both L1 I1 (int WS)) (y : both L2 I2 (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L3)} `{H_opsig_incl_x : is_true (fsubset I1 I3)} *)
           (* `{H_loc_incl_y : is_true (fsubset L2 L3)} `{H_opsig_incl_y : is_true (fsubset I2 I3)} *) : both (L1 :|: L2) (* L3 *) (I1 :|: I2) (* I3 *) (int WS) :=
    int_or := (lift2_both (Hacspec_Lib_Pre.int_or : int _ -> int _ -> int _)).
  Fail Next Obligation.

  Equations int_not {L (* L2 *) : {fset Location}} {I (* I2 *) : Interface} {WS}
           (x : both L I (int WS))
           (* `{H_loc_incl_x : is_true (fsubset L1 L2)} `{H_opsig_incl_x : is_true (fsubset I1 I2)} *) : both L I (int WS) :=
    int_not := (lift1_both (Hacspec_Lib_Pre.int_not : int _ -> int _)).
  Fail Next Obligation.

  Equations cast_int {L (* L2 *) : {fset Location}} {I (* I2 *) : Interface} {WS1 WS2}
           (x : both L I (int WS1))
           (* `{H_loc_incl_x : is_true (fsubset L1 L2)} `{H_opsig_incl_x : is_true (fsubset I1 I2)} *) : both L I (int WS2) :=
    cast_int := (lift1_both (fun (n : int _) => repr _ (unsigned n))).
  Fail Next Obligation.
(* End IntType. *)

Notation secret := (lift1_both secret).

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

(* Section Uint. *)
  Notation uint8_declassify := (lift1_both uint8_declassify).
  Notation int8_declassify := (lift1_both int8_declassify).
  Notation uint16_declassify := (lift1_both uint16_declassify).
  Notation int16_declassify := (lift1_both int16_declassify).
  Notation uint32_declassify := (lift1_both uint32_declassify).
  Notation int32_declassify := (lift1_both int32_declassify).
  Notation uint64_declassify := (lift1_both uint64_declassify).
  Notation int64_declassify := (lift1_both int64_declassify).
  Notation uint128_declassify := (lift1_both uint128_declassify).
  Notation int128_declassify := (lift1_both int128_declassify).

  Notation uint8_classify := (lift1_both uint8_classify).
  Notation int8_classify := (lift1_both int8_classify).
  Notation uint16_classify := (lift1_both uint16_classify).
  Notation int16_classify := (lift1_both int16_classify).
  Notation uint32_classify := (lift1_both uint32_classify).
  Notation int32_classify := (lift1_both int32_classify).
  Notation uint64_classify := (lift1_both uint64_classify).
  Notation int64_classify := (lift1_both int64_classify).
  Notation uint128_classify := (lift1_both uint128_classify).
  Notation int128_classify := (lift1_both int128_classify).

  (* CompCert integers' signedness is only interpreted through 'signed' and 'unsigned',
   and not in the representation. Therefore, uints are just names for their respective ints.
   *)

  Notation declassify_usize_from_uint8 := (lift1_both declassify_usize_from_uint8).
  Notation declassify_u32_from_uint32 := (lift1_both declassify_u32_from_uint32).

  Notation uint8_rotate_left := (lift2_both uint8_rotate_left).

  Notation uint8_rotate_right := (lift2_both uint8_rotate_right).

  Notation uint16_rotate_left := (lift2_both uint16_rotate_left).

  Notation uint16_rotate_right := (lift2_both uint16_rotate_right).

  Notation uint32_rotate_left := (lift2_both uint32_rotate_left).

  Notation uint32_rotate_right := (lift2_both uint32_rotate_right).

  Notation uint64_rotate_left := (lift2_both uint64_rotate_left).

  Notation uint64_rotate_right := (lift2_both uint64_rotate_right).

  Notation uint128_rotate_left := (lift2_both uint128_rotate_left).

  Notation uint128_rotate_right := (lift2_both uint128_rotate_right).
  Notation usize_shift_right_ := (lift2_both (fun u s => u usize_shift_right s)).

  Notation usize_shift_left_ :=
    (fun (u: both (fset []) ([interface]) uint_size) (s: both (fset []) ([interface]) int32) =>
    {|
      is_pure := (is_pure u) usize_shift_left (is_pure s) ;
      is_state :=
      {code
         temp_u ← is_state u ;;
         temp_s ← is_state s ;;
         ret (temp_u usize_shift_left temp_s)
      }
    |}).
  (* Next Obligation. *)
  (*   intros. *)
  (*   pattern_both Hb Hf Hg. *)
  (*   apply (@r_bind_trans_both (uint_size) (uint_size)). *)
  (*   subst Hf Hg Hb ; hnf. *)
  (*   pattern_both Hb Hf Hg. *)
  (*   apply (@r_bind_trans_both (int32)). *)
  (*   subst Hf Hg Hb ; hnf. *)
  (*   apply r_ret. *)
  (*   easy. *)
  (* Qed. *)

  (**** Operations *)

  Notation shift_left_ := (lift2_both shift_left_).
  Notation shift_right_ := (lift2_both shift_right_).

(* End Uint. *)

Infix "usize_shift_right" := (usize_shift_right_) (at level 77) : hacspec_scope.
Infix "usize_shift_left" := (usize_shift_left_) (at level 77) : hacspec_scope.

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.
