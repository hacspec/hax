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

Equations int_add {WS} (x : both (int WS)) (y : both (int WS)) : both (int WS) :=
  int_add := lift2_both (Hacspec_Lib_Pre.int_add).
Fail Next Obligation.

Equations int_sub {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_sub := (lift2_both (Hacspec_Lib_Pre.int_sub)).
Fail Next Obligation.

Equations int_opp {WS} (x : both (int WS)) : both (int WS) :=
  int_opp := (lift1_both (Hacspec_Lib_Pre.int_opp)).
Fail Next Obligation.

Equations int_mul {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_mul := (lift2_both (Hacspec_Lib_Pre.int_mul)).
Fail Next Obligation.

Equations int_div {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_div := (lift2_both (Hacspec_Lib_Pre.int_div : int _ -> int _ -> int _)).
Fail Next Obligation.

Equations int_mod {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_mod := (lift2_both (Hacspec_Lib_Pre.int_mod : int _ -> int _ -> int _)).
Fail Next Obligation.

Equations int_xor {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_xor := (lift2_both (Hacspec_Lib_Pre.int_xor : int _ -> int _ -> int _)).
Fail Next Obligation.

Equations int_and {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_and := (lift2_both (Hacspec_Lib_Pre.int_and : int _ -> int _ -> int _)).
Fail Next Obligation.

Equations int_or {WS}
  (x : both (int WS)) (y : both (int WS))
  : both (int WS) :=
  int_or := (lift2_both (Hacspec_Lib_Pre.int_or : int _ -> int _ -> int _)).
Fail Next Obligation.

Equations int_not {WS} (x : both (int WS)) : both (int WS) :=
  int_not := (lift1_both (Hacspec_Lib_Pre.int_not : int _ -> int _)).
Fail Next Obligation.

Equations cast_int {WS1 WS2} (x : both (int WS1)) : both (int WS2) :=
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

(**** Operations *)

Notation shift_left_ := (lift2_both shift_left_).
Notation shift_right_ := (lift2_both shift_right_).

(* End Uint. *)

Infix "usize_shift_right" := (usize_shift_right_) (at level 77) : hacspec_scope.
Infix "usize_shift_left" := (usize_shift_left_) (at level 77) : hacspec_scope.

Infix "shift_left" := (shift_left_) (at level 77) : hacspec_scope.
Infix "shift_right" := (shift_right_) (at level 77) : hacspec_scope.
