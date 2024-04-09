From compcert Require Import Integers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
From QuickChick Require Import QuickChick.
Require Import Coq.Lists.List.
From Hacspec Require Import Hacspec_Lib.
Open Scope hacspec_scope.

#[global] Instance show_unit : Show (unit) := Build_Show (unit) (fun _ => "tt"%string).
Definition g_unit : G (unit) := returnGen tt.
#[global] Instance gen_unit : Gen (unit) := Build_Gen unit g_unit.

#[global] Instance show_int8 : Show (int8) :=
  Build_Show (int8) (fun x => show (int8_to_nat x)).
Definition g_int8 : G (int8) :=
  bindGen (* arbitrary *) (choose (0,1000)) (fun x => returnGen (Int8.repr x)).
#[global] Instance gen_int8 : Gen (int8) := Build_Gen int8 g_int8.

#[global] Instance show_int32 : Show (int32) :=
  Build_Show (int32) (fun x => show (int32_to_nat x)).
Definition g_int32 : G (int32) := (* restricted *)
  bindGen (choose (0,1000)) (fun x => returnGen (Int32.repr x)).
#[global] Instance gen_int32 : Gen (int32) := Build_Gen int32 g_int32.

#[global] Instance show_int64 : Show (int64) :=
  Build_Show (int64) (fun x => show (int64_to_nat x)).
Definition g_int64 : G (int64) :=
  bindGen (* arbitrary *) (choose (0,1000)) (fun x => returnGen (Int64.repr x)).
#[global] Instance gen_int64 : Gen (int64) := Build_Gen int64 g_int64.

#[global] Instance show_uint_size : Show (uint_size) :=
  Build_Show (uint_size) (fun x => show x).
Definition g_uint_size : G (uint_size) := arbitrary.
#[global] Instance gen_uint_size : Gen (uint_size) := Build_Gen uint_size g_uint_size.


Inductive dependent_pair {A} (n : nat) :=
| elem :  forall (l : list A), length l = n -> dependent_pair n.

Fixpoint g_listOf_aux {A} (gen : G (A)) (n : nat) : G (@dependent_pair A n).
  destruct n.
  - apply (returnGen).
    exists [].
    easy.
  - apply (bindGen gen).
    intros a.
    apply (bindGen (g_listOf_aux A gen n)).
    intros l.
    apply returnGen.
    destruct l as [l H].
    exists (a :: l).
    cbn.
    rewrite H.
    easy.
Defined.

Definition g_listOf {A} (gen : G (A)) : G (list A) :=
  bindGen arbitrary (fun n : nat => bindGen (g_listOf_aux gen n) (fun '(elem _ l _) => returnGen l)).

#[global] Instance show_nseq {A} `{Show A} n : Show (nseq A n) :=
  Build_Show (nseq A n) (fun x =>
     match x with
     | Vector.nil _ => "[]"%string
     | Vector.cons _ x n xs => ("[" ++ fold_left (fun a b => (a ++ " " ++ show b)) (VectorDef.to_list xs) (show x) ++ "]")%string
     end).
 
Definition array_from_list_ (A : Type) (n : nat) (l : list A) `{n = (Datatypes.length l)} : nseq A n.
Proof.
  rewrite H.
  apply array_from_list.
Defined.
Definition g_nseq {A} `{Gen A} n : G (nseq A n). (* (usize *)
   intros.
   apply (bindGen (g_listOf_aux (arbitrary : G A) n)).
   intros l.
   apply returnGen.

  destruct l.
  apply array_from_list_ with (l := l).
  easy.
Defined.
 
#[global] Instance gen_nseq {A} `{Gen A} n : Gen (nseq A n) := Build_Gen (nseq A n) (g_nseq  n).

#[global] Instance show_public_byte_seq : Show (public_byte_seq) :=
  Build_Show (public_byte_seq) (fun x =>
    match x with 
    | [] => "[]"%string
    | x :: xs => ("[" ++ fold_left (fun a b => (a ++ " " ++ show b)) xs (show x) ++ "]")%string
    end).
Definition g_public_byte_seq : G (public_byte_seq) :=
  listOf arbitrary.
  (* @genList int8 gen_int8. *)
  (* listOf (g_int8). *)
  (* bindGen g_int8 (fun y => *)
  (* bindGen g_int8 (fun x => returnGen ([y ; x]))). *)
  (* listOf (g_int8). (*arbitrary*) *)
#[global] Instance gen_public_byte_seq : Gen (public_byte_seq) :=
  Build_Gen public_byte_seq g_public_byte_seq.
