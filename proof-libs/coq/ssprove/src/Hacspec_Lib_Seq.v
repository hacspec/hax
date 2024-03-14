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
(* From Jasmin Require Import word. *)
From Crypt Require Import jasmin_word.

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

(*** Seq *)

(* Section Seqs. *)

(**** Unsafe functions *)

Notation seq_new_ := (lift2_both seq_new_).
Notation seq_new := (lift1_both seq_new).
Equations seq_len {A : choice_type} (x : both (seq A)) : both (uint_size) :=
  seq_len := (lift1_both Hacspec_Lib_Pre.seq_len).
Fail Next Obligation.
Notation seq_index := (lift2_both seq_index).

(**** Seq manipulation *)

(* Notation seq_slice := (lift3_both seq_slice). *)

Notation seq_slice_range :=
  (lift2_both seq_slice_range).

(* updating a subsequence in a sequence *)
Definition seq_update
  {a: choice_type}
  (s: ((seq a)))
  (start: uint_size)
  (input: ((seq a)))
  : both ((seq a)) :=
  ret_both (seq_update s start input).

(* updating only a single value in a sequence*)
Definition seq_upd
  {a: choice_type}

  (s: ((seq a)))
  (start: uint_size)
  (v: ((a)))
  : both ((seq a)) :=
  ret_both (seq_upd s start v).

Definition seq_update_start
  {a: choice_type}

  (s: ( (seq a)))
  (start_s: ( (seq a)))
  : both ((seq a)) :=
  ret_both (seq_update_start s start_s).

Definition seq_update_slice
  {A : choice_type}
  (out: ( (seq A)))
  (start_out: nat)
  (input: ( (seq A)))
  (start_in: nat)
  (len: nat)
  : both ((seq A)) :=
  ret_both (seq_update_slice out start_out input start_in len).

Definition seq_concat
  {a : choice_type}

  (s1 :( (seq a)))
  (s2: ( (seq a)))
  : both ((seq a)) :=
  ret_both (seq_concat s1 s2).

Notation seq_push := (lift2_both seq_push).

Definition seq_from_slice
  {a: choice_type}

  (input: ( (seq a)))
  (start_fin: uint_size × uint_size)
  : both ((seq a)) :=
  ret_both (seq_from_slice input start_fin).

Definition seq_from_slice_range
  {a: choice_type}

  (input: ( (seq a)))
  (start_fin: uint_size × uint_size)
  : both ((seq a)) :=
  ret_both (seq_from_slice_range input start_fin).

Definition seq_from_seq {A} (l : (seq A)) : both (seq A) :=
  ret_both (seq_from_seq l).

(**** Chunking *)

Definition seq_num_chunks {a: choice_type} (s: ( (seq a))) (chunk_len: uint_size) : both (uint_size) :=
  ret_both (seq_num_chunks s chunk_len).

Definition seq_chunk_len
  {a: choice_type}
  (s: ( (seq a)))
  (chunk_len: nat)
  (chunk_num: nat)
  : both (('nat)) :=
  ret_both (seq_chunk_len s chunk_len chunk_num).

Definition seq_get_chunk
  {a: choice_type}

  (s: ( (seq a)))
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  : both (((uint_size × seq a))) :=
  ret_both (seq_get_chunk s chunk_len chunk_num).

Definition seq_set_chunk
  {a: choice_type}

  (s: ( (seq a)))
  (chunk_len: uint_size)
  (chunk_num: uint_size)
  (chunk: ( (seq a)) ) : both ((seq a)) :=
  ret_both (seq_set_chunk s chunk_len chunk_num chunk).


Definition seq_num_exact_chunks {a} (l : ( (seq a))) (chunk_size : ( (uint_size))) : (both uint_size) :=
  ret_both (seq_num_exact_chunks l chunk_size).

Definition seq_get_exact_chunk {a : choice_type}  (l : ( (seq a))) (chunk_size chunk_num: ( (uint_size))) :
  both ((seq a)) :=
  ret_both (seq_get_exact_chunk l chunk_size chunk_num).

Definition seq_set_exact_chunk {a : choice_type} :=
  @seq_set_chunk a.

Definition seq_get_remainder_chunk {a : choice_type}  (l : (seq a)) (chunk_size : (uint_size)) : both ((seq a)) :=
  ret_both (seq_get_remainder_chunk l chunk_size).

Definition seq_xor_ {WS} (x y : seq (@int WS)) : both (seq (@int WS)) :=
  ret_both (seq_xor_ x y).

Definition seq_truncate {a : choice_type}  (x : seq a) (n : nat) : both (seq a) :=
  ret_both (seq_truncate x n).

(* End Seqs. *)
Infix "seq_xor" := seq_xor_ (at level 33) : hacspec_scope.

(* Section Arrays. *)
(**** types *)

(***** prelude.rs *)
Definition uint128_word_t : choice_type := nseq_ uint8 16.
Definition uint64_word_t : choice_type := nseq_ uint8 8.
Definition uint32_word_t : choice_type := nseq_ uint8 4.
Definition uint16_word_t : choice_type := nseq_ uint8 2.

(**** Array manipulation *)
Equations array_new_ {A: choice_type} (init: both A) `(len: uint_size) : both (nseq A len) :=
  array_new_ init len := lift1_both (fun x => Hacspec_Lib_Pre.array_new_ x (from_uint_size len)) init.

Equations array_index
  {A: choice_type} {len : nat} (x : both (nseq_ A len)) {WS} (y : both (int WS)) : both A :=
  array_index x (WS := WS) y := lift2_both (fun x y => Hacspec_Lib_Pre.array_index x y) x y.
Fail Next Obligation.

Equations array_upd {A : choice_type} {len} (s: both (nseq_ A len)) (i: both (@int U32)) (new_v: both A) : both (nseq_ A len) :=
  array_upd s i new_v :=
    (lift3_both (fun (s : nseq_ A len) i new_v => Hacspec_Lib_Pre.array_upd s i new_v) s i new_v).

(* substitutes a sequence (seq) into an array (nseq), given index interval  *)
Definition update_sub {A : choice_type} {len slen}  (v : (nseq_ A len)) (i : nat) (n : nat) (sub : (nseq_ A slen)) : both ((nseq_ A len)) :=
  ret_both (update_sub v i n sub).

Program Fixpoint array_from_list_helper {A: choice_type} (x : both A) (xs: list (both A)) (k : nat) {measure (length xs)} : both (nseq_ A (S k)) :=
  match xs with
  | [] => lift1_both (* (H_loc_incl_x := fsubsetxx L) *) (* (H_opsig_incl_x := fsubsetxx I) *) (fun x => setm emptym (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k O))) x : nseq_ A (S k)) x
  | y :: ys =>
      bind_both x (fun temp_x =>
                     bind_both (array_from_list_helper y ys k) (fun temp_y =>
                                                                  lift_both (ret_both (setm (temp_y : nseq_ A (S k)) (Ordinal (ssrbool.introT ssrnat.ltP (lt_succ_diag_r_sub k (length (y :: ys))))) temp_x : nseq_ A (S k)))))
  end.
Solve All Obligations with (intros ; (* time *) (fset_equality || solve_in_fset)).
Fail Next Obligation.

Equations array_from_list {A: choice_type} (l: list (both A))
  : both (nseq_ A (length l)) :=
  array_from_list l :=
    match l as k return both (nseq_ A (length k)) with
      [] => solve_lift (ret_both (tt : nseq_ A 0))
    | (x :: xs) => array_from_list_helper x xs (length xs)
    end.
Solve All Obligations with (intros ; (fset_equality || solve_in_fset)).
Fail Next Obligation.

Program Definition array_from_seq {A: choice_type} (out_len: nat) (input: both (seq A)) : both (nseq_ A out_len) :=
  lift1_both  (* (H_loc_incl_x := fsubsetxx _) (H_opsig_incl_x := fsubsetxx _) *) (array_from_seq out_len) input.

Equations array_to_seq
  {A : choice_type} {n} (f : both (nseq_ A n))
  (* `{H_loc_incl_x : is_true (fsubset L1 L2)} `{H_opsig_incl_x : is_true (fsubset I1 I2)} *) : both (seq A) :=
  array_to_seq := (lift1_both Hacspec_Lib_Pre.array_to_seq).
Fail Next Obligation.

Definition array_from_slice
  {a: choice_type}

  (default_value: ( a))
  (out_len: nat)
  (input: (seq a))
  (start: uint_size)
  (slice_len: uint_size)  : both ((nseq_ a out_len)) :=
  ret_both (array_from_slice default_value out_len input (from_uint_size start) (from_uint_size slice_len)).

Definition array_slice
  {a: choice_type}

  (input: (seq a))
  (start: nat)
  (slice_len: nat)
  : both ((nseq_ a slice_len)) :=
  ret_both (array_slice input start slice_len).

Definition array_from_slice_range
  {a: choice_type}

  (default_value: a)
  (out_len: nat)
  (input: (seq a))
  (start_fin: (uint_size × uint_size))
  : both ((nseq_ a out_len)) :=
  ret_both (array_from_slice_range default_value out_len input start_fin).

Definition array_slice_range
  {a: choice_type}

  {len : nat}
  (input: (nseq_ a len))
  (start_fin:(uint_size × uint_size))
  : both ((seq a)) :=
  ret_both (array_slice_range input start_fin).

Definition array_update
  {a: choice_type}

  {len: nat}
  (s: (nseq_ a len))
             (start : uint_size)
             (start_s: (seq a))
    : both ((nseq_ a len)) :=
    ret_both (array_update s start start_s).

  Definition array_update_start
             {a: choice_type}

             {len: nat}
             (s: (nseq_ a len))
             (start_s: (seq a))
    : both ((nseq_ a len)) :=
    ret_both (array_update_start s start_s).

  Definition array_len  {a: choice_type} {len: nat} (s: (nseq_ a len)) : both (uint_size) := ret_both (array_len s).
  (* May also come up as 'length' instead of 'len' *)
  Definition array_length  {a: choice_type} {len: nat} (s: (nseq_ a len)) : both (uint_size) := ret_both (array_length s).

  Definition array_update_slice
             {a : choice_type}

             {l : nat}
             (out: ( (nseq_ a l)))
             (start_out: uint_size)
             (input: ( (seq a)))
             (start_in: uint_size)
             (len: uint_size)
    : both ((nseq_ a _)) :=
    ret_both (array_update_slice (l := l) out start_out input start_in (from_uint_size len)).

  (**** Numeric operations *)

(* End Arrays. *)
