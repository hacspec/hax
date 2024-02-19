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
From Hacspec Require Import Hacspec_Lib_Seq.
From Hacspec Require Import Hacspec_Lib_Natmod.
From Hacspec Require Import Hacspec_Lib_Monad.
From Hacspec Require Import Hacspec_Lib_Ltac.

(*** Hacspec-v2 specific fixes *)

Import choice.Choice.Exports.
Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

(** Should be moved to Hacspec_Lib.v **)
Program Definition int_xI {WS : wsize} (a : (* both  *)(@int WS)) : (* both *) (@int WS) :=
  Hacspec_Lib_Pre.int_add (Hacspec_Lib_Pre.int_mul a ((* lift_to_both *) (@repr WS 2))) ((* lift_to_both *) (@one WS)).
(* Next Obligation. intros ; now do 2 rewrite fsetU0. Defined. *)
(* Next Obligation. intros ; rewrite <- fset0E ; now do 2 rewrite fsetU0. Defined. *)

Program Definition int_xO {WS : wsize} (a : int WS) : int WS :=
  Hacspec_Lib_Pre.int_mul a (@repr WS 2).
(* Next Obligation. intros ; now rewrite fsetU0. Defined. *)
(* Next Obligation. intros ; rewrite <- fset0E ; now rewrite fsetU0. Defined. *)

Definition both_int_one {WS : wsize} : both (@int WS) := ret_both (one).

Open Scope hacspec_scope.
Definition int_num {WS : wsize} := int WS.
Number Notation int_num Pos.of_num_int Pos.to_num_int (via positive mapping [[int_xI] => xI, [int_xO] => xO , [one] => xH]) : hacspec_scope.

Notation "0" := (repr _ 0%Z) : hacspec_scope.

(* Notation U8_t := int8. *)
(* Notation U8 := id. *)
(* Notation U16_t := int16. *)
(* Notation U16 := id. *)
(* Notation U32_t := int32. *)
(* Notation U32 := id. *)
(* Notation U64_t := int64. *)
(* Notation U64 := id. *)
(* Notation U128_t := int128. *)
(* Notation U128 := id. *)

Class Addition (A : choice_type) :=
  add : both A -> both A -> both A.
Notation "a .+ b" := (add a b).
Instance int_add_inst {ws : wsize} : Addition (@int ws) := { add a b := int_add a b }.

Class Subtraction (A : choice_type):=
  sub : both A -> both A -> both A.
Notation "a .- b" := (sub a b (Subtraction := _)).
Instance int_sub_inst {ws : wsize}  (* `{H_loc_fsubset13 : is_true (fsubset L1 L3)} `{H_opsig_fsubset13 : is_true (fsubset I1 I3)} `{H_loc_fsubset23 : is_true (fsubset L2 L3)} `{H_opsig_fsubset23 : is_true (fsubset I2 I3)} *) : Subtraction (@int ws) (* H_loc_fsubset13 H_opsig_fsubset13 H_loc_fsubset23 H_opsig_fsubset23 *) := { sub a b := int_sub (* (H_loc_incl_x := H_loc_fsubset13) (H_opsig_incl_x := H_opsig_fsubset13) (H_loc_incl_y := H_loc_fsubset23) (H_opsig_incl_y := H_opsig_fsubset23) *) a b }.

Class Multiplication A (* `(H_loc_incl1 : is_true (fsubset L1 L3)) (H_opsig_incl1 : is_true (fsubset I1 I3)) (H_loc_incl2 : is_true (fsubset L2 L3)) (H_opsig_incl2 : is_true (fsubset I2 I3)) *) := mul : both A -> both A -> both A.
Notation "a .* b" := (mul a b).
(* Instance array_mul_inst {ws : wsize} {len: uint_size} {} : Multiplication (nseq (@int ws) len) := { mul a b := a array_mul b }. *)
Program Instance int_mul_inst {ws : wsize} : Multiplication (@int ws) := { mul a b := int_mul a b }.
Fail Next Obligation.

Class Xor A := xor : both A -> both A -> both A.
Notation "a .^ b" := (xor a b).

Program Instance int_xor_inst {ws : wsize} : Xor (@int ws) := { xor a b := int_xor a b }.
Fail Next Obligation.

Structure array_or_seq A (len : nat) :=
  { as_nseq :> both (nseq_ A len) ;
    as_seq :> both (seq A) ;
    as_list :> both (chList A)
  }.

Arguments as_seq {_} {_}. (* array_or_seq. *)
Arguments as_nseq {_} {_}. (* array_or_seq. *)
Arguments as_list {_} {_}. (* array_or_seq. *)

Definition array_to_list {A n} := lift1_both (fun x => (@array_to_list A n x) : chList _).

Definition seq_to_list {A} := lift1_both (fun x => (@seq_to_list A x) : chList _).

Definition seq_from_list {A} := lift1_both (fun (x : chList _) => seq_from_list A (x : list _)).

Definition array_from_list' {A} {n : nat} := lift1_both (fun (x : chList A) => @array_from_list' A x n : nseq_ _ _).

Equations nseq_array_or_seq {A len} (val : both (nseq_ A len)) : array_or_seq A len :=
  nseq_array_or_seq val := {| as_seq := array_to_seq val ; as_nseq := val ; as_list := array_to_list val |}.
Solve All Obligations with intros ; exact fset0.
Fail Next Obligation.

Arguments nseq_array_or_seq {A} {len}.
(* Check nseq_array_or_seq. *)
Coercion nseq_array_or_seq : both >-> array_or_seq.
Canonical Structure nseq_array_or_seq.

Definition n_seq_array_or_seq {A} {B} (x : both B)
           `(contra : match B with
                      | chUnit => True
                      | chMap (chFin (@mkpos (S n) _)) (C) => C = A
                      | chMap 'nat (C) => C = A
                      | chList C => C = A
                      | _ => False
                      end) :
  let len := (match B as K return
                    match K with
                    | chUnit => True
                    | chMap (chFin (@mkpos (S n) _)) (C) => C = A
                    | chMap 'nat (C) => C = A
                    | chList C => C = A
                    | _ => False
                    end -> nat
              with
              | chUnit => fun _ => 0%nat
              | chMap (chFin (@mkpos p _)) C =>
                  fun m_contra =>
                    match p as p_ return match p_ with
                                         | O => False
                                         | _ => C = A
                                         end -> nat
                          with
                  | O => fun m_contra => False_rect nat m_contra
                  | S n => fun _ => S n
                  end m_contra
              | chMap 'nat C =>
                  fun m_contra => 3%nat
              | chList C => fun m_contra => 4%nat
              | _ => fun m_contra => False_rect nat m_contra
              end contra) in
  array_or_seq A len.
Proof.
  intros.
  destruct B ; try contradiction contra.
  - change 'unit with (nseq_ A len) in x.
    exact {| as_seq := array_to_seq x ; as_nseq := x; as_list := array_to_list x |}.
  - destruct B1 ; try contradiction contra ; simpl in *.
    + subst.
      change (chMap 'nat A) with (seq A) in x.
      exact ({| as_seq := x ; as_nseq := array_from_seq _ x ; as_list := seq_to_list x |}).
    + destruct n.
      destruct pos.
      * contradiction.
      * subst.
        replace (chMap (chFin _) A) with (nseq_ A len) in x.
        2:{
          simpl.
          f_equal.
          f_equal.
          apply (ssrbool.elimT (positive_eqP _ _)).
          unfold positive_eq.
          apply eqtype.eq_refl.
        }
        exact {| as_seq := array_to_seq x ; as_nseq := x; as_list := array_to_list x |}.
  - subst.
    exact {| as_seq := seq_from_list x ; as_nseq := array_from_list' x ; as_list := x |}.
Defined.

Notation " x '.a[' a ']'" := (array_index (n_seq_array_or_seq x _) a) (at level 40).

Fail Next Obligation.
Notation " x '.a[' i ']<-' a" := (array_upd x i a) (at level 40).

Notation update_at := array_upd.
Notation update_at_usize := array_upd.

(* Definition update {A : Type}  `{Default A} {len slen} (s : nseq A len) {WS} (start : @int WS) (start_a : array_or_seq A slen) : nseq A len := *)
(* array_update (a := A) (len := len) s (unsigned start) (as_seq start_a). *)

(* Definition to_le_U32s {A l} := array_to_le_uint32s (A := A) (l := l). *)
(* Axiom to_le_bytes : forall {ws : wsize} {len}, nseq (@int ws) len -> seq int8. *)
(* Definition from_seq {A : Type}  `{Default A} {len slen} (s : array_or_seq A slen) : nseq A len := array_from_seq _ (as_seq s). *)

Notation t_Seq := seq.
(* Notation len := (fun s => seq_len s : int32). *)

(* Definition array_slice {a: Type} `{Default a} {len : nat} (input: nseq a len) {WS} (start: @int WS) (slice_len: @int WS) : seq a := slice (array_to_seq input) (unsigned start) (unsigned (start .+ slice_len)). *)
(* Notation slice := array_slice. *)
(* Definition seq_new {A: Type} `{Default A} {WS} (len: @int WS) : seq A := seq_new (unsigned len). *)
(* Notation new := seq_new. *)
Notation num_exact_chunks := seq_num_exact_chunks.
Notation get_exact_chunk := seq_get_exact_chunk.
(* Definition set_chunk {a: Type} `{Default a} {len} (s: seq a) {WS} (chunk_len: @int WS) (chunk_num: @int WS) (chunk: array_or_seq a len) : seq a := seq_set_chunk s (unsigned chunk_len) (unsigned chunk_num) (as_seq chunk). *)
(* Definition set_exact_chunk {a} `{H : Default a} {len} s {WS} := @set_chunk a H len s WS. *)
Notation get_remainder_chunk := seq_get_remainder_chunk.
Notation "a <> b" := (negb (eqb a b)).

Notation from_secret_literal := nat_mod_from_secret_literal.
(* Definition pow2 {m} (x : @int wsize32) := nat_mod_pow2 m (unsigned x). *)
(* Instance nat_mod_addition {n} : Addition (nat_mod n) := { add a b := a +% b }. *)
(* Instance nat_mod_subtraction {n} : Subtraction (nat_mod n) := { sub a b := a -% b }. *)
(* Instance nat_mod_multiplication {n} : Multiplication (nat_mod n) := { mul a b := a *% b }. *)
(* Definition from_slice {a: Type} `{Default a} {len slen} (x : array_or_seq a slen) {WS} (start: @int WS) (slice_len: @int WS) := array_from_slice default len (as_seq x) (unsigned start) (unsigned slice_len). *)
Notation zero := nat_mod_zero.
Notation to_byte_seq_le := nat_mod_to_byte_seq_le.
Notation U128_to_le_bytes := u128_to_le_bytes.
Notation U64_to_le_bytes := u64_to_le_bytes.
     Notation from_byte_seq_le := nat_mod_from_byte_seq_le.
Definition from_literal {m} := nat_mod_from_literal m.
Notation inv := nat_mod_inv.
Notation update_start := array_update_start.
Notation pow := nat_mod_pow_self.
Notation bit := nat_mod_bit.

(* Definition int_to_int {ws1 ws2} (i : @int ws1) : @int ws2 := repr (unsigned i). *)
(* Coercion int_to_int : int >-> int. *)
(* Notation push := seq_push. *)
Notation Build_secret := secret.
Notation "a -× b" :=
(prod a b) (at level 80, right associativity) : hacspec_scope.
Notation Result_t := result.
Axiom TODO_name : Type.
Notation ONE := nat_mod_one.
Notation exp := nat_mod_exp.
(* Notation nat_mod := GZnZ.znz. *)
(* Instance nat_mod_znz_addition {n} : Addition (GZnZ.znz n) := { add a b := a +% b }. *)
(* Instance nat_mod_znz_subtraction {n} : Subtraction (GZnZ.znz n) := { sub a b := a -% b }. *)
(* Instance nat_mod_znz_multiplication {n} : Multiplication (GZnZ.znz n) := { mul a b := a *% b }. *)
Notation TWO := nat_mod_two.
Notation ne := (fun x y => negb (eqb x y)).
Notation eq := (eqb).
Notation rotate_right := (ror).
Notation to_be_U32s := array_to_be_uint32s.
Notation get_chunk := seq_get_chunk.
Notation num_chunks := seq_num_chunks.
Notation U64_to_be_bytes := uint64_to_be_bytes.
Notation to_be_bytes := array_to_be_bytes.
Notation U8_from_usize := uint8_from_usize.
Notation concat := seq_concat.
Notation declassify := id.
Notation U128_from_be_bytes := uint128_from_be_bytes.
Notation U128_to_be_bytes := uint128_to_be_bytes.
Notation slice_range := array_slice_range.
Notation truncate := seq_truncate.
(* Axiom array_to_be_uint64s : forall {A l}, nseq A l -> seq uint64. *)
Notation to_be_U64s := array_to_be_uint64s.
Notation classify := id.
Notation U64_from_U8 := uint64_from_uint8.
(* Definition Build_Range_t (a b : nat) := (a,b). (* match (b - a)%nat with O => [] | S n => match b with | O => [] | S b' => Build_Range_t a b' ++ [b] end end. *) *)

Definition Build_t_Range {WS} {f_start : both (int WS)} {f_end : both (int WS)} := prod_b (f_start,f_end).
Notation Build_Range  := Build_t_Range.

Notation declassify_eq := eq.
Notation String_t := String.string.

Notation "'i8(' v ')'" := (ret_both (v : int8) : both _).
Notation "'i16(' v ')'" := (ret_both (v : int16) : both _).
Notation "'i32(' v ')'" := (ret_both (v : int32) : both _).
Notation "'i64(' v ')'" := (ret_both (v : int64) : both _).
Notation "'i128(' v ')'" := (ret_both (v : int128) : both _).

Definition (* vec_ *)len {A ws} := lift1_both  (fun (x : chList A) => repr ws (List.length x)).

Definition andb (x : both 'bool) (y : both 'bool) : both 'bool := lift2_both (fun (x y : 'bool) => Datatypes.andb x y : 'bool) x y.
Definition negb (x : both 'bool) : both 'bool := lift1_both (fun (x : 'bool) => Datatypes.negb x : 'bool) x.
Notation "a <> b" := (negb (eqb a b)).
Notation "'not'" := (negb).
Notation "x ':of:' y" := (x : both _ _ y) (at level 100).
Notation "x ':of0:' y" := (x : both y) (at level 100).

Class t_Serialize (Self : choice_type).
Class t_Deserial (Self : choice_type).
Class t_Serial (Self : choice_type).
Notation "'t_Eq'" := (EqDec).
(** end of: Should be moved to Hacspec_Lib.v **)

Definition t_Result A B := result B A.

(** Should be part of core.V **)

Class t_Sized (A : choice_type) := Sized : A -> A.
Class t_TryFrom (A : choice_type) := TryFrom : A -> A.
Class t_Into (A : choice_type) := Into : A -> A.
Class t_PartialEq (A : choice_type) := PartialEq : A -> A.
Class t_Copy (A : choice_type) := Copy : A -> A.
Class t_Clone (A : choice_type) := Clone : A -> A.
Definition t_Option : choice_type -> choice_type := chOption.
Inductive vec_typ :=
| t_Global.
Definition t_Vec : choice_type -> vec_typ -> choice_type := fun A _ => chList A.

Notation t_Default := Default.
(* Class t_Default A := { default : A }. *)

#[global] Instance bool_copy : t_Copy 'bool := {Copy x := x}.
#[global] Instance bool_clone : t_Clone 'bool := {Clone x := x}.
#[global] Instance bool_sized : t_Sized 'bool := {Sized x := x}.

Definition ilog2 {WS} (x : both (int WS)) : both (int WS) := x. (* TODO *)

Definition collect {A} (x : both (chList A)) : both (t_Vec A t_Global) := x.


Equations swap_both_list {A} (x : list (both A)) : both (chList A) :=
  swap_both_list x :=
  (List.fold_left (fun (x : both (chList A)) y =>
   bind_both x (fun x' =>
   bind_both y (fun y' =>
   solve_lift (ret_both ((y' :: x') : chList A))))) x (solve_lift (ret_both ([] : chList A)))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Equations match_list {A B : choice_type} (x : both (chList A)) (f : list A -> B) : both B :=
  match_list x f :=
  bind_both x (fun x' => solve_lift (ret_both (f x'))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Equations map {A B} (x : both (chList A))  (f : both A -> both B) : both (chList B) :=
  map x f :=
  bind_both x (fun x' => swap_both_list (List.map (fun y => f (solve_lift (ret_both y))) x')).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Definition cloned {A} (x : both (chList A)) : both (chList A) := x.

Equations iter {A} (x : both (seq A)) : both (chList A) :=
  iter x :=
  bind_both x (fun x' => solve_lift (ret_both (Hacspec_Lib_Pre.seq_to_list _ x' : chList A))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Definition dedup {A} (x : both (t_Vec A t_Global)) : both (t_Vec A t_Global) := x.

Definition t_String := Coq.Strings.String.string.
Equations new {A} : both (t_Vec A t_Global) :=
  new := solve_lift (ret_both ([] : chList A)).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Definition enumerate {A} (x : both (t_Vec A t_Global)) : both (t_Vec A t_Global) := x.

(*** More functions *)
Definition t_Drain : choice_type -> vec_typ -> choice_type := t_Vec.
Inductive t_Range := RangeFull.
Equations drain : forall {A}, both (t_Vec A t_Global) -> t_Range -> both (t_Drain A t_Global × t_Vec A t_Global) :=
  drain x _ :=
    bind_both x (fun x' => solve_lift (ret_both ((x', []) : (t_Drain A t_Global × t_Vec A t_Global)))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.
Notation t_Rev := id.
Equations rev {A} (x : both (chList A)) : both (chList A) := rev x := bind_both x (fun x => solve_lift (ret_both (List.rev x : chList _))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.

Definition pop {A} : both (chList A) -> both (chOption A × t_Vec A (t_Global)) :=
  lift1_both (fun (x : chList A) => (List.hd_error x , List.tl x) : (chOption A × t_Vec A (t_Global))).

Definition push {A} : both (t_Vec A t_Global) -> both A -> both (t_Vec A (t_Global)) :=
  lift2_both (fun  (x : chList A) y => y :: x : chList A).

Notation Option_Some := Some.
Definition append {A : choice_type} (l : both (chList A)) (x : both (chList A)) : both (chList A × chList A) :=
  lift2_both (fun (x : chList A) (y : chList A) => (app y x, []) : chList A × chList A) x l.

Notation f_clone := id.
Definition seq_unzip {A B} (s : chList (A × B)) : chList A × chList B := (seq.unzip1 s, seq.unzip2 s).
Definition unzip {A B} : both (chList (A × B)) -> both (chList A × chList B) := lift1_both seq_unzip.
Equations deref {A} : both (t_Vec A t_Global) -> both (seq A) :=
  deref X := bind_both X (fun x : t_Vec A t_Global => solve_lift (ret_both (Hacspec_Lib_Pre.seq_from_list A x))).
Solve All Obligations with solve_ssprove_obligations.
Fail Next Obligation.
Definition t_Never : choice_type := 'unit.
Definition abort : both t_Never := ret_both (tt : 'unit).

(* Notation v_Break := id. *)
Notation Result_Err := Err.
Notation Result_Ok := Ok.

Notation "'ret_both' 'tt'" := (ret_both (tt : 'unit)).

(** Should be part of concordium.v **)
Class HasInitContext (Self : choice_type).
Class t_HasInitContext (Self : choice_type) (something : choice_type).
Class t_HasActions (Self : choice_type) := {f_accept : both Self}.
Class HasReceiveContext (Self : choice_type).
Definition t_ParamType := 'unit.
Definition t_ParseError := 'unit.
(* (t_RegisterParam) *)
Class t_HasReceiveContext (Self : choice_type) (something : choice_type) := { f_get : forall {Ctx}, both (t_ParamType × t_Result Ctx (t_ParseError)) }.
Arguments f_get {Self} {something} (t_HasReceiveContext) {Ctx}.

Definition f_parameter_cursor {T : _} `{ t_Sized (T)} `{ t_HasReceiveContext (T) ('unit)} `{ t_Sized (T)} `{ t_HasReceiveContext (T) ('unit)} (ctx : both (T)) : t_HasReceiveContext (T) ('unit) := _.

Notation ControlFlow_Continue := Result_Ok.
Notation v_Break := Result_Err.
Notation never_to_any := id.
Equations run {A} (x : both (choice_typeMonad.M (CEMonad := (@choice_typeMonad.mnd (choice_typeMonad.result_bind_code A))) A)) : both A :=
  run x :=
  bind_both x (fun y => match y with
                             | inl r | inr r => solve_lift ret_both r
                             end).
Fail Next Obligation.


Notation "'matchb' x 'with' '|' a '=>' b 'end'" :=
  (bind_both x (fun y => match y with
                      | a => b end)) (at level 100, a pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d  'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d end)) (at level 100, a pattern, c pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d '|' e '=>' f  'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d
                      | e => f end)) (at level 100, a pattern, c pattern, e pattern).

Notation "'matchb' x 'with' '|' a '=>' b '|' c '=>' d '|' e '=>' f '|' g '=>' h 'end'" :=
  (bind_both x (fun y => match y with
                      | a => b
                      | c => d
                      | e => f
                      | g => h end)) (at level 100, a pattern, c pattern, e pattern, g pattern).

Notation f_branch := id.
Notation ControlFlow_Break_case := inr.
Notation ControlFlow_Continue_case := inl.

Notation f_from_residual := Result_Err.

Ltac remove_duplicate_pair :=
  normalize_fset ;
  repeat match goal with
  | |- context G [(?a :|: (?a :|: ?c))] =>
      replace (a :|: (a :|: c)) with (a :|: a :|: c) by (now rewrite <- fsetUA) ; rewrite fsetUid
  end.


Axiom t_Reject : choice_type.
Equations repeat {A} (e : both A) (n : both uint_size) : both (nseq A (is_pure n)) :=
  repeat e n :=
 (eq_rect
       (Datatypes.length (List.repeat (solve_lift e) (Z.to_nat (unsigned (is_pure n)))))
       (fun n0 : nat => both (nseq_ A n0)) (bind_both e
       (fun _ : A =>
        array_from_list (List.repeat (solve_lift e) (Z.to_nat (unsigned (is_pure n)))))
)
       (Z.to_nat (unsigned (is_pure n)))
       (List.repeat_length (solve_lift e) (Z.to_nat (unsigned (is_pure n))))).
Fail Next Obligation.

Class iterable (A B : choice_type) := {f_into_iter : both A -> both (chList B)}.
Instance nseq_iterable : iterable (nseq int32 20) int32 := {| f_into_iter := array_to_list |}.
Program Instance range_iterable {WS} : iterable ((int WS) × (int WS)) (int WS) :=
  {| f_into_iter :=
    fun x =>
      bind_both x (fun '((a, b) : int WS × int WS) => solve_lift (ret_both (List.map (fun x => repr WS (Z.of_nat x)) (List.seq (Z.to_nat (unsigned a)) (Z.to_nat (unsigned (b))-Z.to_nat (unsigned a))) : chList (int WS) )))
  |}.
Fail Next Obligation.
Notation t_IntoIter := (chList _).

Definition t_Amount := int64.

Definition impl_20__contains_key := int64.
Definition f_micro_ccd := int64.
Equations Build_t_Amount {f_micro_ccd : both int64} : both (t_Amount) :=
  Build_t_Amount  :=
    bind_both f_micro_ccd (fun f_micro_ccd =>
                             solve_lift (ret_both ((f_micro_ccd) : (t_Amount)))) : both (t_Amount).
Fail Next Obligation.
Definition t_Timestamp := int32.
Definition t_BTreeMap (A B : Type) (C : vec_typ) := int32.
Definition f_slot_time := int64.
Definition f_metadata := int64.
Definition t_AccountAddress : choice_type := int64 ∐ int64.
Definition Address_Contract_case (addr : int64) : t_AccountAddress := inl addr.
Definition Address_Account_case (addr : int64) : t_AccountAddress := inr addr.
Definition f_sender : t_AccountAddress :=
  Address_Account_case 0.

(* From ovn *)
Notation f_into_iter_loc := fset0.
Notation f_end_loc := fset0.
Notation f_start_loc := fset0.
Notation f_eq_loc := fset0.
Equations impl__into_vec {A n} : both (nseq_ A n) -> both (t_Vec A t_Global) :=
  impl__into_vec X := bind_both X (fun x : nseq_ A n => solve_lift (ret_both (Hacspec_Lib_Pre.array_to_list x : chList _))).
Fail Next Obligation.

Definition unsize {A} := @id A.
Definition box_new {A} := @id A.

Notation f_get_loc := fset0.
Notation f_clone_loc := fset0.
Notation f_accept_loc := fset0.
Notation f_parameter_cursor_loc := fset0.

Notation Result_Ok_case := inl.
Notation Result_Err_case := inr.
