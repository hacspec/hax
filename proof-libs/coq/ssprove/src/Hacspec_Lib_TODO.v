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

From Hacspec Require Import Hacspec_Lib_Integers.
From Hacspec Require Import Hacspec_Lib_Seq.
From Hacspec Require Import Hacspec_Lib_Natmod.
From Hacspec Require Import Hacspec_Lib_Monad.
From Hacspec Require Import Hacspec_Lib_Ltac.

(*** Result *)

Definition Ok {a b : choice_type} : both a -> both (result b a) := lift1_both Ok.
Definition Err {a b : choice_type} : both b -> both (result b a) := lift1_both Err.

Infix "&&" := andb : bool_scope.
Infix "||" := orb : bool_scope.

Definition u32_word_t := nseq_ uint8 4.
Definition u128_word_t := nseq_ uint8 16.

(*** Hacspec-v2 specific fixes *)

Import choice.Choice.Exports.
Obligation Tactic := (* try timeout 8 *) solve_ssprove_obligations.

(** Should be moved to Hacspec_Lib.v **)
Program Definition int_xI {WS : wsize} (a : (@int WS)) : (@int WS) :=
  Hacspec_Lib_Pre.int_add (Hacspec_Lib_Pre.int_mul a (@repr WS 2)) (@one WS).

Program Definition int_xO {WS : wsize} (a : int WS) : int WS :=
  Hacspec_Lib_Pre.int_mul a (@repr WS 2).

Definition both_int_one {WS : wsize} : both (@int WS) := ret_both (one).

Open Scope hacspec_scope.
Definition int_num {WS : wsize} := int WS.
Number Notation int_num Pos.of_num_int Pos.to_num_int (via positive mapping [[int_xI] => xI, [int_xO] => xO , [one] => xH]) : hacspec_scope.

Notation "0" := (repr _ 0%Z) : hacspec_scope.

Class Addition (A : choice_type) :=
  add : both A -> both A -> both A.
Notation "a .+ b" := (add a b).
Instance int_add_inst {ws : wsize} : Addition (@int ws) := { add a b := int_add a b }.

Class Subtraction (A : choice_type):=
  sub : both A -> both A -> both A.
Notation "a .- b" := (sub a b (Subtraction := _)).
Instance int_sub_inst {ws : wsize} : Subtraction (@int ws) := { sub a b := int_sub a b }.

Class Multiplication A := mul : both A -> both A -> both A.
Notation "a .* b" := (mul a b).
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

Notation t_Seq := seq.
Notation num_exact_chunks := seq_num_exact_chunks.
Notation get_exact_chunk := seq_get_exact_chunk.

Notation get_remainder_chunk := seq_get_remainder_chunk.
Notation "a <> b" := (negb (eqb a b)).

Notation from_secret_literal := nat_mod_from_secret_literal.

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

Notation Build_secret := secret.
Notation "a -× b" :=
(prod a b) (at level 80, right associativity) : hacspec_scope.
Notation Result_t := result.
Axiom TODO_name : Type.
Notation ONE := nat_mod_one.
Notation exp := nat_mod_exp.

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

Notation to_be_U64s := array_to_be_uint64s.
Notation classify := id.
Notation U64_from_U8 := uint64_from_uint8.

Definition Build_t_Range {WS} {f_start : both (int WS)} {f_end : both (int WS)} := prod_b (f_start,f_end).
Notation Build_Range  := Build_t_Range.

Notation declassify_eq := eq.
Notation String_t := String.string.

Notation "'i8(' v ')'" := (ret_both (v : int8) : both _).
Notation "'i16(' v ')'" := (ret_both (v : int16) : both _).
Notation "'i32(' v ')'" := (ret_both (v : int32) : both _).
Notation "'i64(' v ')'" := (ret_both (v : int64) : both _).
Notation "'i128(' v ')'" := (ret_both (v : int128) : both _).

Definition len {A ws} := lift1_both  (fun (x : chList A) => repr ws (List.length x)).

Definition orb (x : both 'bool) (y : both 'bool) : both 'bool := lift2_both (fun (x y : 'bool) => Datatypes.orb x y : 'bool) x y.
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
Class t_PartialEq (A : choice_type) (B : choice_type) := PartialEq : A -> B -> bool.
Class t_Copy (A : choice_type) := Copy : A -> A.
Class t_Clone (A : choice_type) := Clone : A -> A.
Definition t_Option : choice_type -> choice_type := chOption.
Inductive vec_typ :=
| t_Global.
Definition t_Vec : choice_type -> vec_typ -> choice_type := fun A _ => chList A.

Notation t_Default := Default.

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
Instance nseq_iterable_seq {A n} : iterable (nseq A n) A := {| f_into_iter := array_to_list |}.
Program Instance range_iterable {WS} : iterable ((int WS) × (int WS)) (int WS) :=
  {| f_into_iter :=
    fun x =>
      bind_both x (fun '((a, b) : int WS × int WS) => solve_lift (ret_both (List.map (fun x => repr WS (Z.of_nat x)) (List.seq (Z.to_nat (unsigned a)) (Z.to_nat (unsigned (b))-Z.to_nat (unsigned a))) : chList (int WS) )))
  |}.
Fail Next Obligation.
Notation t_IntoIter := (chList _).
Instance nseq_iterable_vec {A n} : iterable (t_Vec A n) A := {| f_into_iter := fun x => x |}.

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

Definition impl__map_err {A B C : choice_type} (r : both (t_Result A B)) (f : B -> C) : both (t_Result A C) :=
  matchb r with
  | inl a => ret_both (inl a : t_Result A C)
  | inr b => ret_both (inr (f b) : t_Result A C)
end.
Axiom f_from : forall {A B}, A -> B. (* TODO *)
