(* File automatically generated by Hacspec *)
From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Require Import Ascii.
Require Import String.
Require Import Coq.Floats.Floats.
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.



From Coq_example Require Import dummy_core_lib.
Export dummy_core_lib.

Inductive t_Instruction : Type :=
| Instruction_Push : t_isize -> _
| Instruction_Pop
| Instruction_Add
| Instruction_Sub
| Instruction_Mul
| Instruction_Not
| Instruction_Dup.
Arguments t_Instruction:clear implicits.
Arguments t_Instruction.

(* NotImplementedYet *)

(* NotImplementedYet *)

Definition impl__Instruction__interpret (self : t_Instruction) (stack : t_Vec ((t_isize)) ((t_Global))) : t_Vec ((t_isize)) ((t_Global)) :=
  let (stack,hax_temp_output) := match self with
  | Instruction_Push (v) =>
    (impl_1__push (stack) (v),tt)
  | Instruction_Pop =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let _ := out in
    (stack,tt)
  | Instruction_Add =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist2 := out in
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist1 := out in
    let hoist3 := (hoist2,hoist1) in
    match hoist3 with
    | (Option_Some (a),Option_Some (b)) =>
      (impl_1__push (stack) (t_Add_f_add (b) (a)),tt)
    | _ =>
      (stack,tt)
    end
  | Instruction_Sub =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist5 := out in
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist4 := out in
    let hoist6 := (hoist5,hoist4) in
    match hoist6 with
    | (Option_Some (a),Option_Some (b)) =>
      (impl_1__push (stack) (sub (b) (a)),tt)
    | _ =>
      (stack,tt)
    end
  | Instruction_Mul =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist8 := out in
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist7 := out in
    let hoist9 := (hoist8,hoist7) in
    match hoist9 with
    | (Option_Some (a),Option_Some (b)) =>
      (impl_1__push (stack) (t_Mul_f_mul (b) (a)),tt)
    | _ =>
      (stack,tt)
    end
  | Instruction_Not =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist10 := out in
    match hoist10 with
    | Option_Some (a) =>
      (impl_1__push (stack) (if
        t_PartialEq_f_eq (a) (0)
      then
        1
      else
        0),tt)
    | _ =>
      (stack,tt)
    end
  | Instruction_Dup =>
    let (tmp0,out) := impl_1__pop (stack) in
    let stack := tmp0 in
    let hoist11 := out in
    match hoist11 with
    | Option_Some (a) =>
      let stack := impl_1__push (stack) (a) in
      let stack := impl_1__push (stack) (a) in
      (stack,tt)
    | _ =>
      (stack,tt)
    end
  end in
  stack.

Definition example (_ : unit) : t_Vec ((t_isize)) ((t_Global)) :=
  let stk := impl__new (tt) in
  let stk := f_fold (f_into_iter ([Instruction_Push (1); Instruction_Push (1); Instruction_Add; Instruction_Push (1); Instruction_Push (1); Instruction_Push (1); Instruction_Add; Instruction_Add; Instruction_Dup; Instruction_Mul; Instruction_Sub])) (stk) (fun stk cmd =>
    impl__Instruction__interpret (cmd) (stk)) in
  stk.