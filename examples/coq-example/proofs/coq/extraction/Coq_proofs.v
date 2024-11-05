(* Handwritten Proofs *)

From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.

From Coq_example Require Import Coq_example.


(* Check example *)
Example is_example_correct : example tt = [-7]. Proof. reflexivity. Qed.

(* Proof composite operations *)
Theorem dup_mul_is_square : forall x,
    impl__Instruction__interpret Instruction_Mul (
        impl__Instruction__interpret Instruction_Dup [x])
    = [Z.pow x 2].
Proof.
  intros.
  cbn.
  rewrite Z.mul_1_r.
  reflexivity.
Qed.

Theorem push_pop_cancel : forall l x,
    impl__Instruction__interpret Instruction_Pop (
        impl__Instruction__interpret (Instruction_Push x) l)
    = l.
Proof.
  intros.
  cbn.
  reflexivity.
Qed.
