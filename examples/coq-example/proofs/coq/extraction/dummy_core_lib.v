From Coq Require Import ZArith.
Require Import List.
Import List.ListNotations.
Open Scope Z_scope.

(* LIBRARY CODE *)
Definition t_isize := Z.
Notation "'t_Vec' T '((t_Global))'" := (list T).
Definition impl_1__push {A} (l : list A) (a : A) : list A := cons a l.
Definition impl_1__pop {A} (l : list A) : list A * option A :=
  match l with
  | [] => ([], None)
  | (x :: xs) => (xs, Some x)
  end.
Definition impl__unwrap {A} (x : option A) `{H : x <> None} : A :=
  match x as k return k <> None -> _ with
  | None => fun H => False_rect _ (H eq_refl)
  | Some a => fun _ => a
  end H.
Definition t_Add_f_add := (fun x y => x + y).
Definition t_Mul_f_mul := (fun x y => x * y).
Definition t_PartialEq_f_eq := (fun x y => x =? y).
Definition impl__isize__rem_euclid := fun x y => x mod y.
Definition cast := fun (x : Z) => x.
Definition ne := fun x y => negb (x =? y).
Definition impl_1__len {A} (l : list A) := Z.of_nat (List.length l).
Definition t_PartialOrd_f_lt := fun x y => x <? y.
Notation "'Option_Some'" := Some.
Notation "'Option_None'" := None.
Definition sub := fun x y => x - y.
Definition impl__new {A} (tt : unit) : list A := [].
Definition f_fold {A B} (l : list A) (i : B) (f : B -> A -> B) : B := List.fold_left f l i.
Definition f_into_iter {A} := @id A.
(* /LIBRARY CODE *)
