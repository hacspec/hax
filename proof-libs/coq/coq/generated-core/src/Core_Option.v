(* File automatically generated by Hacspec *)
From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.

Require Import panic.
Export panic.

Require Import panic_display.
Export panic_display.

Inductive t_Option (T : _) : Type :=
| Option_None : t_Option (T : _)
| Option_Some : T -> t_Option (T : _).
Arguments Option_None {_}.
Arguments Option_Some {_} T.

#[global] Instance t_Option_t T_t_Clone (T : _) : t_Clone (t_Option_t T) := {
  f_clone (self : t_Option_t T) := match self with
  | Option_Some x =>
    Option_Some (f_clone x)
  | Option_None  =>
    Option_Nonet_Option_t T
  end;
}.

Definition impl_1__is_some (self : t_Option_t T) : bool :=
  match self with
  | Option_Some _ =>
    true
  | _ =>
    false
  end.

Definition impl_1__map (self : t_Option_t T) (f : F) : t_Option_t U :=
  match self with
  | Option_Some x =>
    Option_Some (f_call_once f x)
  | Option_None  =>
    Option_Nonet_Option_t U
  end.

Definition unwrap_failed (_ : unit) : t_Never_t :=
  panic called `Option::unwrap()` on a `None` value.

Definition impl_1__unwrap (self : t_Option_t T) : T :=
  match self with
  | Option_Some val =>
    val
  | Option_None  =>
    never_to_any (unwrap_failed tt)
  end.

(*item error backend*)

(*item error backend*)