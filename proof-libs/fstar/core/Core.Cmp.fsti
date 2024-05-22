module Core.Cmp
open Rust_primitives

class min_tc t = {
  min: t -> t -> t
}

instance min_inttype (#t:inttype): min_tc (int_t t) = {
  min = fun a b -> if a <. b then a else b
}

type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering

class t_Ord (v_Self: Type) = {
  f_cmp:v_Self -> v_Self -> t_Ordering;
  // f_max:v_Self -> v_Self -> v_Self;
  // f_min:v_Self -> v_Self -> v_Self;
  // f_clamp:v_Self -> v_Self -> v_Self -> v_Self
}

class t_PartialEq (v_Self: Type) (v_Rhs: Type) = {
  // __constraint_1069563329_t_PartialEq:t_PartialEq v_Self v_Rhs;
  f_eq:v_Self -> v_Rhs -> bool;
  f_ne:v_Self -> v_Rhs -> bool
}

instance all_eq (a: eqtype): t_PartialEq a a = {
  f_eq = (fun x y -> x = y);
  f_ne = (fun x y -> x <> y);
}

class t_PartialOrd (v_Self: Type) (v_Rhs: Type) = {
  __constraint_Rhs_t_PartialEq:t_PartialEq v_Self v_Rhs;
  // __constraint_Rhs_t_PartialOrd:t_PartialOrd v_Self v_Rhs;
  f_partial_cmp:v_Self -> v_Rhs -> Core.Option.t_Option t_Ordering;
  // f_lt:v_Self -> v_Rhs -> bool;
  // f_le:v_Self -> v_Rhs -> bool;
  // f_gt:v_Self -> v_Rhs -> bool;
  // f_ge:v_Self -> v_Rhs -> bool
}

type t_Reverse t = | Reverse of t

let impl__then x y = x

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_u64: t_Ord u64

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_reverse t {| t_Ord t |}: t_Ord (t_Reverse t)
