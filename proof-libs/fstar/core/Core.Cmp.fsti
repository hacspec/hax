module Core.Cmp
open Rust_primitives

class min_tc t = {
  min: t -> t -> t
}

instance min_inttype (#t:inttype): min_tc (int_t t) = {
  min = fun a b -> if a <. b then a else b
}

class t_PartialEq (v_Self: Type) (v_Rhs: Type) = {
  // __constraint_1069563329_t_PartialEq:t_PartialEq v_Self v_Rhs;
  f_eq_pre: v_Self -> v_Rhs -> Type0;
  f_eq_post: v_Self -> v_Rhs -> bool -> Type0;
  f_eq:v_Self -> v_Rhs -> bool;
}

class t_Eq (v_Self: Type) = {
  [@@@FStar.Tactics.Typeclasses.tcresolve]
  __constraint_t_Eq_t_PartialEq:t_PartialEq v_Self v_Self;
}

type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering


class t_PartialOrd (v_Self: Type) (v_Rhs:Type) = {
  _super_9014672428308350468: t_PartialEq v_Self v_Rhs;
  f_partial_cmp_pre: v_Self -> v_Rhs -> Type0;
  f_partial_cmp_post: v_Self -> v_Rhs -> option t_Ordering -> Type0;
  f_partial_cmp:v_Self -> v_Rhs -> option t_Ordering;
}

class t_Ord (v_Self: Type) = {
  _super_8099741844003281729: t_Eq v_Self;
  _super_12866954522599331834: t_PartialOrd v_Self v_Self;
  f_cmp_pre: v_Self -> v_Self -> Type0;
  f_cmp_post: v_Self -> v_Self -> t_Ordering -> Type0;
  f_cmp:v_Self -> v_Self -> t_Ordering;
  // f_max:v_Self -> v_Self -> v_Self;
  // f_min:v_Self -> v_Self -> v_Self;
  // f_clamp:v_Self -> v_Self -> v_Self -> v_Self
}

instance all_eq (a: eqtype): t_PartialEq a a = {
  f_eq_pre = (fun x y -> True);
  f_eq_post = (fun x y r -> True);
  f_eq = (fun x y -> x = y);
}

type t_Reverse t = | Reverse of t

let impl__then x y = x

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_u64: t_Ord u64

[@FStar.Tactics.Typeclasses.tcinstance]
val ord_reverse t {| t_Ord t |}: t_Ord (t_Reverse t)
