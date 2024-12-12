module Core.Cmp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let discriminant_Ordering_Equal: i8 = 0y

let discriminant_Ordering_Greater: i8 = 1y

type t_Ordering =
  | Ordering_Less : t_Ordering
  | Ordering_Equal : t_Ordering
  | Ordering_Greater : t_Ordering

let impl__Ordering__is_eq (self: t_Ordering) : bool =
  match self with
  | Ordering_Equal  -> true
  | _ -> false

let impl__Ordering__is_gt (self: t_Ordering) : bool =
  match self with
  | Ordering_Greater  -> true
  | _ -> false

let impl__Ordering__is_lt (self: t_Ordering) : bool =
  match self with
  | Ordering_Less  -> true
  | _ -> false

let impl__Ordering__reverse (self: t_Ordering) : t_Ordering =
  match self with
  | Ordering_Less  -> Ordering_Greater <: t_Ordering
  | Ordering_Equal  -> Ordering_Equal <: t_Ordering
  | Ordering_Greater  -> Ordering_Less <: t_Ordering

let discriminant_Ordering_Less: i8 = (-1y)

let t_Ordering_cast_to_repr (x: t_Ordering) : i8 =
  match x with
  | Ordering_Less  -> discriminant_Ordering_Less
  | Ordering_Equal  -> discriminant_Ordering_Equal
  | Ordering_Greater  -> discriminant_Ordering_Greater

class t_PartialEq (v_Self: Type0) (v_Rhs: Type0) = {
  f_eq_pre:v_Self -> v_Rhs -> Type0;
  f_eq_post:v_Self -> v_Rhs -> bool -> Type0;
  f_eq:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_eq_pre x0 x1) (fun result -> f_eq_post x0 x1 result);
  f_ne_pre:v_Self -> v_Rhs -> Type0;
  f_ne_post:v_Self -> v_Rhs -> bool -> Type0;
  f_ne:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_ne_pre x0 x1) (fun result -> f_ne_post x0 x1 result)
}

let impl__Ordering__is_ge (self: t_Ordering) : bool =
  ~.(match self with
    | Ordering_Less  -> true
    | _ -> false)

let impl__Ordering__is_le (self: t_Ordering) : bool =
  ~.(match self with
    | Ordering_Greater  -> true
    | _ -> false)

let impl__Ordering__is_ne (self: t_Ordering) : bool =
  ~.(match self with
    | Ordering_Equal  -> true
    | _ -> false)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_PartialEq t_Ordering t_Ordering =
  {
    f_eq_pre = (fun (self: t_Ordering) (other: t_Ordering) -> true);
    f_eq_post = (fun (self: t_Ordering) (other: t_Ordering) (out: bool) -> true);
    f_eq
    =
    (fun (self: t_Ordering) (other: t_Ordering) ->
        match self with
        | Ordering_Less  ->
          (match other with
            | Ordering_Less  -> true
            | _ -> false)
        | Ordering_Equal  ->
          (match other with
            | Ordering_Equal  -> true
            | _ -> false)
        | Ordering_Greater  ->
          match other with
          | Ordering_Greater  -> true
          | _ -> false);
    f_ne_pre = (fun (self: t_Ordering) (other: t_Ordering) -> true);
    f_ne_post = (fun (self: t_Ordering) (other: t_Ordering) (out: bool) -> true);
    f_ne
    =
    fun (self: t_Ordering) (other: t_Ordering) ->
      ~.(match self with
        | Ordering_Less  ->
          (match other with
            | Ordering_Less  -> true
            | _ -> false)
        | Ordering_Equal  ->
          (match other with
            | Ordering_Equal  -> true
            | _ -> false)
        | Ordering_Greater  ->
          match other with
          | Ordering_Greater  -> true
          | _ -> false)
  }

class t_PartialOrd (v_Self: Type0) (v_Rhs: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9014672428308350468:t_PartialEq v_Self v_Rhs;
  f_partial_cmp_pre:v_Self -> v_Rhs -> Type0;
  f_partial_cmp_post:v_Self -> v_Rhs -> Core.Option.t_Option t_Ordering -> Type0;
  f_partial_cmp:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure (Core.Option.t_Option t_Ordering)
        (f_partial_cmp_pre x0 x1)
        (fun result -> f_partial_cmp_post x0 x1 result);
  f_lt_pre:v_Self -> v_Rhs -> Type0;
  f_lt_post:v_Self -> v_Rhs -> bool -> Type0;
  f_lt:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_lt_pre x0 x1) (fun result -> f_lt_post x0 x1 result);
  f_le_pre:v_Self -> v_Rhs -> Type0;
  f_le_post:v_Self -> v_Rhs -> bool -> Type0;
  f_le:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_le_pre x0 x1) (fun result -> f_le_post x0 x1 result);
  f_gt_pre:v_Self -> v_Rhs -> Type0;
  f_gt_post:v_Self -> v_Rhs -> bool -> Type0;
  f_gt:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_gt_pre x0 x1) (fun result -> f_gt_post x0 x1 result);
  f_ge_pre:v_Self -> v_Rhs -> Type0;
  f_ge_post:v_Self -> v_Rhs -> bool -> Type0;
  f_ge:x0: v_Self -> x1: v_Rhs
    -> Prims.Pure bool (f_ge_pre x0 x1) (fun result -> f_ge_post x0 x1 result)
}
