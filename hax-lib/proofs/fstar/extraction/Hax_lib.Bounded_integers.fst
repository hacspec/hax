module Hax_lib.Bounded_integers
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Bounded (v_T: Type) (v_MIN: i128) (v_MAX: i128) =
  | Bounded : v_T -> t_Bounded v_T v_MIN v_MAX

type t_Int = | Int : i128 -> t_Int

class t_ToInt (v_Self: Type) = {
  f_value_pre:v_Self -> bool;
  f_value_post:v_Self -> t_Int -> bool;
  f_value:x0: v_Self -> Prims.Pure t_Int (f_value_pre x0) (fun result -> f_value_post x0 result)
}

let impl_4__fits
      (#v_T: Type)
      (v_MIN v_MAX: u128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_ToInt v_T)
      (x: t_Int)
    : bool =
  x >=. (Int (cast (v_MIN <: u128) <: i128) <: t_Int) &&
  x <=. (Int (cast (v_MAX <: u128) <: i128) <: t_Int)

type t_UBounded (v_T: Type) (v_MIN: u128) (v_MAX: u128) =
  | UBounded : v_T -> t_UBounded v_T v_MIN v_MAX

let impl_4__new
      (#v_T: Type)
      (v_MIN v_MAX: u128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_ToInt v_T)
      (x: v_T)
    : t_UBounded v_T v_MIN v_MAX = UBounded x <: t_UBounded v_T v_MIN v_MAX

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5
      (#v_T: Type)
      (v_MIN v_MAX: u128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_ToInt v_T)
    : t_ToInt (t_UBounded v_T v_MIN v_MAX) =
  {
    f_value_pre = (fun (self: t_UBounded v_T v_MIN v_MAX) -> true);
    f_value_post = (fun (self: t_UBounded v_T v_MIN v_MAX) (out: t_Int) -> true);
    f_value = fun (self: t_UBounded v_T v_MIN v_MAX) -> f_value self._0
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Add t_Int t_Int =
  {
    f_Output = t_Int;
    f_add_pre = (fun (self: t_Int) (rhs: t_Int) -> true);
    f_add_post = (fun (self: t_Int) (rhs: t_Int) (out: t_Int) -> true);
    f_add = fun (self: t_Int) (rhs: t_Int) -> Int (self._0 +! rhs._0) <: t_Int
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Sub t_Int t_Int =
  {
    f_Output = t_Int;
    f_sub_pre = (fun (self: t_Int) (rhs: t_Int) -> true);
    f_sub_post = (fun (self: t_Int) (rhs: t_Int) (out: t_Int) -> true);
    f_sub = fun (self: t_Int) (rhs: t_Int) -> Int (self._0 -! rhs._0) <: t_Int
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Arith.t_Mul t_Int t_Int =
  {
    f_Output = t_Int;
    f_mul_pre = (fun (self: t_Int) (rhs: t_Int) -> true);
    f_mul_post = (fun (self: t_Int) (rhs: t_Int) (out: t_Int) -> true);
    f_mul = fun (self: t_Int) (rhs: t_Int) -> Int (self._0 *! rhs._0) <: t_Int
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Div t_Int t_Int =
  {
    f_Output = t_Int;
    f_div_pre = (fun (self: t_Int) (rhs: t_Int) -> true);
    f_div_post = (fun (self: t_Int) (rhs: t_Int) (out: t_Int) -> true);
    f_div = fun (self: t_Int) (rhs: t_Int) -> Int (self._0 /! rhs._0) <: t_Int
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20
      (#v_T: Type)
      (v_MIN v_MAX: u128)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core.Ops.Arith.t_Add v_T v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_ToInt v_T)
    : Core.Ops.Arith.t_Add (t_UBounded v_T v_MIN v_MAX) (t_UBounded v_T v_MIN v_MAX) =
  {
    f_Output = t_UBounded v_T v_MIN v_MAX;
    f_add_pre = (fun (self: t_UBounded v_T v_MIN v_MAX) (rhs: t_UBounded v_T v_MIN v_MAX) -> true);
    f_add_post
    =
    (fun
        (self: t_UBounded v_T v_MIN v_MAX)
        (rhs: t_UBounded v_T v_MIN v_MAX)
        (out: t_UBounded v_T v_MIN v_MAX)
        ->
        true);
    f_add
    =
    fun (self: t_UBounded v_T v_MIN v_MAX) (rhs: t_UBounded v_T v_MIN v_MAX) ->
      impl_4__new v_MIN v_MAX (self._0 +! rhs._0 <: v_T)
  }
