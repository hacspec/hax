module Core_models.Ops.Control_flow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::ControlFlow`]
type t_ControlFlow (v_B: Type0) (v_C: Type0) =
  | ControlFlow_Continue : v_C -> t_ControlFlow v_B v_C
  | ControlFlow_Break : v_B -> t_ControlFlow v_B v_C

/// See [`std::ops::ControlFlow::is_break`]
let impl_3__is_break (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : bool =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Break _ -> true
  | _ -> false

/// See [`std::ops::ControlFlow::is_continue`]
let impl_3__is_continue (#v_B #v_C: Type0) (self: t_ControlFlow v_B v_C) : bool =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue _ -> true
  | _ -> false

/// See [`std::ops::ControlFlow::map_break`]
let impl_3__map_break
      (#v_B #v_C #v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_B)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_ControlFlow v_B v_C)
      (f: v_F)
    : t_ControlFlow v_T v_C =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue x -> ControlFlow_Continue x <: t_ControlFlow v_T v_C
  | ControlFlow_Break x ->
    ControlFlow_Break
    (Core_models.Ops.Function.f_call_once #v_F #v_B #FStar.Tactics.Typeclasses.solve f (x <: v_B))
    <:
    t_ControlFlow v_T v_C

/// See [`std::ops::ControlFlow::map_continue`]
let impl_3__map_continue
      (#v_B #v_C #v_T #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Ops.Function.t_FnOnce v_F v_C)
      (#_: unit{i0.Core_models.Ops.Function.f_Output == v_T})
      (self: t_ControlFlow v_B v_C)
      (f: v_F)
    : t_ControlFlow v_B v_T =
  match self <: t_ControlFlow v_B v_C with
  | ControlFlow_Continue x ->
    ControlFlow_Continue
    (Core_models.Ops.Function.f_call_once #v_F #v_C #FStar.Tactics.Typeclasses.solve f (x <: v_C))
    <:
    t_ControlFlow v_B v_T
  | ControlFlow_Break x -> ControlFlow_Break x <: t_ControlFlow v_B v_T

/// See [`std::ops::ControlFlow::into_value`]
let impl_4__into_value (#v_T: Type0) (self: t_ControlFlow v_T v_T) : v_T =
  match self <: t_ControlFlow v_T v_T with
  | ControlFlow_Continue x -> x
  | ControlFlow_Break x -> x
