module Core_models.Ops.Deref
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::DerefPure`]. Not `unsafe`, unlike in real core.
class t_DerefPure (v_Self: Type0) = { __marker_trait_t_DerefPure:Prims.unit }

/// See [`std::ops::Receiver`]
class t_Receiver (v_Self: Type0) = { [@@@ FStar.Tactics.Typeclasses.no_method]f_Target:Type0 }

/// See [`std::ops::Deref`]
class t_Deref (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Target:Type0;
  f_deref_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_deref_post:v_Self -> f_Target -> Type0;
  f_deref:x0: v_Self -> Prims.Pure f_Target (f_deref_pre x0) (fun result -> f_deref_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) : t_Deref v_T =
  {
    f_Target = v_T;
    f_deref_pre = (fun (self: v_T) -> true);
    f_deref_post = (fun (self: v_T) (out: v_T) -> true);
    f_deref = fun (self: v_T) -> self
  }
