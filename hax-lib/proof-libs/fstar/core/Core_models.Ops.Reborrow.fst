module Core_models.Ops.Reborrow
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::Reborrow`]
class t_Reborrow (v_Self: Type0) = { __marker_trait_t_Reborrow:Prims.unit }

/// See [`std::ops::CoerceShared`]
class t_CoerceShared (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Reborrow v_Self;
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Target:Type0;
  f_Target_i0:Core_models.Marker.t_Copy f_Target
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_CoerceShared v_Self|} -> i._super_i0
