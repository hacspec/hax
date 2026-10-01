module Core_models.Ops.Unsize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::ops::CoerceUnsized`]
class t_CoerceUnsized (v_Self: Type0) (v_T: Type0) = { __marker_trait_t_CoerceUnsized:Prims.unit }

/// See [`std::ops::DispatchFromDyn`]
class t_DispatchFromDyn (v_Self: Type0) (v_T: Type0) = {
  __marker_trait_t_DispatchFromDyn:Prims.unit
}
