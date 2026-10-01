module Core_models.Mem.Drop_guard
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::mem::DropGuard`]
type t_DropGuard (v_T: Type0) (v_F: Type0) = {
  f_inner:v_T;
  f_f:v_F
}

/// See [`std::mem::DropGuard::new`]
val impl__new
      (#v_T #v_F: Type0)
      {| i0: Core_models.Ops.Function.t_FnOnce v_F v_T |}
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (inner: v_T)
      (f: v_F)
    : Prims.Pure (t_DropGuard v_T v_F) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::DropGuard::dismiss`]
val impl__dismiss
      (#v_T #v_F: Type0)
      {| i0: Core_models.Ops.Function.t_FnOnce v_F v_T |}
      (#_: unit{i0.Core_models.Ops.Function.f_Output == Prims.unit})
      (guard: t_DropGuard v_T v_F)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)
