module Core_models.Mem.Manually_drop
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::mem::ManuallyDrop`]
type t_ManuallyDrop (v_T: Type0) = { f_value:v_T }

/// See [`std::mem::ManuallyDrop::new`]
val impl__new (#v_T: Type0) (value: v_T)
    : Prims.Pure (t_ManuallyDrop v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::ManuallyDrop::into_inner`]
val impl__into_inner (#v_T: Type0) (slot: t_ManuallyDrop v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::ManuallyDrop::take`]
val impl__take (#v_T: Type0) (slot: t_ManuallyDrop v_T)
    : Prims.Pure (t_ManuallyDrop v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::ManuallyDrop::drop`]
val impl_1__drop (#v_T: Type0) (slot: t_ManuallyDrop v_T)
    : Prims.Pure (t_ManuallyDrop v_T) Prims.l_True (fun _ -> Prims.l_True)
