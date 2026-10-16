module Core_models.Mem.Maybe_dangling
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::mem::MaybeDangling`]
type t_MaybeDangling (v_P: Type0) = | MaybeDangling : v_P -> t_MaybeDangling v_P

/// See [`std::mem::MaybeDangling::new`]
val impl__new (#v_P: Type0) (x: v_P)
    : Prims.Pure (t_MaybeDangling v_P) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::MaybeDangling::as_ref`]
val impl__as_ref (#v_P: Type0) (self: t_MaybeDangling v_P)
    : Prims.Pure v_P Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::MaybeDangling::into_inner`]
val impl__into_inner (#v_P: Type0) (self: t_MaybeDangling v_P)
    : Prims.Pure v_P Prims.l_True (fun _ -> Prims.l_True)
