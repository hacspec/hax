module Core_models.Mem
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::mem::forget`]
val forget (#v_T: Type0) (t: v_T) : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::forget_unsized`]
val forget_unsized (#v_T: Type0) (t: v_T)
    : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::size_of`]
val size_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::size_of_val`]
val size_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::min_align_of`]
val min_align_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::min_align_of_val`]
val min_align_of_val (#v_T: Type0) (v_val: v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::align_of`]
val align_of: #v_T: Type0 -> Prims.unit -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::align_of_val`]
val align_of_val (#v_T: Type0) (v_val: v_T) : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::align_of_val_raw`]
val align_of_val_raw (#v_T: Type0) (v_val: v_T)
    : Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::needs_drop`]
val needs_drop: #v_T: Type0 -> Prims.unit -> Prims.Pure bool Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::uninitialized`]
val uninitialized: #v_T: Type0 -> Prims.unit
  -> Prims.Pure v_T (requires false) (fun _ -> Prims.l_True)

/// See [`std::mem::swap`]
val swap (#v_T: Type0) (x y: v_T) : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::replace`]
val replace (#v_T: Type0) (dest src: v_T)
    : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::drop`]
val drop (#v_T: Type0) (e_x: v_T) : Prims.Pure Prims.unit Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::take`]
val take (#v_T: Type0) (x: v_T) : Prims.Pure (v_T & v_T) Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::transmute_copy`]
val transmute_copy (#v_Src #v_Dst: Type0) (src: v_Src)
    : Prims.Pure v_Dst (requires false) (fun _ -> Prims.l_True)

/// See [`std::mem::variant_count`]
val variant_count: #v_T: Type0 -> Prims.unit
  -> Prims.Pure usize Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::zeroed`]
val zeroed: #v_T: Type0 -> Prims.unit -> Prims.Pure v_T (requires false) (fun _ -> Prims.l_True)

/// See [`std::mem::transmute`]
val transmute (#v_Src #v_Dst: Type0) (src: v_Src)
    : Prims.Pure v_Dst (requires false) (fun _ -> Prims.l_True)

/// See [`std::mem::copy`]
val copy (#v_T: Type0) {| i0: Core_models.Marker.t_Copy v_T |} (x: v_T)
    : Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)

/// See [`std::mem::conjure_zst`]
val conjure_zst: #v_T: Type0 -> Prims.unit -> Prims.Pure v_T Prims.l_True (fun _ -> Prims.l_True)
