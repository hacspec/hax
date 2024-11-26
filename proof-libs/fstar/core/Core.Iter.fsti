module Core.Iter

open Rust_primitives

open Core.Iter.Traits.Iterator

(*** Instances for the `iterator` trait *)

(**** Enumerate *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_enumerate_contains it (i: iterator it)
  : t_contains (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.f_Item)
val iterator_enumerate_fold it (i: iterator it)
  : t_fold (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.f_Item) (iterator_enumerate_contains it i)
val iterator_enumerate_enumerate it
  : t_enumerate (Core.Iter.Adapters.Enumerate.t_Enumerate it)
val iterator_enumerate_all it (i: iterator it)
  : t_all (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.f_Item)
val iterator_enumerate_step_by it
  : t_step_by (Core.Iter.Adapters.Enumerate.t_Enumerate it)

instance iterator_enumerate it {| i: iterator it |}: iterator (Core.Iter.Adapters.Enumerate.t_Enumerate it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = (usize * i.f_Item);
    f_next = (fun {iter; count} -> 
      let open Core.Ops in
      let iter, opt = f_next iter in
      match opt with
      | Core.Option.Option_Some value -> if v count = max_usize
                     then {iter; count                }, Core.Option.Option_None
                     else {iter; count = count +. sz 1}, Core.Option.Option_Some (count, value)
      | Core.Option.Option_None -> {iter; count}, Core.Option.Option_None
    );
    f_contains  = iterator_enumerate_contains  it i;
    f_fold      = iterator_enumerate_fold      it i;
    f_enumerate = iterator_enumerate_enumerate it;
    f_step_by   = iterator_enumerate_step_by it;
    f_all       = iterator_enumerate_all it i;
  }

(**** Step_by *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_step_by_contains it (i: iterator it)
  : t_contains (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item
val iterator_step_by_fold it (i: iterator it)
  : t_fold (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item (iterator_step_by_contains it i)
val iterator_step_by_next it (i: iterator it)
  : t_next (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item
val iterator_step_by_enumerate it
  : t_enumerate (Core.Iter.Adapters.Step_by.t_StepBy it)
val iterator_step_by_all it (i: iterator it)
  : t_all (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item
val iterator_step_by_step_by it
  : t_step_by (Core.Iter.Adapters.Step_by.t_StepBy it)

unfold instance iterator_step_by it {| i: iterator it |}: iterator (Core.Iter.Adapters.Step_by.t_StepBy it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = i.f_Item;
    f_next      = iterator_step_by_next      it i;
    f_contains  = iterator_step_by_contains  it i;
    f_fold      = iterator_step_by_fold      it i;
    f_enumerate = iterator_step_by_enumerate it  ;
    f_step_by   = iterator_step_by_step_by   it  ;
    f_all       = iterator_step_by_all       it i;
  }

(**** Slice *)
(** Slices are not iterable as such in Rust. We ignore this indirection here. *)
open Core.Ops.Range

val iterator_slice_next t: t_next (t_Slice t) t
unfold
let iterator_slice_contains (t: eqtype): t_contains (t_Slice t) t
  = fun s x -> Rust_primitives.Arrays.contains s x
val iterator_slice_fold (t: eqtype): t_fold (t_Slice t) t (iterator_slice_contains t)
val iterator_slice_enumerate (t: eqtype): t_enumerate (t_Slice t)
val iterator_slice_step_by (t: eqtype): t_step_by (t_Slice t)
val iterator_slice_all (t: eqtype): t_all (t_Slice t) t

instance iterator_slice (t: eqtype): iterator (t_Slice t) = {
  f_Item = t;
  f_next = iterator_slice_next t;
  // size_hint = (fun s -> Core.Option.Option_Some (Rust_primitives.Arrays.length s));
  f_contains  = iterator_slice_contains  t;
  f_fold      = iterator_slice_fold      t;
  f_enumerate = iterator_slice_enumerate t;
  f_step_by   = iterator_slice_step_by   t;
  f_all       = iterator_slice_all       t;
}

(**** Array *)
(** Arrays are not iterable as such in Rust. We ignore this indirection here. *)
val iterator_array_next t len: t_next (t_Array t len) t
unfold
let iterator_array_contains (t: eqtype) len: t_contains (t_Array t len) t
  = fun s x -> Rust_primitives.Arrays.contains s x
val iterator_array_fold (t: eqtype) len: t_fold (t_Array t len) t (iterator_array_contains t len)
val iterator_array_enumerate (t: eqtype) len: t_enumerate (t_Array t len)
val iterator_array_step_by (t: eqtype) len: t_step_by (t_Array t len)
val iterator_array_all (t: eqtype) len: t_all (t_Array t len) t

instance iterator_array (t: eqtype) len: iterator (t_Array t len) = {
  f_Item = t;
  f_next = iterator_array_next t len;
  // size_hint = (fun (_s: t_Array t len) -> Core.Option.Option_Some len);
  f_contains  = iterator_array_contains  t len;
  f_fold      = iterator_array_fold      t len;
  f_enumerate = iterator_array_enumerate t len;
  f_step_by   = iterator_array_step_by t len;
  f_all       = iterator_array_all t len;
}

