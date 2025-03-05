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
val iterator_enumerate_rev it
  : t_rev (Core.Iter.Adapters.Enumerate.t_Enumerate it)
val iterator_enumerate_map it (i: iterator it)
  : t_map (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.f_Item)
val iterator_enumerate_flat_map it (i: iterator it)
  : t_flat_map (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.f_Item)
val iterator_enumerate_zip it
  : t_zip (Core.Iter.Adapters.Enumerate.t_Enumerate it)
val iterator_enumerate_take it
: t_take (Core.Iter.Adapters.Enumerate.t_Enumerate it)

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
    f_rev       = iterator_enumerate_rev it;
    f_map       = iterator_enumerate_map it i;
    f_flat_map  = iterator_enumerate_flat_map it i;
    f_zip       = iterator_enumerate_zip it;
    f_take      = iterator_enumerate_take it;
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
val iterator_step_by_rev it
  : t_rev (Core.Iter.Adapters.Step_by.t_StepBy it)
val iterator_step_by_zip it
  : t_zip (Core.Iter.Adapters.Step_by.t_StepBy it)
val iterator_step_by_take it
  : t_take (Core.Iter.Adapters.Step_by.t_StepBy it)
val iterator_step_by_map it (i: iterator it)
  : t_map (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item
val iterator_step_by_flat_map it (i: iterator it)
  : t_flat_map (Core.Iter.Adapters.Step_by.t_StepBy it) i.f_Item

unfold instance iterator_step_by it {| i: iterator it |}: iterator (Core.Iter.Adapters.Step_by.t_StepBy it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = i.f_Item;
    f_next      = iterator_step_by_next      it i;
    f_contains  = iterator_step_by_contains  it i;
    f_fold      = iterator_step_by_fold      it i;
    f_enumerate = iterator_step_by_enumerate it  ;
    f_step_by   = iterator_step_by_step_by   it  ;
    f_rev       = iterator_step_by_rev       it  ;
    f_all       = iterator_step_by_all       it i;
    f_zip       = iterator_step_by_zip       it  ;
    f_take      = iterator_step_by_take      it  ;
    f_map       = iterator_step_by_map       it i;
    f_flat_map  = iterator_step_by_flat_map  it i;
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
val iterator_slice_rev (t: eqtype): t_rev (t_Slice t)
val iterator_slice_all (t: eqtype): t_all (t_Slice t) t
val iterator_slice_zip (t: eqtype): t_zip (t_Slice t)
val iterator_slice_take (t: eqtype): t_take (t_Slice t)
val iterator_slice_map (t: eqtype): t_map (t_Slice t) t
val iterator_slice_flat_map (t: eqtype): t_flat_map (t_Slice t) t

instance iterator_slice (t: eqtype): iterator (t_Slice t) = {
  f_Item = t;
  f_next = iterator_slice_next t;
  // size_hint = (fun s -> Core.Option.Option_Some (Rust_primitives.Arrays.length s));
  f_contains  = iterator_slice_contains  t;
  f_fold      = iterator_slice_fold      t;
  f_enumerate = iterator_slice_enumerate t;
  f_step_by   = iterator_slice_step_by   t;
  f_rev       = iterator_slice_rev       t;
  f_all       = iterator_slice_all       t;
  f_zip       = iterator_slice_zip       t;
  f_take      = iterator_slice_take      t;
  f_map       = iterator_slice_map       t;
  f_flat_map  = iterator_slice_flat_map  t;
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
val iterator_array_rev (t: eqtype) len: t_rev (t_Array t len)
val iterator_array_all (t: eqtype) len: t_all (t_Array t len) t
val iterator_array_zip (t: eqtype) len: t_zip (t_Array t len)
val iterator_array_take (t: eqtype) len: t_take (t_Array t len)
val iterator_array_map (t: eqtype) len: t_map (t_Array t len) t
val iterator_array_flat_map (t: eqtype) len: t_flat_map (t_Array t len) t

instance iterator_array (t: eqtype) len: iterator (t_Array t len) = {
  f_Item = t;
  f_next = iterator_array_next t len;
  // size_hint = (fun (_s: t_Array t len) -> Core.Option.Option_Some len);
  f_contains  = iterator_array_contains  t len;
  f_fold      = iterator_array_fold      t len;
  f_enumerate = iterator_array_enumerate t len;
  f_step_by   = iterator_array_step_by t len;
  f_rev       = iterator_array_rev t len;
  f_all       = iterator_array_all t len;
  f_zip       = iterator_array_zip t len;
  f_take      = iterator_array_take t len;
  f_map       = iterator_array_map t len;
  f_flat_map  = iterator_array_flat_map t len;
}

(**** Zip *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_zip_contains it (i: iterator it) it2 (i2: iterator it2)
  : t_contains (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item)
val iterator_zip_fold it (i: iterator it) it2 (i2: iterator it2)
  : t_fold (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item) (iterator_zip_contains it i it2 i2)
val iterator_zip_next it (i: iterator it) it2 (i2: iterator it2)
  : t_next (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item)
val iterator_zip_enumerate it it2
  : t_enumerate (Core.Iter.Adapters.Zip.t_Zip it it2)
val iterator_zip_all it (i: iterator it) it2 (i2: iterator it2)
  : t_all (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item)
val iterator_zip_step_by it it2
  : t_step_by (Core.Iter.Adapters.Zip.t_Zip it it2)
val iterator_zip_rev it it2
  : t_rev (Core.Iter.Adapters.Zip.t_Zip it it2)
val iterator_zip_zip it it2
  : t_zip (Core.Iter.Adapters.Zip.t_Zip it it2)
val iterator_zip_take it it2
  : t_take (Core.Iter.Adapters.Zip.t_Zip it it2)
val iterator_zip_map it (i: iterator it) it2 (i2: iterator it2)
  : t_map (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item)
val iterator_zip_flat_map it (i: iterator it) it2 (i2: iterator it2)
  : t_flat_map (Core.Iter.Adapters.Zip.t_Zip it it2) (i.f_Item & i2.f_Item)

unfold instance iterator_zip it {| i: iterator it |} it2 {| i2: iterator it2 |}
: iterator (Core.Iter.Adapters.Zip.t_Zip it it2) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = i.f_Item & i2.f_Item;
    f_next      = iterator_zip_next      it i it2 i2;
    f_contains  = iterator_zip_contains  it i it2 i2;
    f_fold      = iterator_zip_fold      it i it2 i2;
    f_enumerate = iterator_zip_enumerate it it2;
    f_step_by   = iterator_zip_step_by   it it2;
    f_rev       = iterator_zip_rev       it it2;
    f_all       = iterator_zip_all       it i it2 i2;
    f_zip       = iterator_zip_zip       it it2;
    f_take      = iterator_zip_take      it it2;
    f_map       = iterator_zip_map       it i it2 i2;
    f_flat_map  = iterator_zip_flat_map  it i it2 i2;
  }

(**** Rev *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_rev_contains it (i: iterator it)
  : t_contains (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item
val iterator_rev_fold it (i: iterator it)
  : t_fold (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item (iterator_rev_contains it i)
val iterator_rev_next it (i: iterator it)
  : t_next (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item
val iterator_rev_enumerate it
  : t_enumerate (Core.Iter.Adapters.Rev.t_Rev it)
val iterator_rev_all it (i: iterator it)
  : t_all (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item
val iterator_rev_step_by it
  : t_step_by (Core.Iter.Adapters.Rev.t_Rev it)
val iterator_rev_rev it
  : t_rev (Core.Iter.Adapters.Rev.t_Rev it)
val iterator_rev_zip it
  : t_zip (Core.Iter.Adapters.Rev.t_Rev it)
val iterator_rev_take it
  : t_take (Core.Iter.Adapters.Rev.t_Rev it)
val iterator_rev_map it (i: iterator it)
  : t_map (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item
val iterator_rev_flat_map it (i: iterator it)
  : t_flat_map (Core.Iter.Adapters.Rev.t_Rev it) i.f_Item

unfold instance iterator_rev it {| i: iterator it |}: iterator (Core.Iter.Adapters.Rev.t_Rev it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = i.f_Item;
    f_next      = iterator_rev_next      it i;
    f_contains  = iterator_rev_contains  it i;
    f_fold      = iterator_rev_fold      it i;
    f_enumerate = iterator_rev_enumerate it  ;
    f_step_by   = iterator_rev_step_by   it  ;
    f_rev       = iterator_rev_rev       it  ;
    f_all       = iterator_rev_all       it i;
    f_zip       = iterator_rev_zip       it  ;
    f_take      = iterator_rev_take      it  ;
    f_map       = iterator_rev_map       it i;
    f_flat_map  = iterator_rev_flat_map  it i;
  }

(**** Map *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_map_contains it (i: iterator it) res
  : t_contains (Core.Iter.Adapters.Map.t_Map it res) res
val iterator_map_fold it (i: iterator it) res
  : t_fold (Core.Iter.Adapters.Map.t_Map it res) res (iterator_map_contains it i res)
val iterator_map_next it (i: iterator it) res
  : t_next (Core.Iter.Adapters.Map.t_Map it res) res
val iterator_map_enumerate it res
  : t_enumerate (Core.Iter.Adapters.Map.t_Map it res)
val iterator_map_all it (i: iterator it) res
  : t_all (Core.Iter.Adapters.Map.t_Map it res) res
val iterator_map_step_by it res
  : t_step_by (Core.Iter.Adapters.Map.t_Map it res)
val iterator_map_rev it res
  : t_rev (Core.Iter.Adapters.Map.t_Map it res)
val iterator_map_take it res
  : t_take (Core.Iter.Adapters.Map.t_Map it res)
val iterator_map_zip it res
  : t_zip (Core.Iter.Adapters.Map.t_Map it res)
val iterator_map_map it (i: iterator it) res
  : t_map (Core.Iter.Adapters.Map.t_Map it res) res
val iterator_map_flat_map it (i: iterator it) res
  : t_flat_map (Core.Iter.Adapters.Map.t_Map it res) res

unfold instance iterator_map it {| i: iterator it |} res
: iterator (Core.Iter.Adapters.Map.t_Map it res) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = res;
    f_next      = iterator_map_next      it i res;
    f_contains  = iterator_map_contains  it i res;
    f_fold      = iterator_map_fold      it i res;
    f_enumerate = iterator_map_enumerate it res;
    f_step_by   = iterator_map_step_by   it res;
    f_rev       = iterator_map_rev       it res;
    f_all       = iterator_map_all       it i res;
    f_zip       = iterator_map_zip       it res;
    f_take      = iterator_map_take      it res;
    f_map       = iterator_map_map       it i res;
    f_flat_map  = iterator_map_flat_map       it i res;
  }
