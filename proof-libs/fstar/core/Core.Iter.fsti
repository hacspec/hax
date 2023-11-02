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

instance iterator_enumerate it {| i: iterator it |}: iterator (Core.Iter.Adapters.Enumerate.t_Enumerate it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    f_Item = (usize * i.f_Item);
    f_next = (fun {iter; count} -> 
      let open Core.Ops in
      let iter, opt = f_next iter in
      match opt with
      | Some value -> if v count = max_usize
                     then {iter; count                }, None
                     else {iter; count = count +. sz 1}, Some (count, value)
      | None -> {iter; count}, None
    );
    f_contains  = iterator_enumerate_contains  it i;
    f_fold      = iterator_enumerate_fold      it i;
    f_enumerate = iterator_enumerate_enumerate it;
    f_all       = iterator_enumerate_all it i;
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
val iterator_slice_all (t: eqtype): t_all (t_Slice t) t

instance iterator_slice (t: eqtype): iterator (t_Slice t) = {
  f_Item = t;
  f_next = iterator_slice_next t;
  // size_hint = (fun s -> Some (Rust_primitives.Arrays.length s));
  f_contains  = iterator_slice_contains  t;
  f_fold      = iterator_slice_fold      t;
  f_enumerate = iterator_slice_enumerate t;
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
val iterator_array_all (t: eqtype) len: t_all (t_Array t len) t

instance iterator_array (t: eqtype) len: iterator (t_Array t len) = {
  f_Item = t;
  f_next = iterator_array_next t len;
  // size_hint = (fun (_s: t_Array t len) -> Some len);
  f_contains  = iterator_array_contains  t len;
  f_fold      = iterator_array_fold      t len;
  f_enumerate = iterator_array_enumerate t len;
  f_all       = iterator_array_all t len;
}

