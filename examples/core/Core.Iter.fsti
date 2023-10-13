module Core.Iter

open Rust_primitives

open Core.Iter.Traits.Iterator

(*** Instances for the `iterator` trait *)

(**** Enumerate *)
(** This lives in this file for cyclic dependencies reasons. *)

val iterator_enumerate_contains it {| i: iterator it |}
  : t_contains (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.item)
val iterator_enumerate_fold it {| i: iterator it |}
  : t_fold (Core.Iter.Adapters.Enumerate.t_Enumerate it) (usize * i.item) (iterator_enumerate_contains it)
val iterator_enumerate_enumerate it
  : t_enumerate (Core.Iter.Adapters.Enumerate.t_Enumerate it)

instance iterator_enumerate it {| i: iterator it |}: iterator (Core.Iter.Adapters.Enumerate.t_Enumerate it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    item = (usize * i.item);
    next = (fun {iter; count} -> 
      let open Core.Ops in
      let iter, opt = next iter in
      match opt with
      | Some value -> if v count = max_usize
                     then {iter; count                }, None
                     else {iter; count = count +. sz 1}, Some (count, value)
      | None -> {iter; count}, None
    );
    contains  = iterator_enumerate_contains  it;
    fold      = iterator_enumerate_fold      it;
    enumerate = iterator_enumerate_enumerate it;
  }

(**** Slice *)
(** Slices are not iterable as such in Rust. We ignore this indirection here. *)
open Core.Ops.Range

val iterator_slice_next t: t_next (slice t) t
unfold
let iterator_slice_contains (t: eqtype): t_contains (slice t) t
  = fun s x -> Rust_primitives.Arrays.contains s x
val iterator_slice_fold (t: eqtype): t_fold (slice t) t (iterator_slice_contains t)
val iterator_slice_enumerate (t: eqtype): t_enumerate (slice t)

instance iterator_slice (t: eqtype): iterator (slice t) = {
  item = t;
  next = iterator_slice_next t;
  // size_hint = (fun s -> Some (Rust_primitives.Arrays.length s));
  contains  = iterator_slice_contains  t;
  fold      = iterator_slice_fold      t;
  enumerate = iterator_slice_enumerate t;
}

(**** Array *)
(** Arrays are not iterable as such in Rust. We ignore this indirection here. *)
val iterator_array_next t len: t_next (array t len) t
unfold
let iterator_array_contains (t: eqtype) len: t_contains (array t len) t
  = fun s x -> Rust_primitives.Arrays.contains s x
val iterator_array_fold (t: eqtype) len: t_fold (array t len) t (iterator_array_contains t len)
val iterator_array_enumerate (t: eqtype) len: t_enumerate (array t len)

instance iterator_array (t: eqtype) len: iterator (array t len) = {
  item = t;
  next = iterator_array_next t len;
  // size_hint = (fun (_s: array t len) -> Some len);
  contains  = iterator_array_contains  t len;
  fold      = iterator_array_fold      t len;
  enumerate = iterator_array_enumerate t len;
}

