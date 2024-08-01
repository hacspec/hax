module Alloc.Vec
open Rust_primitives

unfold type t_Vec t (_: unit) = s:t_Slice t

let impl__new #t (): t_Vec t () = FStar.Seq.empty

let impl_2__extend_from_slice #t (#[(Tactics.exact (`()))]alloc:unit) (self: t_Vec t alloc) (other: t_Slice t{Seq.length self + Seq.length other <= max_usize}): t_Vec t alloc
  = FStar.Seq.append self other

let impl__with_capacity (_capacity: usize) = impl__new ()

// TODO: missing precondition For now, `impl_1__push` has a wrong
// semantics: pushing on a "full" vector does nothing. It should panic
// instead.
let impl_1__push #t
  (#[(Tactics.exact (`()))]alloc:unit)
  (v: t_Vec t alloc)// Removed: {Seq.length v + 1 <= max_usize})
  (x: t)
   : t_Vec t alloc = 
     if Seq.length v <= max_usize then v else
     FStar.Seq.append v (FStar.Seq.create 1 x)

let impl_1__len #t (#[(Tactics.exact (`()))]alloc:unit) (v: t_Vec t alloc) =
  let n = Seq.length v in
  assert (n <= maxint usize_inttype);
  mk_int #usize_inttype (Seq.length v)

let from_elem #a (item: a) (len: usize) = Seq.create (v len) item

open Rust_primitives.Hax
open Core.Ops.Index
instance update_at_tc_array t n: update_at_tc (t_Vec t ()) (int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Vec t ()) (int_t n);
  update_at = (fun arr i x -> FStar.Seq.upd arr (v i) x);
}

let impl_1__is_empty #t (#[(Tactics.exact (`()))]alloc:unit) (v: t_Vec t alloc) =
  Seq.length v == 0