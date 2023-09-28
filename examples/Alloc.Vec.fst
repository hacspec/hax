module Alloc.Vec
open Core.Types

unfold type t_Vec t _ = slice t

let new_under_impl #t: t_Vec t () = FStar.Seq.empty

let extend_from_slice_under_impl_2 #t (self: t_Vec t ()) (other: slice t {SizeT.fits (Seq.length self + Seq.length other)}): t_Vec t ()
  = FStar.Seq.append self other

let with_capacity_under_impl (_capacity: usize) = new_under_impl

let push_under_impl_1
  (v: t_Vec 't () {SizeT.fits (FStar.Seq.length v + 1)})
  (x: 't)
  : t_Vec 't () = 
    FStar.Seq.append v (FStar.Seq.create 1 x)

let len_under_impl_1 (v: t_Vec 't unit) = SizeT.uint_to_t (Seq.length v)

let from_elem (item: 'a) (len: usize) = Seq.create (SizeT.v len) item

