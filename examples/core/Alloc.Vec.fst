module Alloc.Vec
open Core.Types

unfold type t_Vec t _ = slice t

let impl__new #t: t_Vec t () = FStar.Seq.empty

let impl_2__extend_from_slice #t (self: t_Vec t ()) (other: slice t {SizeT.fits (Seq.length self + Seq.length other)}): t_Vec t ()
  = FStar.Seq.append self other

let impl__with_capacity (_capacity: usize) = impl__new

let impl_1__push
  (v: t_Vec 't () {SizeT.fits (FStar.Seq.length v + 1)})
  (x: 't)
  : t_Vec 't () = 
    FStar.Seq.append v (FStar.Seq.create 1 x)

let impl_1__len (v: t_Vec 't unit) = SizeT.uint_to_t (Seq.length v)

let from_elem (item: 'a) (len: usize) = Seq.create (SizeT.v len) item

