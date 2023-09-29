module Rust_primitives.Hax

let x = 0ul

let repeat (value: 'a) (n: SizeT.t): FStar.Seq.seq 'a = 
  FStar.Seq.create (SizeT.v n) value

type t_Never =

open Core.Types

let update_at
  (#t: Type) (#idx: Type)
  {| inst: update_at t idx |}
  (arr: t)
  (i: idx {inst.super_index.in_range arr i})
  (v: inst.super_index.output)
  : t
  = admit ()
  
let never_to_any #t (x: t_Never): t = (match x with)

let array_of_list = Seq.seq_of_list

