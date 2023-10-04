module Rust_primitives.Arrays

open Rust_primitives.Integers
open Lib.Sequence
  
unfold type slice t = s:seq t{Seq.length s <= max_usize}
type t_Array t (l: usize) = 
  s: seq t { length s == v l }

unfold type array = t_Array

class index self idx = {
  output: Type;
  in_range: self -> idx -> bool;
  (.[]): s:self -> i:idx {in_range s i} -> output;
}

class update_at self idx = {
  super_index: index self idx;
  (.[]<-): s: self -> i: idx {super_index.in_range s i} -> super_index.output -> self;
}

let repeat (value: 'a) (n: SizeT.t): FStar.Seq.seq 'a = 
  FStar.Seq.create (SizeT.v n) value

type t_Never = False

(*
let update_at
  (#t: Type) (#idx: Type)
  {| inst: update_at t idx |}
  (arr: t)
  (i: idx {inst.super_index.in_range arr i})
  (v: inst.super_index.output)
  : t
  = admit ()
  *)
  
let never_to_any #t (x: t_Never{False}): t = admit()

let array_of_list = Seq.seq_of_list


