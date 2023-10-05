module Rust_primitives.Arrays

open Rust_primitives.Integers
  
unfold type slice t = s:Seq.seq t{Seq.length s <= max_usize}
unfold type array t (l:usize) = s: Seq.seq t { Seq.length s == v l }

type t_Array = array


class index self idx = {
  output: Type;
//  in_range: self -> idx -> bool;
  (.[]): s:self -> i:idx -> output;
}

class update_at self idx = {
  super_index: index self idx;
  (.[]<-): s: self -> i: idx -> super_index.output -> self;
}

type ranged_usize (l:usize) = x:usize{v x < v l}

instance index_array t l : index (array t l) (s:ranged_usize l) = {
  output = t;
  (.[]) = (fun (x:array t l) (idx:ranged_usize l) -> Seq.index x (v idx));
}

let repeat (value: 'a) (n: usize): FStar.Seq.seq 'a = 
  FStar.Seq.create (v n) value

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
  
let array_of_list = Seq.seq_of_list

