module Rust_primitives.Hax

open Rust_primitives.Integers
open Rust_primitives.Arrays

type t_Never = False
let never_to_any #t: t_Never -> t = (fun _ -> match () with)

let repeat (x: 'a) (len: usize): t_Array 'a len = 
  FStar.Seq.create (v len) x

open Core.Ops.Index
class update_at_tc self idx = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  super_index: t_Index self idx;
  update_at: s: self -> i: idx {in_range s i} -> super_index.f_Output -> self;
}

open Core.Slice

instance update_at_tc_array t l n: update_at_tc (t_Array t l) (int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Array t l) (int_t n);
  update_at = (fun arr i x -> FStar.Seq.upd arr (v i) x);
}

let (.[]<-) #self #idx {| update_at_tc self idx |} (s: self) (i: idx {in_range s i})
  = update_at s i

let array_of_list #t = Rust_primitives.Arrays.of_list #t

// class index self idx = {
//   [@@@FStar.Tactics.Typeclasses.no_method]
//   output: Type;
//   in_range: self -> idx -> bool;
//   (.[]): s:self -> i:idx {in_range s i} -> output;
// }

// class update_at_tc self idx = {
//   [@@@FStar.Tactics.Typeclasses.tcinstance]
//   super_index: index self idx;
//   (.[]<-): s: self -> i: idx {in_range s i} -> super_index.output -> self;
// }
// let update_at #self #idx {| update_at_tc self idx |} (s: self) (i: idx {in_range s i})
//   = (.[]<-) s i

// instance index_array t l n : index (array t l) (int_t n) = {
//   output = t;
//   in_range = (fun (_:array t l) (idx: int_t n) -> v idx >= 0 && v idx < v l);
//   (.[]) = (fun (x:array t l) idx -> Seq.index x (v idx));
// }


