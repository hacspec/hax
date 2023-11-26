module Rust_primitives.Hax

open Rust_primitives.Integers
open Rust_primitives.Arrays

type t_Never = False
inline_for_extraction
let never_to_any #t: t_Never -> t = (fun _ -> match () with)

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
let repeat (x: 'a) (len: usize {v len > 0}): HST.StackInline (t_Array 'a len) (fun _ -> True) (fun _ _ _ -> True) = 
  B.alloca x len

open Core.Ops.Index

inline_for_extraction
class update_at_tc self idx = {
  [@@@FStar.Tactics.Typeclasses.tcinstance]
  super_index: t_Index self idx;
  update_at: s: self -> i: idx {in_range s i} -> super_index.f_Output -> HST.St unit;
}

open Core.Slice

inline_for_extraction
instance impl__index t l n: t_Index (t_Array t l) (int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Array t l) (i: int_t n) -> v i >= 0 && v i < v l);
      f_index = (fun s i -> admit (); s.(i));
    }

inline_for_extraction
instance update_at_tc_array t l n: update_at_tc (t_Array t l) (int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Array t l) (int_t n);
  update_at = (fun arr i x -> 
            admit ();
            arr.(i) <- x
    );
}

inline_for_extraction
instance update_at_tc_slice t n: update_at_tc (t_Slice t) (int_t n) = {
  super_index = FStar.Tactics.Typeclasses.solve <: t_Index (t_Slice t) (int_t n);
  update_at = (fun arr i x -> 
            admit ()
            // arr.(i) <- x
    );
}

inline_for_extraction
let (.[]<-) #self #idx {| update_at_tc self idx |} (s: self) (i: idx {in_range s i})
  = update_at s i

inline_for_extraction
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



