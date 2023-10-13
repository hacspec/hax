module Rust_primitives.Arrays

open Rust_primitives.Integers

unfold type t_Slice t = s:Seq.seq t{Seq.length s <= max_usize}
unfold type t_Array t (l:usize) = s: Seq.seq t { Seq.length s == v l }
unfold type slice = t_Slice
unfold type array = t_Array

let of_list (#t:Type) l = Seq.seq_of_list l
let to_list (#t:Type) s = Seq.seq_to_list s

let to_of_list_lemma t l = Seq.lemma_list_seq_bij l
let of_to_list_lemma t l = Seq.lemma_seq_list_bij l

let length (arr: slice 'a): usize = sz (Seq.length arr)
let contains (#t: eqtype) (arr: slice t) (x: t): bool = Seq.mem x arr

let map_array #n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n 
  = FStar.Seq.map_seq_len f arr;
    FStar.Seq.map_seq f arr 

