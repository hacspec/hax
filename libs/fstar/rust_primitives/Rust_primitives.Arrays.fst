module Rust_primitives.Arrays

open Rust_primitives.Integers

type t_Slice t = s:Seq.seq t{Seq.length s <= max_usize}
type t_Array t (l:usize) = s: Seq.seq t { Seq.length s == v l }

let of_list (#t:Type) (l: list t {FStar.List.Tot.length l < maxint Lib.IntTypes.U16}): t_Slice t = Seq.seq_of_list l
let to_list (#t:Type) (s: t_Slice t): list t = Seq.seq_to_list s

let to_of_list_lemma t l = Seq.lemma_list_seq_bij l
let of_to_list_lemma t l = Seq.lemma_seq_list_bij l

let length (s: t_Slice 'a): usize = sz (Seq.length s)
let contains (#t: eqtype) (s: t_Slice t) (x: t): bool = Seq.mem x s

let map_array #n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n 
  = FStar.Seq.map_seq_len f arr;
    FStar.Seq.map_seq f arr 

