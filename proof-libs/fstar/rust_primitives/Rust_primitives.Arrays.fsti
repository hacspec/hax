module Rust_primitives.Arrays

open Rust_primitives.Integers

type t_Slice t = s:Seq.seq t{Seq.length s <= max_usize}
type t_Array t (l:usize) = s: Seq.seq t { Seq.length s == v l }
let length (s: t_Slice 'a): usize = sz (Seq.length s)
let contains (#t: eqtype) (s: t_Slice t) (x: t): bool = Seq.mem x s


val of_list (#t:Type) (l: list t {FStar.List.Tot.length l < maxint Lib.IntTypes.U16}):
    t_Array t (sz (FStar.List.Tot.length l))
val to_list (#t:Type) (s: t_Slice t): list t

val map_array #n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n 
