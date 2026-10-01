module Rust_primitives.Sequence

open Rust_primitives.Integers

type t_Seq t = Rust_primitives.Arrays.t_Slice t

let seq_empty #t () : t_Seq t = FStar.Seq.empty

let seq_from_slice #t (s: Rust_primitives.Arrays.t_Slice t) : t_Seq t = s 

let seq_from_boxed_slice #t (s: Rust_primitives.Arrays.t_Slice t) : t_Seq t = s 

let seq_from_array #t n (s: Rust_primitives.Arrays.t_Array t n) : t_Seq t = s 

let seq_to_slice #t (s: t_Seq t) : Rust_primitives.Arrays.t_Slice t = s 

let seq_concat #t (s1: t_Seq t) (s2: t_Seq t {(Seq.length s1) + (Seq.length s2) <= max_usize}): t_Seq t & t_Seq t = Seq.append s1 s2, FStar.Seq.empty

let seq_extend #t (s1: t_Seq t) (s2: t_Seq t {(Seq.length s1) + (Seq.length s2) <= max_usize}): t_Seq t = Seq.append s1 s2

let seq_push #t (s: t_Seq t {Seq.length s < max_usize}) (x: t): t_Seq t = Seq.append s (Seq.create 1 x)
let seq_one #t (x: t): t_Seq t = Seq.create 1 x

let seq_create #t (x: t) (n: usize): t_Seq t = Seq.create (v n) x

let seq_len #t (s: t_Seq t): usize = mk_usize (Seq.length s)

let seq_drain #t (s: t_Seq t) (b: usize) (e: usize{e >=. b && e <=. seq_len s}): t_Seq t & t_Seq t = 
  Seq.append (Seq.slice s 0 (v b)) (Seq.slice s (v e) (Seq.length s)), Seq.slice s (v b) (v e)

let seq_remove #t (s: t_Seq t) (i: usize{v i >= 0 && i <. seq_len s}): t_Seq t & t = 
  Seq.append (Seq.slice s 0 (v i)) (Seq.slice s (1 + v i) (Seq.length s)), Rust_primitives.Slice.slice_index s i 

let seq_index #t (s: t_Seq t) (i: usize{i <. seq_len s}): t = Rust_primitives.Slice.slice_index s i 
