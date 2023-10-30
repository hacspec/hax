module Core.Slice
open Rust_primitives.Arrays
open Rust_primitives.Integers

let impl__len (#t: Type) (s: t_Slice t)
  : len: usize {len == sz (Seq.length s)} = 
  sz (Seq.length s)

open Core.Slice.Iter

val impl__chunks (x: t_Slice 'a) (cs: usize): t_Chunks 'a

let impl__iter (s: t_Slice 't): t_Slice 't = s

val impl__chunks_exact (x: t_Slice 'a) (cs: usize): t_Slice (s: t_Slice 'a {length s == cs})

open Core.Ops.Index

instance impl__index t n: t_Index (t_Slice t) (int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < v (length s));
      f_index = (fun s i -> Seq.index s (v i));
    }

let impl__copy_from_slice #t (x:t -> t_Slice t) (y:t_Slice t) : t_Slice t = y
