module Core.Slice
open Rust_primitives

let impl__len (s: slice 'a)
  : len: usize {len == sz (Seq.length s)} = 
  sz (Seq.length s)

open Core.Slice.Iter

val impl__chunks (x: slice 'a) (cs: usize): t_Chunks 'a

let impl__iter (s: slice 't): slice 't = s

val impl__chunks_exact (x: slice 'a) (cs: usize): t_ChunksExact 'a

open Core.Ops.Index

instance impl__index t: t_Index (slice t) usize
  = { f_Output = t;
      in_range = (fun (s: slice t) (i: usize) -> i <. length s);
      f_index = (fun s i -> Seq.index s (v i));
    }

