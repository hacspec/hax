module Core.Slice
open Rust_primitives

let impl__len (s: slice 'a)
  : len: usize {len == sz (Seq.length s)} = 
  sz (Seq.length s)

open Core.Slice.Iter

let impl__chunks (x: slice 'a) (cs: usize): t_Chunks 'a = magic ()

let impl__iter (s: slice 't): slice 't = s

let impl__chunks_exact (x: slice 'a) (cs: usize): t_ChunksExact 'a = magic ()

  
