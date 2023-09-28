module Core.Slice
open Core.Types

let len_under_impl (s: slice 'a)
  : len: usize {len == SizeT.uint_to_t (Seq.length s)} = 
  SizeT.uint_to_t (Seq.length s)

open Core.Slice.Iter

let chunks_under_impl (x: slice 'a) (cs: usize): t_Chunks 'a = magic ()

let iter_under_impl (s: slice 't): slice 't = s

let chunks_exact_under_impl (x: slice 'a) (cs: usize): t_ChunksExact 'a = magic ()

