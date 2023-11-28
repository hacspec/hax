module Core.Slice
open Rust_primitives.Arrays
open Rust_primitives.Integers

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

inline_for_extraction
let impl__len (#t: Type) (s: t_Slice t)
  : HST.St usize
      // (requires (fun h -> B.live h s.len))
      // (ensures  (fun h y h' -> h == h' /\ y == Seq.index (B.as_seq h s.len) 0)) 
  = admit (); length s

open Core.Slice.Iter

inline_for_extraction
val impl__chunks (x: t_Slice 'a) (cs: usize): t_Chunks 'a

inline_for_extraction
let impl__iter (s: t_Slice 't): t_Slice 't = s

inline_for_extraction
val impl__chunks_exact (x: t_Slice 'a) (cs: usize): t_Slice (s: t_Slice 'a {spec_length s == cs})

open Core.Ops.Index

inline_for_extraction
instance impl__index t n: t_Index (t_Slice t) (int_t n)
  = { f_Output = t;
      in_range = (fun (s: t_Slice t) (i: int_t n) -> v i >= 0 && v i < v (spec_length s));
      f_index = (fun s i -> 
        admit ();
        s.buffer.(i)
      );
    }

inline_for_extraction
let impl__copy_from_slice #t (x: t_Slice t) (y:t_Slice t) : HST.St unit
    = LowStar.BufferOps.blit x.buffer 0ul y.buffer 0ul y.len

inline_for_extraction
let impl__split_at #t (s: t_Slice t) (mid: usize): HST.St (t_Slice t * t_Slice t) =
  let b1 = B.sub s.buffer 0ul mid in
  let l2 = s.len -. mid in
  let b2 = B.sub s.buffer mid l2 in
  let s1 = {buffer = b1; len = mid} in
  let s2 = {buffer = b2; len = l2} in
  (s1,s2)
