module Rust_primitives.Arrays

open Rust_primitives.Integers

open LowStar.BufferOps
module B = LowStar.Buffer
module HS = FStar.HyperStack
module HST = FStar.HyperStack.ST

noeq type t_nonempty_Slice t = {
   buffer: B.buffer t;
   len:    len: usize {len == B.len buffer}
}
// Use Low* null thing
inline_for_extraction type t_Slice t = option (t_nonempty_Slice t)
inline_for_extraction type t_Array t (l:usize) = b: B.buffer t {B.length b = v l}

inline_for_extraction
let of_list (#t:Type) (l: list t {
    FStar.List.Tot.length l < maxint Lib.IntTypes.U16
  /\ FStar.List.Tot.length l > 0
  })
  : HST.StackInline 
    (t_Array t (mk_int (FStar.List.Tot.length l)))
    (requires fun _ -> True)
    (requires fun h0 b h1 -> B.alloc_post_mem_common b h0 h1 (Seq.seq_of_list l)
                        /\ B.frameOf b == HS.get_tip h0)
  = B.alloca_of_list l

// let to_list (#t:Type) (s: t_Slice t): list t = Seq.seq_to_list s

// let to_of_list_lemma t l = Seq.lemma_list_seq_bij l
// let of_to_list_lemma t l = Seq.lemma_seq_list_bij l
#set-options "--fuel 0 --ifuel 1 --z3rlimit 30"


inline_for_extraction
let length (s: t_Slice 'a)
  : usize
  = match s with
  | Some s -> s.len
  | None -> 0ul
    
unfold let spec_length (s: t_Slice 'a): GTot usize 
  = match s with
  | Some s -> B.len s.buffer
  | None -> 0ul

let arr_contains_spec (#t: eqtype) (s: t_Array t 'l) (x: t): Type0 = admit ()
let contains_spec (#t: eqtype) (s: t_Slice t) (x: t): Type0 = admit ()
let contains (#t: eqtype) (s: t_Slice t) (x: t): HST.St bool = admit ()

// let map_array #n (arr: t_Array 'a n) (f: 'a -> 'b): t_Array 'b n 
//   = FStar.Seq.map_seq_len f arr;
//     FStar.Seq.map_seq f arr 

