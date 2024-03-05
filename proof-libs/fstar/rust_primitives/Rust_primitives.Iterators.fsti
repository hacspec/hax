module Rust_primitives.Iterators

open Rust_primitives
open Core.Ops.Range
open FStar.Mul

val foldi_range  (#n:inttype) (#acc_t:Type)
                 (#inv:(acc_t -> i:int_t n -> Type))
                 (r: t_Range (int_t n){r.f_start <=. r.f_end}) 
                 (acc:acc_t{inv acc r.f_start})
                 (f: (acc:acc_t -> i:int_t n{i >=. r.f_start /\ i <. r.f_end /\ inv acc i}
                       -> acc':acc_t{inv acc' (i +! mk_int 1)}))
                 : res:acc_t{inv res r.f_end}

val foldi_range_step_by  (#n:inttype) (#acc_t:Type)
                 (#inv:(acc_t -> i:int_t n -> Type))
                 (r: t_Range (int_t n){r.f_start <=. r.f_end}) 
                 (step: usize{v step > 0 /\ range (v step) n /\ range (v r.f_end + v step) n})
                 (acc:acc_t{inv acc r.f_start})
                 (f: (acc:acc_t -> i:int_t n{i >=. r.f_start /\ i <. r.f_end /\ 
                                            (v i - v r.f_start) % (v step) == 0 /\ inv acc i}
                       -> acc':acc_t{inv acc' (i +! mk_int #n (v step))}))
                 : res:acc_t{inv res r.f_end}

/// Predicate that asserts a slice `s_chunk` is exactly the nth chunk
/// of the sequence `s`
let nth_chunk_of #t
  (s: Seq.seq t)
  (s_chunk: Seq.seq t {Seq.length s_chunk > 0})
  (chunk_nth: nat {chunk_nth < Seq.length s / Seq.length s_chunk})
  =  Seq.slice s (Seq.length s_chunk * chunk_nth) (Seq.length s_chunk * (chunk_nth + 1))
  == s_chunk

val foldi_chunks_exact
  (#t #acc_t:Type)
  (#inv: acc_t -> usize -> Type)
  (s: t_Slice t)
  (chunk_len: usize {v chunk_len > 0})
  (acc: acc_t {inv acc (sz 0)})
  (f: ( acc:acc_t
      -> it: (usize & t_Array t chunk_len) {
              let (i, s_chunk) = it in
                v i < Seq.length s / v chunk_len
              /\ nth_chunk_of s s_chunk (v i)
              /\ inv acc i
        }
      -> acc': acc_t {inv acc' (fst it +! sz 1)}
      )
  )
  : res:acc_t{inv res (length s /! chunk_len)}

val fold_chunks_exact
                 (#t:Type) (#acc_t:Type)
                 (#inv:(acc_t -> Type))
                 (s:t_Slice t)
                 (chunk_len:usize{v chunk_len > 0}) // /\ Seq.length s % v chunk_len == 0})
                 (acc:acc_t{inv acc})
                 (f: (acc:acc_t -> it:t_Array t chunk_len{inv acc}
                       -> acc':acc_t{inv acc'}))
                 : res:acc_t{inv res}


val foldi_slice  (#t:Type) (#acc_t:Type)
                 (#inv:(acc_t -> usize -> Type))
                 (sl: t_Slice t)
                 (acc:acc_t{inv acc (sz 0)})
                 (f: (acc:acc_t -> it:(usize & t){
                                  let (i,item) = it in
                                  v i >= 0 /\
                                  v i < Seq.length sl /\
                                  Seq.index sl (v i) == item /\
                                  inv acc i}
                       -> acc':acc_t{inv acc' (fst it +! sz 1)}))
                 : res:acc_t{inv res (length sl)}

