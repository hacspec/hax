module Rust_primitives.Iterators

open Rust_primitives
open Core.Ops.Range

val foldi_range  (#n:inttype) (#acc_t:Type)
                 (#inv:(acc_t -> i:int_t n -> Type))
                 (r: t_Range (int_t n){r.f_start <=. r.f_end}) 
                 (acc:acc_t{inv acc r.f_start})
                 (f: (acc:acc_t -> i:int_t n{i >=. r.f_start /\ i <. r.f_end /\ inv acc i}
                       -> acc':acc_t{inv acc' (i +! mk_int 1)}))
                 : res:acc_t{inv res r.f_end}


val foldi_chunks_exact
                 (#t:Type) (#acc_t:Type)
                 (#inv:(acc_t -> usize -> Type))
                 (s:t_Slice t)
                 (chunk_len:usize{v chunk_len > 0 /\ Seq.length s % v chunk_len == 0})
                 (acc:acc_t{inv acc (sz 0)})
                 (f: (acc:acc_t -> it:(usize & t_Slice t){
                                  let (i,item) = it in
                                  v i >= 0 /\
                                  v i < Seq.length s / v chunk_len /\
                                  inv acc i}
                       -> acc':acc_t{inv acc' (fst it +! mk_int 1)}))
                 : res:acc_t{inv res (length s /! chunk_len)}
