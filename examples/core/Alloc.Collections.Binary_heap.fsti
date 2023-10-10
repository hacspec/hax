module Alloc.Collections.Binary_heap
open Rust_primitives

val t_BinaryHeap: Type -> eqtype

val impl_9__new: #t:Type -> t_BinaryHeap t
val impl_9__push: #t:Type -> t_BinaryHeap t -> t -> t_BinaryHeap t
val impl_10__len: #t:Type -> t_BinaryHeap t -> usize
val impl_10__iter: #t:Type -> t_BinaryHeap t -> slice t

open Core.Option

val impl_10__peek: #t:Type -> t_BinaryHeap t -> t_Option t
val impl_9__pop: #t:Type -> t_BinaryHeap t -> t_BinaryHeap t & t_Option t

unfold
let nonempty h = v (impl_10__len h) > 0

val lemma_peek_len: #t:Type -> h: t_BinaryHeap t 
  -> Lemma (Option_Some? (impl_10__peek h) <==> nonempty h)
  
val lemma_pop_len: #t:Type -> h: t_BinaryHeap t 
  -> Lemma (Option_Some? (snd (impl_9__pop h)) <==> nonempty h)

let lemma_peek_pop: #t:Type -> h: t_BinaryHeap t 
  -> Lemma (Option_Some? (impl_10__peek h) <==> Option_Some? (snd (impl_9__pop h)))
          [SMTPat (impl_10__peek h)]
  = fun h -> lemma_peek_len h; lemma_pop_len h

