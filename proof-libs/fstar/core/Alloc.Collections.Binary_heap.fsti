module Alloc.Collections.Binary_heap
open Rust_primitives

val t_BinaryHeap: Type -> unit -> eqtype

val impl_10__new: #t:Type -> t_BinaryHeap t ()
val impl_10__push: #t:Type -> t_BinaryHeap t () -> t -> t_BinaryHeap t ()
val impl_11__len: #t:Type -> t_BinaryHeap t () -> usize
val impl_11__iter: #t:Type -> t_BinaryHeap t () -> t_Slice t

open Core.Option

val impl_11__peek: #t:Type -> t_BinaryHeap t () -> t_Option t
val impl_10__pop: #t:Type -> t_BinaryHeap t () -> t_BinaryHeap t () & t_Option t

unfold
let nonempty h = v (impl_11__len h) > 0

val lemma_peek_len: #t:Type -> h: t_BinaryHeap t ()
  -> Lemma (Option_Some? (impl_11__peek h) <==> nonempty h)
  
val lemma_pop_len: #t:Type -> h: t_BinaryHeap t ()
  -> Lemma (Option_Some? (snd (impl_10__pop h)) <==> nonempty h)

val lemma_peek_pop: #t:Type -> h: t_BinaryHeap t ()
  -> Lemma (impl_11__peek h == snd (impl_10__pop h))
          [SMTPat (impl_11__peek h)]
