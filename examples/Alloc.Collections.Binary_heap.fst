module Alloc.Collections.Binary_heap

type t_BinaryHeap (t: Type): eqtype = | BinaryHeap

let new_under_impl_9 #t: t_BinaryHeap t = BinaryHeap

let peek_under_impl_10 #t_Self (self: t_BinaryHeap t_Self): Core.Option.t_Option t_Self = Core.Option.Option_None

let pop_under_impl_9 #t_Self (self: t_BinaryHeap t_Self): (t_BinaryHeap t_Self * Core.Option.t_Option t_Self) = self, Core.Option.Option_None

let push_under_impl_9 #t (self: t_BinaryHeap t) (item: t): t_BinaryHeap t = self

let len_under_impl_10 #t (self: t_BinaryHeap t): Core.Types.usize = magic ()

let iter_under_impl_10 #t (self: t_BinaryHeap t): Core.Types.slice t = magic ()
