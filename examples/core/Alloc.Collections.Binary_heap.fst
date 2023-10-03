module Alloc.Collections.Binary_heap

type t_BinaryHeap (t: Type): eqtype = | BinaryHeap

let impl_9__new #t: t_BinaryHeap t = BinaryHeap

let impl_10__peek #t_Self (self: t_BinaryHeap t_Self): Core.Option.t_Option t_Self = Core.Option.Option_None

let impl_9__pop #t_Self (self: t_BinaryHeap t_Self): (t_BinaryHeap t_Self * Core.Option.t_Option t_Self) = self, Core.Option.Option_None

let impl_9__push #t (self: t_BinaryHeap t) (item: t): t_BinaryHeap t = self

let impl_10__len #t (self: t_BinaryHeap t): Core.Types.usize = magic ()

let impl_10__iter #t (self: t_BinaryHeap t): Core.Types.slice t = magic ()
