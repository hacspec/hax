module Alloc.Collections.Btree.Set
open Rust_primitives

val t_BTreeSet (t:Type0) (u:unit): eqtype

val t_Iter (t:Type0): eqtype

val impl_13__new #t (): t_BTreeSet t ()

val impl_14__len #t (x:t_BTreeSet t ()) : usize

val impl_14__insert #t #u (x:t_BTreeSet t u) (y:t) : t_BTreeSet t u
