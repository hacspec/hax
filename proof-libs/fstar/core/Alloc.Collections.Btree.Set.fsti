module Alloc.Collections.Btree.Set
open Rust_primitives

val t_BTreeSet (t:Type0) (u:unit): eqtype

val t_Iter (t:Type0): eqtype

val impl_13__new #t (): t_BTreeSet t ()

val impl_14__len #t #u (x:t_BTreeSet t u) : usize

val impl_14__insert #t #u (x:t_BTreeSet t u) (y:t) : (t_BTreeSet t u & bool)

val btree_iter_iter (t: Type0): Core.Iter.Traits.Iterator.iterator (t_Iter t)

val impl_14__iter #t #u (x:t_BTreeSet t u): t_Iter t

unfold instance impl t : Core.Iter.Traits.Iterator.iterator (t_Iter t) = {
  f_Item = t;
  f_next = (btree_iter_iter t).f_next;
  f_contains = (btree_iter_iter t).f_contains;
  f_fold = (btree_iter_iter t).f_fold;
  f_enumerate = (btree_iter_iter t).f_enumerate;
  f_step_by = (btree_iter_iter t).f_step_by;
  f_all = (btree_iter_iter t).f_all;
}
