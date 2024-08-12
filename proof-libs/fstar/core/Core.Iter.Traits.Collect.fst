module Core.Iter.Traits.Collect

class into_iterator (v_Self: Type0) = {
  // f_Item:Type0;
  f_IntoIter:Type0;
  f_IntoIter_Iterator:Core.Iter.Traits.Iterator.t_Iterator f_IntoIter;
  f_into_iter_pre:v_Self -> bool;
  f_into_iter_post:v_Self -> f_IntoIter -> bool;
  f_into_iter:x0: v_Self
    -> Prims.Pure f_IntoIter (f_into_iter_pre x0) (fun result -> f_into_iter_post x0 result)
}

let t_IntoIterator = into_iterator

unfold instance impl t {| iterator_t: Core.Iter.Traits.Iterator.iterator t |} {| Core.Iter.Traits.Iterator.iterator t |}: into_iterator t = {
  f_IntoIter = t;
  f_into_iter = id;
  f_IntoIter_Iterator = iterator_t;
  f_into_iter_pre = (fun (self: t) -> true);
  f_into_iter_post = (fun (self: t) (out: t) -> true)
}
