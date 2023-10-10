module Core.Iter.Traits.Collect

class into_iterator self = {
  f_IntoIter: Type;
  // f_Item: Type;
  f_into_iter: self -> f_IntoIter;
}

instance t_impl t {| Core.Iter.iterator t |}: into_iterator (Core.Ops.Range.Range.t_Range t) = {
  f_IntoIter = Core.Ops.Range.Range.t_Range t;
  f_into_iter = id;
}
