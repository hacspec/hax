module Core.Iter.Traits.Collect

class into_iterator self = {
  f_IntoIter: Type;
  // f_Item: Type;
  f_into_iter: self -> f_IntoIter;
}

unfold instance impl t {| Core.Iter.Traits.Iterator.iterator t |}: into_iterator t = {
  f_IntoIter = t;
  f_into_iter = id;
}
