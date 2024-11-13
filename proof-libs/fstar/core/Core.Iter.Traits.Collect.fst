module Core.Iter.Traits.Collect

class into_iterator self = {
  f_IntoIter: Type0;
  // f_Item: Type0;
  f_into_iter: self -> f_IntoIter;
}

let t_IntoIterator = into_iterator

unfold instance impl t {| Core.Iter.Traits.Iterator.iterator t |}: into_iterator t = {
  f_IntoIter = t;
  f_into_iter = id;
}
