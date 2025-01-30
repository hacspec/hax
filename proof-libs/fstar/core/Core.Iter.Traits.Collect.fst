module Core.Iter.Traits.Collect

class t_IntoIterator self = {
  f_IntoIter: Type0;
  // f_Item: Type0;
  f_into_iter: self -> f_IntoIter;
}

unfold instance impl t {| Core.Iter.Traits.Iterator.iterator t |}: t_IntoIterator t = {
  f_IntoIter = t;
  f_into_iter = id;
}
