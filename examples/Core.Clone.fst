module Core.Clone

class t_Clone self = {
  clone: self -> self
}

instance clone_all (t: Type): t_Clone t = {
  clone = (fun x -> x);
}

