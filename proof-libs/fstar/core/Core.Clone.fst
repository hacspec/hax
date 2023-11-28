module Core.Clone

class t_Clone self = {
  f_clone: x:self -> r:self {x == r}
}

(** Everything is clonable *)
inline_for_extraction
instance clone_all (t: Type): t_Clone t = {
  f_clone = (fun x -> x);
}

