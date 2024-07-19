let id : 'a . 'a -> 'a = fun x -> x
type ('a, 'b) either =
  | Inl of 'a
  | Inr of 'b
