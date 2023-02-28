open Base

let todo () = failwith "unimplemented!"
let ( << ) f g x = f (g x)
let ( >> ) f g x = g (f x)
let ( &&& ) (f : 'a -> 'b) (g : 'a -> 'c) (x : 'a) : 'b * 'c = (f x, g x)

let ( *** ) (f : 'a -> 'b) (g : 'c -> 'd) ((l, r) : 'a * 'c) : 'b * 'd =
  (f l, g r)

let map_fst f = f *** Fn.id
let map_snd g = Fn.id *** g
let fst3 (x, _, _) = x
let snd3 (_, y, _) = y
let thd3 (_, _, z) = z

let curry f x y = f (x, y)
let uncurry f (x, y) = f x y
