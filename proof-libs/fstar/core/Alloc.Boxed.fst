module Alloc.Boxed

type t_Box t t_Global = t

assume val impl__pin #t (x: t) : Core.Pin.t_Pin (t_Box t Alloc.Alloc.t_Global)
