module Core.Option

type t_Option t = | Option_Some of t | Option_None

let and_then_under_impl (self: t_Option 'self) (f: 'self -> t_Option 't): t_Option 't = 
  match self with
  | Option_Some x -> f x
  | Option_None -> Option_None

let unwrap_under_impl #t (_: t_Option t): t = magic ()

