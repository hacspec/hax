module Core.Ops
open Rust_primitives

// class add_tc self rhs = {
//   output: Type;
//   in_bounds: self -> rhs -> Type0;
//   ( +! ): x:self -> y:rhs {in_bounds x y} -> output;
// }

class negation_tc self = {
  ( ~. ): self -> self;
}

instance negation_for_integers #t: negation_tc (int_t t) = {
  ( ~. ) = fun x -> lognot x
}

instance negation_for_bool: negation_tc bool = {
  ( ~. ) = not
}

open Core.Ops.Index

let ( .[] ) (#self:Type0) (#idx:Type0) {| inst: t_Index self idx |}
  : s:self -> i:idx{in_range s i} -> inst.f_Output
  = f_index

