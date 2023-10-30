module Core.Ops.Arith
open Rust_primitives


class t_Add self rhs = {
   add_output: Type;
   add_in_bounds: self -> rhs -> Type0;
   ( +! ): x:self -> y:rhs {add_in_bounds x y} -> add_output;
}

class t_Sub self rhs = {
   sub_output: Type;
   sub_in_bounds: self -> rhs -> Type0;
   ( -! ): x:self -> y:rhs {sub_in_bounds x y} -> sub_output;
}

