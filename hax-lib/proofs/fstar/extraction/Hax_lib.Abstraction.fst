module Hax_lib.Abstraction
open Rust_primitives

class t_Abstraction (v_Self: Type0) = {
      f_AbstractType: Type;
      f_lift: v_Self -> f_AbstractType;
}

instance int_abs t : t_Abstraction (int_t t) {
      f_AbstractType = int;
      f_lift = fun x -> v x;
}
