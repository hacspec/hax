module Hax_lib.Abstraction
open Rust_primitives

class t_Abstraction (v_Self: Type0) = {
      f_AbstractType: Type;
      f_lift: v_Self -> f_AbstractType;
}

