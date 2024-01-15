module Core.Ops.Arith.Neg
open Rust_primitives

let neg #t #l (x:int_t_l t l) = zero #t #l -! x
