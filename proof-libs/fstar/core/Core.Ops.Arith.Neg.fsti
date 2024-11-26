module Core.Ops.Arith.Neg
open Rust_primitives

let neg #t x = zero #t -! x
