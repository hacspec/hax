module Core.Ops.Arith.Neg
open Rust_primitives

inline_for_extraction
let neg #t x = zero #t -! x
