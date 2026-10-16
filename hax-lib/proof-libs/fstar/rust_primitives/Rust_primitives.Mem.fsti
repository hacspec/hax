module Rust_primitives.Mem

open FStar.Mul

let copy (#t: Type0) (x: t) = x

let read (#t: Type0) (x: t) : t = x