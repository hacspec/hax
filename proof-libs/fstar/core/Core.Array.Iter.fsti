module Core.Array.Iter
open Rust_primitives

let into_iter = Core.Iter.iterator_array
let t_IntoIter t l = t_Array t l
