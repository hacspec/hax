module Alloc.Slice
open Rust_primitives.Arrays
open Alloc.Vec

let impl__to_vec #a (s: t_Slice a): t_Vec a Alloc.Alloc.t_Global = s
