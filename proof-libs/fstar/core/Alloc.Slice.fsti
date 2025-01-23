module Alloc.Slice
open Rust_primitives.Arrays
open Alloc.Vec

let impl__to_vec #a (s: t_Slice a): t_Vec a Alloc.Alloc.t_Global = s

val impl__concat #t1 #t2 (s: t_Slice t1): t_Slice t2
