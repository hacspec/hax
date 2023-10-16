module Core.Slice.Iter

open Rust_primitives

let t_Chunks a = t_Slice (t_Slice a)
let t_ChunksExact a = t_Slice (t_Slice a)
let t_Iter a = t_Slice a

