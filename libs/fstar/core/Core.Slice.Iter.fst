module Core.Slice.Iter

open Rust_primitives

let t_Chunks a = slice (slice a)
let t_ChunksExact a = slice (slice a)
let t_Iter a = slice a

