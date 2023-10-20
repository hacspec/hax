module Core.Slice.Iter

open Rust_primitives

unfold let t_Chunks a = t_Slice (t_Slice a)
unfold let t_ChunksExact a = t_Slice (t_Slice a)
unfold let t_Iter a = t_Slice a

