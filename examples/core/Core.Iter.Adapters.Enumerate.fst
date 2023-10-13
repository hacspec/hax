module Core.Iter.Adapters.Enumerate
open Rust_primitives

type t_Enumerate t = { iter: t; count: usize }

