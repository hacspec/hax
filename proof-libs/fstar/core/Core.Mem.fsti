module Core.Mem
open Rust_primitives

// TODO: remove default type
val size_of (#[FStar.Tactics.exact (`eqtype_as_type unit)]t:Type): unit -> usize
