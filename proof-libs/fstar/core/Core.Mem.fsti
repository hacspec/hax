module Core.Mem
open Rust_primitives

// FIXME(unsafe!): remove default type (see #545)
val size_of (#[FStar.Tactics.exact (`eqtype_as_type unit)]t:Type): unit -> usize
