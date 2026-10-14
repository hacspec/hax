module
public import CoreModels.RustPrimitives.Types
public import CoreModels.RustPrimitives.Funs

@[expose] public section

/-!

# Rust Primitives

This module contains Lean definitions for the `rust_primitives` crate. These primitives
are the basis on top of which the `core` and `alloc` models are defined. In contrast to
`core` and `alloc`, these Lean definitions are manually crafted and not generated from
Rust code.

-/
