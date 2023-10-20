# Core (and alloc) library

This directory contains a model for the [Core Rust
library](https://doc.rust-lang.org/core/): the minimal Rust foundation
behind the [standard libarary of
Rust](https://doc.rust-lang.org/std/index.html). This also includes a
model for some part of the [`alloc` Rust
library](https://doc.rust-lang.org/stable/alloc/).

Core is self-contained, and is dependency-free: it links to no
upstream or system libraries. Thus, even if it is minimal, it is not
small: it is around **75k LoC**, comments excluded.

In this directory, you will find the first stage of our approach to
`core` in F\*: a hand-written model. Note that this model tries to
follow as much as possible the structure and naming found in the Rust
core library.

The second stage of our approach to `core` is automatic generation
with specifications and models.
Our plan is to annotate the Rust `core` library with specifications
and models written directly as Rust annotations.
This will enable automatic generation of `core` models with consistent
semantics in all of hax backends (for now F\* and Coq).

Note that we already started experimenting with this second approach:
hax is already able to digest and generate signature-only F\* for a
huge part of core.

