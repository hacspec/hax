# `hax-engine-names`

## Purpose of the crate
The crate `hax-engine-names` is a dummy crate that contains all the
Rust names the engine should be aware of.

For instance, the engine needs to know about `Some` and `None` to
reconstruct loops: Rust desugars `for .. in iterator {..}` loops into
loops with pattern matching on `iterator.next()`, which returns an
option.

## How to edit this crate
If you need a special treatment for a Rust name in the engine, you
should just add a piece of code that is using it.

For example, to make the name `Some` available to the engine, one
could add the following function at the end of the `src/lib.rs` file:

```rust
fn some(x: Option<()>) {
    match x {
        Some(_) => (),
        _ => (),
    }
}
```

Note this will also make `Option` available.

## How names are generated in OCaml
The subcrate `hax-engine-names-extract` runs `cargo hax into json` on
the crate `hax-engine-names`, and extracts all the names it finds,
along with other information.

Those names are compiled into the enumeration type
`Concrete_ident_generated.name`. You can look at those names by
running `hax-engine-names-extract | less`. As an example,
`core::option::Option::None` is made available as the
`Core__option__Option__None` variant.

## How to match a name in the engine
The functions `Concrete_ident.eq_name` and `Global_ident.eq_name`
allow for comparing `Concrete_ident.t` and `Global_ident.t` with
`Concrete_ident_generated.name`.

For example, the expression `Concrete_ident.eq_name
Core__option__Option__None my_concrete_ident` checks whether the
concrete ident `my_concrete_ident` is `core::option::Option::None`.

## How to build a concrete ident out of a name
See the function `Concrete_ident.of_name`.

