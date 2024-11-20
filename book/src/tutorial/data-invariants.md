# Data invariants

In the two previous chapters we saw how to write specifications on
functions, be it with pre and post-condition or with lemmas. In this
chapter, we will see how to maintain invariants with precise types.

## Making illegal states unpresentable
With the Barrett example, we were working on a certain field, whose
elements were represented as `i32` integers. To simplify, let's
consider `F₃`, the finite field with 3 elements (say `0`, `1` and
`2`). Every element of `F3` can be represented as a `i32` integers,
but the converse doesn't hold: the vast majority of `i32` integers are
not in of `F₃`.

Representing `F₃` as `i32`s, every time we define a function consuming
`F₃` elements, we face the risk to consume *illegal* elements. We are
thus back to [chapter 4.1](panic-freedom.md): we should panic on
illegal elements, and add hax pre-conditions on every single
function. That's not ideal: the property of being either `0`, `1` or
`2` should be encoded directly on the type representing `F₃` elements.

### `enum`s to then rescue
Rust alone already can solve our representation issues with
[enums](https://doc.rust-lang.org/book/ch06-00-enums.html)! Below, we
define the `enum` type `F3` which has only three constructor: `F3`
represent exactly the elements of `F₃`, not more, not less.

```rust,editable
enum F3 {
    E1,
    E2,
    E3,
}
```

With `F3`, there doesn't exist illegal values at all: we can now
define [*total*
functions](https://en.wikipedia.org/wiki/Partial_function) on `F₃`
elements. We dropped altogether a source of panic!

Soon you want to work with a bigger finite field: say
`F₂₃₄₇`. Representing this many `q` different elements with an Rust
enum would be very painful... The `enum` approach falls apart.

### Newtype and refinements
Since we don't want an `enum` with 2347 elements, we have to revert to
a type that can hold this many elements. The smallest integer type
large enough provided by Rust is `u16`.

Let's define `F` a
["newtype"](https://matklad.github.io/2018/06/04/newtype-index-pattern.html):
a [struct](https://doc.rust-lang.org/book/ch05-00-structs.html) with
one `u16` field `v`. Notice the refinment annotation on `v`: the
extraction of this type `F` via hax will result in a type enforcing
`v` small enough.

```rust,editable
pub const Q: u16 = 2347;

#[hax_lib::attributes]
pub struct F {
    #[hax_lib::refine(v < Q)]
    pub v: u16,
}
```

In Rust, we can now define functions that operates on type `F`,
assuming they are in bounds with respect to `F₂₃₄₇`: every such
assumption will be checked and enforced by the proof assistant. As an
example, below is the implementation of the addition for type `F`.

```rust,editable
# pub const Q: u16 = 2347;
# 
# #[hax_lib::attributes]
# pub struct F {
#     #[hax_lib::refine(v < Q)]
#     pub v: u16,
# }

use core::ops::Add;

impl Add for F {
    type Output = Self;
    fn add(self, rhs: Self) -> Self {
        Self {
            v: (self.v + rhs.v) % Q,
        }
    }
}
```

Here, F* is able to prove automatically that (1) the addition doesn't
overflow and (2) that the invariant of `F` is preserved. The
definition of type `F` in F* (named `t_F`) very explicitly requires
the invariant as a refinement on `v`.
