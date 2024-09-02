# Error handling

Error handling in Rust is done via the `Result` type (see the structs and
enums section). But on top of explicit pattern-matching, hacspec also
supports the popular `?` operator to quickly perform an early return and
propagate the error case upwards.

`?` is only allowed at the very end of an expression in a let-binding or
reassignment statement:

```rust, noplaypen
let x = foo(true)?; // GOOD
let y = foo(bar(0)?); // ERROR: the ? is not at the end of the statement
```

Currently, `?` is the only way to return early in a hacspec function.
