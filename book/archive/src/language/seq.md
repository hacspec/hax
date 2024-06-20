# Sequences and arrays

## Sequences

The staple `Vec` type is forbidden in hacspec. Instead, you have to use the
type `Seq`, which is implemented as a wrapper around `Vec`.

The most notable differences between `Seq` and `Vec` is that `Seq` is not
resizable, and does not support `push` and `pop` operations. Instead, the
final length of the seq has to be provided at creation time. See the
hacspec standard library documentation for more details.

`Seq` is a built-in generic type that always has to be indexed by the content of the
cells: `Seq<u8>`, etc.

## Arrays

The native Rust array types `[<type of contents>, <size>]` is forbidden in
hacspec. Instead, you have to declare nominally at the top-level new array types
for a specific cell content and size with:

```rust, noplaypen
array!(FooArray, u8, 64);
// This declares type FooArray as an array of u8 of size 64
bytes!(BarArray, 64);
// bytes! is a specialized version of array! with secret bytes
array!(BazArray, u8, 64, type_for_indexes:BazIndex);
// The additional argument type_for_indexes defines an alias of usize
// intended to spot which usizes are used to index BazArray (useful for
// verification)
```

