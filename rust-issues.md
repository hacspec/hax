# Rust Syntax Issues

A list of Rust code that isn't handled yet.

## Loops
```rust
for i in (0..10).step_by(2) {}
```

```rust
let array = [0u8; 10];
for i in array.chunks(2) {}
```

```rust
for i in 0..5 {}
```

```
error[CE0001]: (Diagnostics.Context.Phase FunctionalizeLoops): something is not implemented yet.            
               Only for loop are being functionalized for now
```

## Arrays, Vectors, and Slices
```rust
let mut a = [1, 2];
a[0] = 3;
```

```
error[CE0008]: (Diagnostics.Context.Phase (Reject ArbitraryLhs)): ExplicitRejection { reason: "unknown reason" }
```

```rust
let mut v1 = vec![1, 2, 3];
v1.append(&mut vec![4, 5, 6]);
```

```
error[CE0003]: The mutation of this &mut is not allowed here.
```

## Unknown & Bugs

```
error[CE0003]: The mutation of this &mut is not allowed here.
  --> src/lib.rs:65:26
   |
65 |         let leaf_index = self.hashes.iter().position(|h| h == &value_hash).unwrap();
   |                          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```
