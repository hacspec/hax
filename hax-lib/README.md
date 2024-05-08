# hax library

This crate contains helpers that can be used when writing Rust code that is proven
through the hax toolchain.

**⚠️ The code in this crate has no effect when compiled without the `--cfg hax`.**

## Examples:

```rust
fn sum(x: Vec<u32>, y: Vec<u32>) -> Vec<u32> {
  hax_lib::assume!(x.len() == y.len());
  hax_lib::assert!(hax_lib::forall(|i: usize| hax_lib::implies(i < x.len(), || x[i] < 4242)));
  hax_lib::debug_assert!(hax_lib::exists(|i: usize| hax_lib::implies(i < x.len(), || x[i] > 123)));
  x.into_iter().zip(y.into_iter()).map(|(x, y)| x + y).collect()
}
```
