# A crate for secret-independent coding in Rust

## Using this crate

* Add `hax-secret-integers` as a dependency to your own crate
* Enable the `secret_independence` feature:
```
[features]
secret_independence = ["hax-secret-integers/secret_independence"]
```
* Replace any integer in your code by its secret counter-part, e.g. `u8` by `U8`, `u32` by `U32`
* The Rust typechecker will tell you if your code is secret independent

Example: See `examples/chacha20`

## Extracting F*

```
cargo hax into -i "+:**" fstar
```

