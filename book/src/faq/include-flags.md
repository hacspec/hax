# The include flag: which items should be extracted, and how?

Often, you need to extract only a portion of a crate. The subcommand
`cargo hax into` accepts the `-i` flag which will help you to include
or exclude items from the extraction.

Consider the following `lib.rs` module of a crate named `mycrate`.

```rust
fn interesting_function() { aux() }
fn aux() { foo::f() }
fn something_else() { ... }
mod foo {
  fn f() { ... }
  fn g() { ... }
  fn h() { ... }
  fn interesting_function() { something() }
  fn something() { ... }
  mod bar {
    fn interesting_function() { ... }
  }
}
fn not_that_one() { not_that_one_dependency() }
fn not_that_one_dependency() { ... }
```

Here are a few examples of the `-i` flag.
 - `cargo hax into -i '-** +mycrate::**::interesting_function' <BACKEND>`  
   The first clause `-**` makes items not to be extracted by default.  
   This extracts any item that matches the [glob pattern](https://en.wikipedia.org/wiki/Glob_(programming)) `mycrate::**::interesting_function`, but also any (local) dependencies of such items. `**` matches any sub-path.  
   Thus, the following items will be extracted:
    + `mycrate::interesting_function` (direct match);
    + `mycrate::foo::interesting_function` (direct match);
    + `mycrate::foo::bar::interesting_function` (direct match);
    + `mycrate::aux` (dependency of `mycrate::interesting_function`);
    + `mycrate::foo::f` (dependency of `mycrate::aux`);
    + `mycrate::foo::something` (dependency of `mycrate::foo::interesting_function`).
 - `cargo hax into -i '+** -*::not_that_one' <BACKEND>`  
   Extracts any item but the ones named `<crate>::not_that_one`. Here,
   everything is extracted but `mycrate::not_that_one`, including
   `mycrate::not_that_one_dependency`.
 - `cargo hax into -i '-** +!mycrate::interesting_function' <BACKEND>`  
    Extracts only `mycrate::interesting_function`, not taking into
    account dependencies.
 - `cargo hax into -i '-** +~mycrate::interesting_function' <BACKEND>`  
    Extracts `mycrate::interesting_function` and its direct
    dependencies (no transitivity): this includes `mycrate::aux`, but
    not `mycrate::foo::f`.

Now, suppose we add the function `not_extracting_function`
below. `not_extracting_function` uses some unsafe code: this is not
supported by hax. However, let's suppose we have a functional model
for this function and that we still want to extract it as an
axiomatized, assumed symbol.
```rust
fn not_extracting_function(u8) -> u8 {
    ... 
    unsafe { ... }
    ...
}
```

 - `cargo hax into -i '+:mycrate::not_extracting_function' <BACKEND>`  
   Extracts `mycrate::not_extracting_function` in signature-only mode.

