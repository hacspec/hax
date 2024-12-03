# **Rust Item Extraction Using `cargo hax`**

## **Overview**
When extracting Rust items with hax, it is often necessary to include only a specific subset of items from a crate. The `cargo hax into` subcommand provides the `-i` flag to control which items are included or excluded, and how their dependencies are handled. This allows precise tailoring of the extraction process.

## **The `-i` Flag**
The `-i` flag accepts a list of patterns with modifiers to define inclusion or exclusion rules for Rust items. Patterns are processed sequentially from left to right, determining which items are extracted.

### **Basic Concepts**
- **Patterns**: Rust paths with support for `*` and `**` globs.
  - `*` matches any single segment (e.g., `mycrate::*::myfn`).
  - `**` matches any subpath, including empty segments (e.g., `**::myfn`).
- **Modifiers**:
  - `+`: Includes items and their dependencies (transitively).
  - `+~`: Includes items and their **direct dependencies only**.
  - `+!`: Includes only the item itself (no dependencies).
  - `+:`: Includes only the item's type signature (no body or dependencies).
  - `-`: Excludes items.

By default, **all items are included**, unless explicitly modified.

### **Practical Examples of the `-i` Flag Usage**

Consider the following crate (`mycrate`) with the `lib.rs` module:

```rust
fn interesting_function() { aux() }
fn aux() { foo::f() }
fn something_else() { /* ... */ }

mod foo {
    fn f() { /* ... */ }
    fn g() { /* ... */ }
    fn h() { /* ... */ }
    fn interesting_function() { something() }
    fn something() { /* ... */ }

    mod bar {
        fn interesting_function() { /* ... */ }
    }
}

fn not_that_one() { not_that_one_dependency() }
fn not_that_one_dependency() { /* ... */ }

fn not_extracting_function(_: u8) -> u8 {
    unsafe { /* ... */ }
    0
}
```

#### **1. Selectively Including Items with Dependencies**
```bash
cargo hax into -i '-** +mycrate::**::interesting_function' <BACKEND>
```

- **Explanation**:
  - `-**`: Excludes all items by default.
  - `+mycrate::**::interesting_function`: Includes all items matching `mycrate::**::interesting_function` and their dependencies.
- **Extracted Items**:
  1. `mycrate::interesting_function` (direct match).
  2. `mycrate::foo::interesting_function` (direct match).
  3. `mycrate::foo::bar::interesting_function` (direct match).
  4. `mycrate::aux` (dependency of `mycrate::interesting_function`).
  5. `mycrate::foo::f` (dependency of `mycrate::aux`).
  6. `mycrate::foo::something` (dependency of `mycrate::foo::interesting_function`).

#### **2. Excluding Specific Items**
```bash
cargo hax into -i '+** -*::not_that_one' <BACKEND>
```

- **Explanation**:
  - `+**`: Includes all items by default.
  - `-*::not_that_one`: Excludes any item named `not_that_one`, but keeps all other items, including `not_that_one_dependency`.
- **Extracted Items**: All except `mycrate::not_that_one`.

#### **3. Including Items Without Dependencies**
```bash
cargo hax into -i '-** +!mycrate::interesting_function' <BACKEND>
```

- **Explanation**:
  - `-**`: Excludes all items by default.
  - `+!mycrate::interesting_function`: Includes only `mycrate::interesting_function`, without dependencies.
- **Extracted Items**: Only `mycrate::interesting_function`.

#### **4. Including Items with Direct Dependencies Only**
```bash
cargo hax into -i '-** +~mycrate::interesting_function' <BACKEND>
```

- **Explanation**:
  - `-**`: Excludes all items by default.
  - `+~mycrate::interesting_function`: Includes `mycrate::interesting_function` and its direct dependencies (but not their transitive dependencies).
- **Extracted Items**:
  1. `mycrate::interesting_function`.
  2. `mycrate::aux` (direct dependency).
- **Excluded Items**:
  - `mycrate::foo::f` (transitive dependency of `mycrate::aux`).

#### **5. Including Items in Signature-Only Mode**
```bash
cargo hax into -i '+:mycrate::not_extracting_function' <BACKEND>
```

- **Explanation**:
  - `+:mycrate::not_extracting_function`: Includes only the type signature of `mycrate::not_extracting_function` (e.g., as an assumed or axiomatized symbol).
- **Extracted Items**:
  - The type signature of `mycrate::not_extracting_function`, without its body or dependencies.

### **Summary**
The `-i` flag offers powerful control over extraction, allowing fine-grained inclusion and exclusion of items with various dependency handling strategies. Use it to:
- Extract specific items and their dependencies (`+` or `+~`).
- Exclude certain items (`-`).
- Include items without dependencies (`+!`).
- Extract type signatures only (`+:`).

For complex crates, this flexibility ensures only the necessary parts are extracted, optimizing analysis or transformation workflows.

