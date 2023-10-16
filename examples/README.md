# Examples

| Name     | Status         |
| -------- | -------------- |
| chacha20 | Lax-typechecks |
| lob      | Typechecks     |
| sha256   | Lax-typechecks |

## How-to extract and typecheck an example
To generate F* modules and **lax-typecheck** them for an example `<EXAMPLE>`:
1. `cd <EXAMPLE>/proofs/fstar/extraction`
2. `make` (or `OTHERFLAGS="--lax" make` if the example is only lax-checking)

