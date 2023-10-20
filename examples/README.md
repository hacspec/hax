# Examples

| Name     | Status of the F* extraction |
| -------- | -------------- |
| chacha20 | Lax-typechecks |
| limited-order-book | Typechecks     |
| sha256   | Lax-typechecks |

## How to extract and typecheck an example
For each example `<EXAMPLE>`, there exists a a subdirectory
`./<EXAMPLE>/proof/fstar/` that contains a `Makefile`. This `Makefile`
extracts `<EXAMPLE>` as F* code and then typechecks it.

Thus, to generate the F* modules of an example `<EXAMPLE>` and to
**typecheck** them, you should:
1. move to the proper `extraction` subdirectory: `cd <EXAMPLE>/proofs/fstar/extraction`;
2. run `make`: `make` (or `OTHERFLAGS="--lax" make` if the example is only lax-checking).

