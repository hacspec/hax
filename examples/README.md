# Examples

| Name     | Status of the F* extraction |
| -------- | -------------- |
| chacha20 | Lax-typechecks |
| limited-order-book | Typechecks     |
| sha256   | Lax-typechecks |

## How to generate the F\* code and typecheck it for the examples
To generate F\* code for all the example and then typecheck
everything, just run `make` in this directory.

Running `make` will run `make` in each example directory, which in
turn will generate F\* modules using hax and then typecheck those
modules using F\*.

Note the generated modules live in the
`<EXAMPLE>/proofs/fstar/extraction` folders.
