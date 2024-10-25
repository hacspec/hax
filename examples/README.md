# Examples

| Name               | Status of the F\* extraction |
| ------------------ | ---------------------------- |
| chacha20           | Typechecks                   |
| limited-order-book | Typechecks                   |
| sha256             | Lax-typechecks               |
| barrett            | Typechecks                   |
| kyber_compress     | Typechecks                   |

## How to generate the F\* code and typecheck it for the examples

<details>
  <summary><b>Requirements</b></summary>
  
  First, make sure to have hax installed in PATH. Then:
  
  * With Nix, `nix develop .#examples` setups a shell automatically for you.
     
  * Without Nix:
    1. install F* `v2024.01.13`<!---FSTAR_VERSION--> manually (see https://github.com/FStarLang/FStar/blob/master/INSTALL.md);
       1. make sure to have `fstar.exe` in PATH;
       2. or set the `FSTAR_HOME` environment variable.
    2. clone [Hacl*](https://github.com/hacl-star/hacl-star) somewhere;
    3. `export HACL_HOME=THE_DIRECTORY_WHERE_YOU_HAVE_HACL_STAR`.
</details>

To generate F\* code for all the example and then typecheck
everything, just run `make` in this directory.

Running `make` will run `make` in each example directory, which in
turn will generate F\* modules using hax and then typecheck those
modules using F\*.

Note the generated modules live in the
`<EXAMPLE>/proofs/fstar/extraction` folders.

## Coq

For those examples, we generated Coq modules without typechecking them.
The `<EXAMPLE>/proofs/coq/extraction` folders contain the generated Coq modules.
