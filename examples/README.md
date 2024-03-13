# Examples

| Name               | Status of the F\* extraction |
| ------------------ | ---------------------------- |
| chacha20           | Typechecks                   |
| limited-order-book | Typechecks                   |
| barrett            | Typechecks w/ proofs         |
| kyber_compress     | Typechecks w/ proofs         |
| sha256             | Lax-typechecks               |

## Open Source Crypto Workshop

To get started, pull the docker image for your platform.

```bash
docker pull franziskus/hax:x64
```

or

```bash
docker pull franziskus/hax:arm64
```

Then run the image, with the correct tag for your platform

```bash
docker run -p 3818:3000 --rm --name hax -td franziskus/hax:{arm64, x64} password
```

Then point your browser to `http://localhost:3818/?tkn=password&folder=/home/hax-user/hax`

### Examples

For all examples the following is the general workflow.

Open the example in `examples/<name>`.
The code is in `examples/<name>/src/lib.rs`.

To extract the Rust code to F\*, run `cargo hax into fstar` in the crate.
This generates a fresh F\* extraction in `proofs/fstar/extraction/<crate-name>.fst`.

Run `make` in `proofs/fstar/extraction` to see that/if the extracted code type checks.
When it typechecks, you proved panic freedom of the code! Congrats 🎉

#### ChaCha20

Chacha20 typechecks out of the box.

Some of the functions are annotated with pre-conditions.
For example `chacha20_line` has preconditions

```rust
#[hax::requires(a < 16 && b < 16 && d < 16)]
```

This is necessary to prove panic freedom.
Otherwise array indexing in the function like `state[a]` may panic because `state.len() == 16`.

To see that F* can prove panic freedom statically, try to change one of the bounds to `17` or larger.
Now, after extracting the F* code again, the typechecking will fail.

#### Barrett Reduction

#### ML-KEM (Kyber) Compression

## How to generate the F\* code and typecheck it for the examples

<details>
  <summary><b>Requirements</b></summary>
  
  First, make sure to have hax installed in PATH. Then:
  
  * With Nix, `nix develop .#fstar` setups a shell automatically for you.
     
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
