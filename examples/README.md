# Examples

| Name               | Status of the F\* extraction | Details                                   |
| ------------------ | ---------------------------- | ----------------------------------------- |
| chacha20           | Typechecks                   | [Instructions](#chacha20)                 |
| limited-order-book | Typechecks                   |                                           |
| barrett            | Typechecks w/ proofs         |                                           |
| kyber_compress     | Typechecks w/ proofs         | [Instructions](#ml-kem-kyber-compression) |
| sha256             | Lax-typechecks               |                                           |

## Open Source Crypto Workshop

### Before the Workshop

Pull the docker image for your platform.
The image is relatively big, so please do this on a reliable connection and don't
rely on the workshop's wifi.

```bash
docker pull franziskus/hax:x64
```

or

```bash
docker pull franziskus/hax:arm64
```

The docker image has hax pre-installed, as well as the F\* toolchain.
As entry point, the docker image provides a vscode interface that you can open
in the browser.

There's a [Zulip](https://hacspec.zulipchat.com/#narrow/stream/429856-oscw2024) that you can join if you have any questions. Please use the linked oscw2024 channel for that.

### Running the docker image

To use the docker image, run it with the correct tag for your platform

```bash
docker run -p 3818:3000 --rm --name hax -td franziskus/hax:{arm64, x64} password
```

Then point your browser to `http://localhost:3818/?tkn=password&folder=/home/hax-user/hax`

### Examples

For all examples the following is the general workflow.
Note that there is a more detailed description for the chacha20 and kyber
compression target below.

There's also a [tutorial in the book](https://hacspec.org/book/tutorial/index.html) that can be run.

<details>
  <summary>VSCode how-to</summary>

Command Palette

- ⇧⌘P (Mac) or ⇧^P or View > Command Palette will bring you directly to the editor commands
- [More docs](https://code.visualstudio.com/docs/getstarted/userinterface#_command-palette)

Terminal

- To toggle the terminal panel, use the ⌃` keyboard shortcut.
- To create a new terminal, use the ⌃⇧` keyboard shortcut.
- [More docs](https://code.visualstudio.com/docs/terminal/basics)

</details>

Open the example in `examples/<name>`.
The code is in `examples/<name>/src/lib.rs`.

#### Extracting F\* Code

The hax tool extracts F\* code (and other languages) from the Rust crate.

To extract the Rust code to F\*, run `cargo hax into fstar` in the crate.
Most examples require a higher than default z3 limit, which makes sure that z3 tries
longer to find an answer.
To do this, add `--z3rlimit 150` to the `cargo hax into fstar` command.
This generates a fresh F\* extraction in `proofs/fstar/extraction/<crate-name>.fst`.

#### Typechecking the F\* Code

Typechecking the F\* code tells us whether the properties put on the Rust code
hold.
Lax-typechecking of the F\* code ensures that the code is syntactically correct.
Fully typechecking proves that the properties on it hold.

##### Using the Makefile

Run `make` in `proofs/fstar/extraction` to see that/if the extracted code typechecks.
When it typechecks, you proved panic freedom of the code! Congrats 🎉

##### Interactive Mode

The interactive mode is preferrable because it allows lax and fully typechecking.
You can also typecheck only parts of a file.

Use the vscode commands (`>`) to trigger F\* (start typing `F*`).
Note that you may have to restart F\* after each use.
(The vscode extension is not very stable yet.)
You can lax-typecheck (Lax to position) the F\* code to ensure that the code is syntactically correct, or "Verify to position" to fully typecheck.
In each case it will run F\* up to the cursor in the file.

#### ChaCha20

Chacha20 typechecks out of the box.
_Note however that it takes a while to go through._

Some of the functions are annotated with pre-conditions.
For example `chacha20_line` has preconditions

```rust
#[hax::requires(a < 16 && b < 16 && d < 16)]
```

This is necessary to prove panic freedom.
Otherwise array indexing in the function like `state[a]` may panic because `state.len() == 16`.

To see that F\* can prove panic freedom statically, try to change one of the bounds to `17` or larger.
Now, after extracting the F\* code again, the typechecking will fail.

You can also try a smaller value for one of the indices.
In this case typechecking of the function goes through (because it will always
succeed with the given preconditions).
However, when you typecheck the next function, which calls the `chacha20_line`,
it will fail, because it tries to call the function with a value that does not
meet the tighter pre-condition.

In this example you proved, statically, panic freedom for the Rust code.
In particular, none of the operations, like the indexing the state, can panic.
This rules out some big class of bugs commonly seen in cryptographic code, both
primitives and protocols.
No out of bound reads or writes, and no arithmetic over- or under-flows.

#### ML-KEM (Kyber) Compression

This is a function to compress [ML-KEM](https://nvlpubs.nist.gov/nistpubs/FIPS/NIST.FIPS.203.ipd.pdf)
(Kyber) field elements.

This example uses post conditions and a little more complicated arithmetic that
F\* is not able to prove out of the box.
So here we go beyond panic freedom and prove, some pretty loose, properties of
the code.

When the typechecking does not go through, try adding the code snippets below
into the F\* code just before the result is returned in the respective functions.

- `get_n_least_significant_bits`

```ocaml
Rust_primitives.Integers.logand_mask_lemma value (v n);
```

- `compress_unsafe` and `compress`

```ocaml
Rust_primitives.Integers.logand_mask_lemma compressed (v coefficient_bits);
```

---

# Regular Readme

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
