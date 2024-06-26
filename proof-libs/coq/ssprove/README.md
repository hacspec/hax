## Dependencies

The coq libraries uses `ssprove/jasmin` for machine signed and unsigned integer modulo arithmetic, and `coqword` for finite field arithmetic on prime modulus (to support hacspec's `nat_mod p` type).
This requires the following repository:

```
opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
```

Then one can install the dependencies through `opam` (assuming you have coq installed through opam)

```
opam update
opam install conf-ppl.1 -y
opam install coq-mathcomp-word.2.0 -y
opam pin jasmin https://github.com/SSProve/ssprove.git#3d40bc89 -y
opam pin ssprove https://github.com/SSProve/ssprove.git#bead4e76acbb69b3ecf077cece56cd3fbde501e3 -y
opam upgrade -y
```
the development uses the Jasmin branch of SSProve, meaning one might need to install these from source.

## Docker

There is a docker container with the dependencies installed (Coq / Rust) at `ghcr.io/cmester0/hacspec_ssprove:8.15.2`.

## Compiling the coq files

In folder `/coq_ssprove`, type `make`. This compiles the coq libraries and the compiled examples, as defined in `_CoqProject`.

If you want to add a new example to `_CoqProject`, such that it is compiled through `make`, you should run `coq_makefile -f _CoqProject -o Makefile` in `/coq` to update the makefile.
