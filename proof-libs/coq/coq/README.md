## Dependencies

The coq libraries uses `compcert` for machine signed and unsigned integer modulo arithmetic, and `coqprime` for finite field arithmetic on prime modulus (to support hacspec's `nat_mod p` type). 
These requires the following repository:

```
opam repo add coq-released https://coq.inria.fr/opam/released --all-switches
```

Then one can install the dependencies through `opam`:

```
opam install coq-compcert coq-coqprime
```
(assuming you have coq installed through opam).

## Compiling the coq files

In folder `/coq`, type `make`. This compiles the coq libraries and the compiled examples, as defined in `_CoqProject`.
This requires the coq compiler to be installed (only tested on coq 8.13.1)

If you want to add a new example to `_CoqProject`, such that it is compiled through `make`, you should run `coq_makefile -f _CoqProject -o Makefile` in `/coq` to update the makefile.
