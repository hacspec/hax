# Stack example
This example is a simple interpreter for a stack.

## How to build
```sh
cargo hax into coq
```

## Coq
Now we have the file `proofs/coq/extraction/Coq_example.v`.
To run the files we first need to install some dependencies.

### Dependencies for Coq
The coq backend depends on `coq-record-update` to implement Rust record updates. 
This can be installed by
```sh
opam install coq-record-update
```
or alternatively the import lines 
```coq
From RecordUpdate Require Import RecordSet.
Import RecordSetNotations.
```
can be commented out.

## Library required to run
As Rust implicitly imports the `Core` library for a lot of the basic functionality, we will also require a core library for Coq. For this small example, we build a dummy library with the required definitions, to run the example. As a hack to get this to run we add
```
mod dummy_core_lib;
use dummy_core_lib::*;
```
to the Rust example file `src/lib.rs`. The definitions of the library are put into `proofs/coq/extraction/dummy_core_lib.v` to match this import.

## Running the code and doing proofs
We can set up a Coq project by making a `_CoqProject` file in `proofs/coq/extraction/`.
```
-R ./ Coq_example
-arg -w
-arg all

./dummy_core_lib.v
./Coq_example.v
./Coq_proofs.v
```
We then build a makefile from the project file by
```sh
coq_makefile -f _CoqProject -o Makefile
```
and run `make` to build. Any tests and proofs, we put into a seperate file `proofs/coq/extraction/Coq_proofs.v`. which imports the generated file, such that we can update and regenerate the file, without overwriting the proofs.
