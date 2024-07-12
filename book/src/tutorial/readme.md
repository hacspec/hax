# Tutorial

This tutorial is a guide for formally verifying properties about Rust
programs using the hax toolchain. hax is a tool that translates Rust
programs to various formal programming languages.

The formal programming languages we target are called *backends*. Some
of them, e.g. [F*](https://fstar-lang.org/) or
[Coq](https://coq.inria.fr/), are general purpose formal programming
languages. Others are specialized tools:
[ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/) is
dedicated to proving properties about protocols.

This tutorial focuses on proving properties with the
[F* programming language](https://fstar-lang.org/).
