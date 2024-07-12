# The hacspec language

This section gives an informal description of the hacspec language, whose
goal is to provide hands-on documentation for users of the language. For
a formal specification of the semantics of the language, please refer
to the [technical report][1].

hacspec is a domain-specific language embedded inside Rust. This means that
all correct hacspec programs are correct Rust programs: you can use
the usual Rust tooling for working on your hacspec developments. However,
hacspec is a strict subset of Rust: this means that some features of Rust
are forbidden inside hacspec. The goal of restricting the expressiveness of
the language is twofold: first, help domain experts such as cryptographers
convey their specifications in a fashion that should help them avoid
mistakes; second, provide a way for Rust programmers to interact with theorem
provers such as F\* or Coq.

[1]: https://hal.inria.fr/hal-03176482
