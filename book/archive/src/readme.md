# Introduction

hacspec is a specification language for crypto primitives, protocols, and more.
It is a subset of the [Rust] programming language, focused on functional
programming and it avoids the use of mutable state as much as possible.

This book gives an overview of:
* [The hacspec language](./language);
* The different parts of the project:
    * [the standard library](./std),
    * [examples of hacspec programs](./examples);
* How to use hacspec to write [specifications] for standards and [verification];
* How to use hacspec to generate [test vectors];
* [Work on the hacspec compiler and tooling itself](./developers).

For a quick introduction you can also check out these [slides] from April 2021.
An in-depth [technical report] is also available, and serves as a reference
for the language formalization.

[slides]: https://raw.githubusercontent.com/hacspec/hacspec/master/presentation_slides.pdf
[technical report]: https://hal.inria.fr/hal-03176482
[Rust]: https://www.rust-lang.org/
[specifications]: ./usage/specifications.md
[verification]: ./usage/verification.md
[test vectors]: ./usage/test_vectors.md
