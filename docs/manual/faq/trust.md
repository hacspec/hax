---
title: Trust
weight: -4
---

# Is hax-verified code guaranteed to be correct?

No.

Formally verifying code with hax (or any other tool) gives a high assurance that the code is
correct, higher than what can be achieved with auditing and testing alone. But there are many
moving parts that can fail. The goal of this page is to summarize what can still go wrong.

## Specification

The most common issue with verified code is that the specification does not state what it is
intended to state. No improvements to our tools can eradicate this fundamental issue entirely.
The specification is the source of truth and is therefore unverifiable.
To mitigate this danger, auditing and testing of the specification is crucial.
After extraction via hax, one can also prove properties about the specification's code
to gain more confidence about its correctness.

## Verification coverage

This is probably the second-most common issue with verified code.
It is rare that 100% of a crate can realistically be extracted and verified.
Understanding exactly the scope of
what should be extracted is paramount to using hax on real-world projects.
The hax CLI has various options to exclude
parts of the code from extraction, and parts of the code can also be excluded via annotations.
But using these features can also be dangerous: We must make sure that all of the code
that we want to verify is actually included the extraction.

Some projects have their core implemented in Rust and offer wrappers for other languages.
Wrappers can be buggy, too, and if they are not implemented in Rust, they are out of scope for hax.

## Drift between source code and proof artifacts

A real-world Rust project constantly changes, and keeping up the proofs with the code changes
can be costly. So sometimes, it can make sense to verify only a snapshot of the code, but that also
means that only that snapshot is verified. When the ambition is
to keep the proofs up to date with all code changes, CI must enforce that both extraction and
verification keep up with every change.

## Extraction

Verification with hax relies on hax translating the code faithfully from Rust to the backend
language (e.g., Lean). We also rely on the `hax-lib` macros to expand correctly and
on hax to faithfully translate them and the specification as a whole.

Depending on the backend, hax internally uses various tools to implement the translations,
and we rely on these.
For Lean, there are
charon (which in turn uses rustc) and aeneas (with some modifications) that are used as trusted tools.
For F*, the trusted toolchain contains the hax frontend (also using rustc) and the hax engine.

## Model of Rust and Rust libraries

Each backend comes with a library modeling the semantics of Rust and its core library.
The verification relies on this library modeling the semantics of Rust and its core library
correctly.

For Lean and F*, we model Rust's `core` and `alloc` libraries directly in Rust
(see [our core models library](https://github.com/cryspen/hax/tree/main/hax-lib/core-models)).
This Rust library gets extracted via hax into Lean and F*. Only some Rust primitives
that can not be modeled in terms of others are implemented directly in the backend languages.
With this approach, we need to trust the Rust model, their translation into the backend language,
and the Rust primitives written in the backend language. The advantage of the approach is
that a Rust model of Rust is easier to audit and that sharing the code between backends
leads to a higher chance of finding bugs.

In some projects, we also model external Rust crates that are not themselves verified.
If we do, correctness of the verification also relies on the correctness of these models.

## Backend prover

We are also relying on the backend provers (e.g., Lean or F*) to work correctly.
The most common issue here is probably that running the prover (e.g., `lake build`) may not
always run all the proofs that are supposed to be run. For example, a contract that is stated in
Rust and that is extracted correctly, may not have a corresponding Lean theorem. Or the Lean
theorem might be in a file that is not actually imported and as a result remains unchecked when
running `lake build`.

Most provers allow users to state axioms that the prover is supposed to assume as fact
as a basis for its proofs.
Depending on the prover, such assumptions can be called `sorry`s, `admit`s, or `assume`s.
If there are unintended axioms in the code, the verification
is compromised.
In Lean, `#print axioms` can be used to guard against this.
Also, correctness theorems stated in the prover language may carry additional preconditions
that are not present in the Rust annotations.

And of course, even widely used tools like Lean can have soundness bugs,
allowing users (and AI) to prove false statements.
For Lean in particular, there are various known ways to trick the system when relying only
on the compilation of the code to pass. The tool [comparator](https://github.com/leanprover/comparator)
is recommended for code that might use Lean adversarially,
in particular for AI generated proofs.
Comparator can also be used to check
for unintended axioms and preconditions and to ensure that a given list of theorems is
actually part of the verification.

## Beyond functional correctness

hax can only verify functional correctness. It cannot guard against side channel attacks,
it cannot verify unsafe Rust code, and it cannot model concurrency.

## Rust compiler

If all of the above goes well, we can be sure that the Rust code is correct with respect
to its specification. But to actually run
the Rust code, we still need to compile it. Since hax only verifies the Rust code and
not the machine code that the Rust compiler produces, we also need to trust the Rust compiler.

## Environment

Finally, we also need to trust the environment on which the verification runs.
If the operating system or the hardware is buggy or compromised, we cannot be sure that
the verification actually executes as intended.
