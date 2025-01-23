---
authors:
  - franziskus
  - lucas
title: "A new chapter"
date: 2025-01-21
---

# Hax Takes Flight: Announcing Our First Release and New Home at Cryspen!

We're thrilled to announce that hax is entering a new era of stability and
growth with the launch of our new website, a fresh start at Cryspen,
and our first official release,
[v0.1.0](https://github.com/cryspen/hax/releases/tag/cargo-hax-v0.1.0)!

After an intense period of research and development, hax is transitioning to a
more stable phase.
To support this evolution, we've moved the repository to its new home within the
Cryspen GitHub organization.
This change streamlines our processes and clarifies project ownership while
maintaining hax's open-source nature.
Cryspen is responsible for driving hax forward, but we enthusiastically
welcome contributions from the community, and continue working closely with
the team of existing contributors!

This move also marks our shift to a release-driven development model,
culminating in our first official release, v0.1.0.
While we anticipate some breaking changes in the lead-up to v1.0, detailed
release notes will clearly outline any backward compatibility issues.

### The state of hax

Hax currently boasts three actively used backends: ([F\*](https://fstar-lang.org/),
[Rocq](https://rocq-prover.org/) and [SSProve](https://github.com/SSProve/ssprove)).
While Cryspen primarily focuses on the F\* backend, [Bas Spitters](https://www.au.dk/en/spitters@cs.au.dk)
and his team at the University of Aarhus are actively developing and utilizing
the Rocq and SSProve backends. Cryspen also supports an experimental backend for
[ProVerif](https://bblanche.gitlabpages.inria.fr/proverif/).

With this initial release, hax can process a significant subset of Rust code.
Both the frontend, which extracts a JSON AST from the Rust compiler, and the
engine, which lowers the code to the backends, have undergone major
improvements and stabilization throughout 2024.

Our new website provides a central hub for all things hax.
Users can explore the [manual](../../manual/index.md), experiment with the
interactive [hax playground](https://hax-playground.cryspen.com/),
and delve into a diverse collection of [examples](https://github.com/cryspen/hax/tree/main/examples)
showcasing hax's capabilities.

We will work on improving the manual and developer documentation over the next
few months.

#### Hax in Action

Over the past year, hax has proven its versatility in various projects:

- [Verifying Bertie](https://cryspen.com/post/hax-pv/): A TLS 1.3 implementation, verified with the ProVerif backend
- [Verifying ML-KEM](https://cryspen.com/post/ml-kem-verification): A post quantum cryptographic algorithm verified with the F\* backend
- [Verifying Smart Contracts](https://github.com/hacspec/hacspec.github.io/blob/master/coqpl24-paper9-13.pdf): Leveraging the Rocq backend for enhanced security verification.

#### The Road Ahead

While hax can handle a substantial portion of Rust code, certain limitations
remain.
Features like Generic Associated Types (GATs), some Rust nightly features, specific
loop and pattern structures, and a range of mutations are not yet supported.

??? hint "Detailed list of unsupported features"
    Here's some content.

    **GATs**

    Support for Generic Associated Types (GATs) in the frontend is under consideration
    ([Issue #915](https://github.com/hacspec/hax/issues/915))

    **Rust nightly features**

    A full list of unsupported Rust nightly features can be found with the [unsupported-rust label](https://github.com/hacspec/hax/issues?q=is%3Aissue%20state%3Aopen%20nightly%20label%3Aunsupported-rust).

    **Pattern**

    Some expressive Rust patterns are not supported yet in the hax engine.
    For example, [range patterns](https://github.com/hacspec/hax/issues/925) such as
    `0..12`, [`as` patterns](https://github.com/hacspec/hax/issues/833) such as `x @ Option(_)` or [array or slice patterns](https://github.com/hacspec/hax/issues/804) such as `[head, ..tail]` are not supported.

    **Mutation**

    - Mutations inside closures are not supported ([Issue #1060](https://github.com/hacspec/hax/issues/1060))
    - Re-borrowing mutable refferences is not allowed ([Issue #420](https://github.com/hacspec/hax/issues/420))
    - Implicit reborrowing of mutable references is not supported ([Issue #419](https://github.com/hacspec/hax/issues/419))
    - User-defined functions cannot return `&mut`s ([Issue #418](https://github.com/hacspec/hax/issues/418))
    - Calling `&mut`-returning functions is not allowed in general ([Issue #418](https://github.com/hacspec/hax/issues/418), [Issue #494](https://github.com/hacspec/hax/issues/494) and [Issue #491](https://github.com/hacspec/hax/issues/491))
    - Enum variants cannot be mutated ([Issue #493](https://github.com/hacspec/hax/issues/493))

    **Loops**

    - Unconditional loops `loop {...}` ([Issue #124](https://github.com/hacspec/hax/issues/124))
    - While let `while let .. = .. {}` ([Issue #113](https://github.com/hacspec/hax/issues/113))
    - Loops without side effect ([Issue #405](https://github.com/hacspec/hax/issues/405))

    **`const` inline blocks**

    Inline `const` blocks are not supported yet.
    [Issue #923](https://github.com/hacspec/hax/issues/923)

### Parting Thoughts

This is an exciting time for hax!
With our new home at Cryspen, a dedicated release model, and a growing community,
we're confident that hax will continue to mature and empower developers to build
secure and reliable software.

We encourage you to explore the new hax website, dive into the documentation,
and experiment with the playground.
Join us on this journey!
Contribute to the project, share your feedback, and help us shape the future of
Rust verification.
