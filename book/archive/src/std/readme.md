# The hacspec std library

The hacspec standard library contains a host of functions, type generators
and methods that define the base objects manipulated in classic cryptographic
primitives.

Methods in the standard library can be divided into three categories:
1. The `not_hacspec` methods whose signature and body does not belong to the
hacspec fragment of Rust. They should not be used in hacspec code, but can
be used as helpers for e.g. testing.
2. The `unsafe_hacspec` methods whose signature belongs to hacspec but not
the body. These methods can be used in hacspec programs but their body
is part of the trusted codebase.
3. The `in_hacspec` methods whose signatures and bodies belong to the
hacspec fragment of Rust. These can be used safely in hacspec programs.
