# `generate_visitors`

This binary reads the AST module of hax and creates **standalone**
visitors. We need to define visitors and the types of the AST in two
separate modules. Otherwise, each time we instantiate the AST functor,
we end up re-defining every single visitor. Since the AST functor is
instantiated a lot, this used to lead to huge memory consumption while
building.

This binary takes an OCaml module that defines types as input and
outputs an OCaml module defining visitors for those types.

Note that this binary relies on the structure and naming of the AST of
hax; it is not intended for any other use.
