module
public import Aeneas

@[expose] public section

/-!
# Missing Aeneas

Material that Aeneas's Lean backend does not (yet) provide but that the models in
`CoreModels` need.

-/

namespace Aeneas.Std.ScalarElab

open Lean

/-! ## `%ToLowerCase`: working around a missing lowercase keyword in Aeneas

Aeneas's `ScalarElab` substitution keywords in `uscalar`/`iscalar` blocks
(`«%S»` for a whole name component, `'S` for a substring of one) always
insert the *capitalised* scalar name: `U8`, `Usize`, `I128`, `Isize`.
That is right for Aeneas's own lemmas, which live in the `U8`/`I8` namespaces, but
it cannot name a model extracted from Rust: those follow the Rust item names, and Rust
spells the scalar types in lowercase (`pow_u8`, `pow_usize`). So there is no way to refer to
such a model from inside a `uscalar`/`iscalar` block. -/

/-- `%ToLowerCase x` lowercases the last component of the identifier `x`.

Combine it with Aeneas's `'S` keyword to name a lowercase-spelled model from inside a
`uscalar`/`iscalar` block:

```
uscalar theorem «%S».pow_spec (x : «%S») (n : U32) :
    partialSpec ((%ToLowerCase rust_primitives.arithmetic.«pow_'S») x n) … := …
```

`'S` expands `pow_'S` to `pow_U8`, and `%ToLowerCase` lowercases it to `pow_u8`. The result
is a plain identifier, so it is resolved against the enclosing namespace as usual. -/
scoped syntax:max (name := toLowerCaseIdent) "%ToLowerCase" ident : term

macro_rules
  | `(%ToLowerCase $x:ident) =>
    match x.getId with
    | .str pre last => return mkIdent (.str pre last.toLower)
    | n => Macro.throwError s!"'%ToLowerCase' expects an identifier with a named last \
                              component, got '{n}'"

end Aeneas.Std.ScalarElab

namespace Aeneas.Std

open Std.Do

/-- The equation lemmas of a structurally recursive definition state its `do` blocks with
`Std.bind`, which `mvcgen` does not step through: it only knows `>>=`. Registered as a spec,
this equation lets `mvcgen` rewrite the former into the latter. -/
@[spec]
theorem bind_eq_tc_bind {α β : Type} (x : RustM α) (f : α → RustM β) :
    Std.bind x f = x >>= f := rfl

end Aeneas.Std
