# `ppx_functor_application`

## Motivation
The engine consists of numerous phases, implemented as OCaml functors
parametrized over "AST features" (see the book). Two phases can be
binded (sequenced) via `Phase_utils.BindPhase` functor.

Since OCaml define (or let users define) infix notations for functor
application, combining many phases (functors) results in the following
christmas tree looking kinds of code:

```ocaml
struct
    module ARG0 = (Phases.Reject.RawOrMutPointer)(Features.Rust)
    module ARG1 = (Phases.Transform_hax_lib_inline)(ARG0.FB)
    module ARG2 = (Phases.Specialize)(ARG1.FB)
    module ARG3 = (Phases.Drop_sized_trait)(ARG2.FB)
    module ARG4 = (Phases.Simplify_question_marks)(ARG3.FB)
    module ARG5 = (Phases.And_mut_defsite)(ARG4.FB)
    module ARG6 = (Phases.Reconstruct_for_loops)(ARG5.FB)
    module ARG7 = (Phases.Reconstruct_while_loops)(ARG6.FB)
    module ARG8 = (Phases.Direct_and_mut)(ARG7.FB)
    module ARG9 = (Phases.Reject.Arbitrary_lhs)(ARG8.FB)
    module ARG10 = (Phases.Drop_blocks)(ARG9.FB)
    module ARG11 = (Phases.Drop_references)(ARG10.FB)
    module ARG12 = (Phases.Trivialize_assign_lhs)(ARG11.FB)
    module ARG13 = (Side_effect_utils.Hoist)(ARG12.FB)
    module ARG14 = (Phases.Simplify_match_return)(ARG13.FB)
    module ARG15 = (Phases.Drop_needless_returns)(ARG14.FB)
    module ARG16 = (Phases.Local_mutation)(ARG15.FB)
    module ARG17 = (Phases.Reject.Continue)(ARG16.FB)
    module ARG18 = (Phases.Cf_into_monads)(ARG17.FB)
    module ARG19 = (Phases.Reject.EarlyExit)(ARG18.FB)
    module ARG20 = (Phases.Functionalize_loops)(ARG19.FB)
    module ARG21 = (Phases.Reject.As_pattern)(ARG20.FB)
    module ARG22 = (Phases.Traits_specs)(ARG21.FB)
    module ARG23 = (Phases.Simplify_hoisting)(ARG22.FB)
    module ARG24 = (Phases.Newtype_as_refinement)(ARG23.FB)
    module ARG25 = (SubtypeToInputLanguage)(ARG24.FB)
    module ARG26 = (Identity)(ARG25.FB)
    include
        ((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(((BindPhase)(ARG0))(ARG1)))(ARG2)))(ARG3)))(ARG4)))(ARG5)))(ARG6)))(ARG7)))(ARG8)))(ARG9)))(ARG10)))(ARG11)))(ARG12)))(ARG13)))(ARG14)))(ARG15)))(ARG16)))(ARG17)))(ARG18)))(ARG19)))(ARG20)))(ARG21)))(ARG22)))(ARG23)))(ARG24)))(ARG25)))(ARG26)
end
```

The system of phases is supposed to let backends opt-in or out easily
for phases. This syntactic limitation was a major issue for that.

## Solution
This PPX defines a small DSL that embeds in the OCaml syntax of
expressions to provide a nice way of binding phases functors via a
`|>` infix operator.

Example:
```ocaml
module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.RawOrMutPointer(Features.Rust)
  |> Phases.Transform_hax_lib_inline
  |> Phases.Specialize
  |> Phases.Drop_sized_trait
  |> Phases.Simplify_question_marks
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_for_loops
  |> Phases.Reconstruct_while_loops
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]
```

Note: the `[@ocamlformat "disable"]` annotation is important,
otherwise `ocamlformat` tries to format those PPX invokations with its
rules for expressions, yielding rather ugly looking code...

### Syntax
 - `Name`: a module `Name`
 - `Name(X, Y, Z)`: the application of the functor `Name` with three arguments `X`, `Y` and `Z`
 - `(module <M>)`: the arbitary OCaml module expression `<M>`
 - `<a> <b>`: the application of the module described by `<a>` and the module described by `<b>`
 - `(fun X -> <a>)`: a "functor" from `X` to `<a>`
 - `<a> |> <b>`: `<a>` binded with `<b>`
