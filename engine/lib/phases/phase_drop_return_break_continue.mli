(** This phase transforms `return e` expressions into `e` when `return
e` is on an exit position. It should come after phase `RewriteControlFlow`
and thus eliminate all `return`s. Inside loops it rewrites `return`,
`break` and `continue` as their equivalent in terms of the `ControlFlow`
wrapper that will be handled by the specific fold operators introduced by 
phase `FunctionalizeLoops`. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
