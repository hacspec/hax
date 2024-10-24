(** This phase transforms `return e` expressions into `e` when `return
e` is on an exit position. It should come after phase `RewriteControlFlow`
and thus eliminate all `return`s. Inside loops it rewrites `return`,
`break` and `continue` as their equivalent in terms of the `ControlFlow`
wrapper that will be handled by the specific fold operators introduced by 
phase `FunctionalizeLoops`. *)

module Make (F : Features.T) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.On.Fold_like_loop
      include Features.Off.Early_exit
      include Features.Off.Break
      include Features.Off.Continue
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
