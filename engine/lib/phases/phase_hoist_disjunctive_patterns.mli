(** This phase eliminates nested disjunctive patterns (leaving 
    only shallow disjunctions). It moves the disjunctions up 
    to the top-level pattern. *)

module Make : functor (F : Features.T) -> sig
  include module type of struct
    module FB = F
    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T

  val hoist_disjunctions :
    < visit_F__block : unit -> _ -> _ ; .. > Ast_visitors.Make(F).map
end
