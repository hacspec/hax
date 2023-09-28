
module Make
    (F : Features.T
           with type mutable_variable = Features.On.mutable_variable
            and type mutable_reference = Features.On.mutable_reference
            and type nontrivial_lhs = Features.On.nontrivial_lhs
            and type arbitrary_lhs = Features.On.arbitrary_lhs
            and type reference = Features.On.reference) : sig
  include module type of struct
    module FB = F
    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end
