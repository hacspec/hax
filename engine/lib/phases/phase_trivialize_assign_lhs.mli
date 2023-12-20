module Make (F : Features.T) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.Off.Nontrivial_lhs
      include Features.On.Construct_base
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
