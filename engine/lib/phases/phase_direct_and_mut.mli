open Base
open Utils

module Make
    (F : Features.T
           with type raw_pointer = Features.Off.raw_pointer
            and type mutable_pointer = Features.Off.mutable_pointer) : sig
  include module type of struct
    module FB = struct
      include F
      include Features.On.Mutable_variable
      include Features.On.Arbitrary_lhs
      include Features.On.Nontrivial_lhs
      include Features.Off.Mutable_reference
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
    module FA = F
  end

  include ImplemT.T
end
