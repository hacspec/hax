open! Prelude

module Make
    (F : Features.T
           with type raw_pointer = Features.Off.raw_pointer
            and type mutable_reference = Features.Off.mutable_reference) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.Off.Mutable_pointer
      include Features.Off.Lifetime
      include Features.Off.Reference
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
