open Base
open Utils

module Make
    (F : Features.T
           with type mutable_reference = Features.Off.mutable_reference
            and type mutable_pointer = Features.Off.mutable_pointer
            and type raw_pointer = Features.Off.raw_pointer
            and type arbitrary_lhs = Features.Off.arbitrary_lhs
            and type nontrivial_lhs = Features.Off.nontrivial_lhs
            and type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding) : sig
  include module type of struct
    open Ast
    module FA = F

    module FB = struct
      include F
      include Features.Off.Mutable_variable
      include Features.On.State_passing_loop
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
