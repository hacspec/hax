open Base
open Utils

module Make
    (F : Features.T
           with type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.Off.Continue
      include Features.Off.Early_exit

      (* TODO: when break is introduced: include Features.Off.Break *)
      (* include Features.Off.Mutable_variable *)
      include Features.On.Monadic_binding
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
