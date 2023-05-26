open Base
open Utils

module Make
    (F : Features.T
           with type continue = Features.Off.continue
            and type early_exit = Features.Off.early_exit) : sig
  include module type of struct
    open Ast
    module FA = F

    module FB = struct
      include F
      include Features.Off.Loop
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
