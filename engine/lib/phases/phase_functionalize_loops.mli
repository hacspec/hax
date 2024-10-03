open! Prelude

module Make
    (F : Features.T
           with type continue = Features.Off.continue
            and type early_exit = Features.Off.early_exit
            and type break = Features.Off.break) : sig
  include module type of struct
    module FA = F

    module FB = struct
      include F
      include Features.Off.Loop
      include Features.Off.While_loop
      include Features.Off.For_loop
      include Features.Off.For_index_loop
      include Features.Off.State_passing_loop
    end

    module A = Ast.Make (F)
    module B = Ast.Make (FB)
    module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)
  end

  include ImplemT.T
end
