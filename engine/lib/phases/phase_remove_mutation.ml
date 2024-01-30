(* TODO: handle Exn report *)
open! Prelude
open Side_effect_utils

module%inlined_contents Make
    (F : Features.T
           with type mutable_reference = Features.Off.mutable_reference
            and type mutable_pointer = Features.Off.mutable_pointer
            and type raw_pointer = Features.Off.raw_pointer
            and type arbitrary_lhs = Features.Off.arbitrary_lhs
            and type nontrivial_lhs = Features.Off.nontrivial_lhs
            and type monadic_action = Features.Off.monadic_action
            and type monadic_binding = Features.Off.monadic_binding
            and type for_index_loop = Features.Off.for_index_loop
            and type state_passing_loop = Features.On.state_passing_loop) =
struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Mutable_variable
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.RemoveMutation
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
    end

    module SI = MakeSI (FB)

    [%%inline_defs dmutability]

    let rec dpat' (span : span) (p : A.pat') : B.pat' =
      match p with
      | [%inline_arms "dpat'.*" - PBinding - PDeref] -> auto
      | PBinding { var : Local_ident.t; typ; subpat; _ } ->
          PBinding
            {
              mut = Immutable;
              mode = ByValue;
              var;
              typ = dty span typ;
              subpat = Option.map ~f:(dpat *** Fn.id) subpat;
            }
      | PDeref { subpat; _ } -> (dpat subpat).p

    and dexpr_unwrapped e = dexpr e [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
