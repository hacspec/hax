open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Block
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module UA = Ast_utils.Make (F)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability + dsafety_kind]

    let rec dexpr' (span : span) (e : A.expr') : B.expr' =
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      | [%inline_arms "dexpr'.*" - Block] -> auto
      | Block { e; _ } -> (dexpr e).e
      [@@inline_ands bindings_of dexpr - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
