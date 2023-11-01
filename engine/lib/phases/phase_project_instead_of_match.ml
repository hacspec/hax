open! Prelude

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Project_instead_of_match
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.ProjectInsteadOfMatch
      end)

  module UA = Ast_utils.Make (F)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id
    end

    [%%inline_defs dmutability]

    let rec dexpr' (span : span) (e : A.expr') : B.expr' =
      match (UA.unbox_underef_expr { e; span; typ = UA.never_typ }).e with
      | [%inline_arms "dexpr'.*" - Let - Closure - Loop - Match] -> auto
      | Match { scrutinee; arms } ->
        Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms }
      | Let { monadic; lhs; rhs; body } ->
        Let
          {
            monadic =
              Option.map
                ~f:(dsupported_monads span *** S.monadic_binding)
                monadic;
            lhs = dpat lhs;
            rhs = dexpr rhs;
            body = dexpr body;
          }
      | Loop { body; kind; state; label; witness } ->
        Loop
          {
            body = dexpr body;
            kind = dloop_kind span kind;
            state = Option.map ~f:(dloop_state span) state;
            label;
            witness = S.loop witness;
          }
      | Closure { params; body; captures } ->
        Closure
          {
            params = List.map ~f:dpat params;
            body = dexpr body;
            captures = List.map ~f:dexpr captures;
          }
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]

    (* let rec dty (span : span) (ty : A.ty) : B.ty = *)
    (*   match ty with *)
    (*   | [%inline_arms "dty.*"] -> auto *)

    (* and dgeneric_value (span : span) (generic_value : A.generic_value) : *)
    (*   B.generic_value = *)
    (* match generic_value with *)
    (* | GLifetime { lt; witness } -> *)
    (*     GLifetime { lt; witness = S.lifetime witness } *)
    (* | GType t -> GType (dty span t) *)
    (* | GConst e -> GConst (dexpr e) *)

    (* and dpat' (span : span) (p : A.pat') : B.pat' = *)
    (*   match p with *)
    (*   | [%inline_arms "dpat'.*"] -> auto *)

  end

  include Implem
end
[@@add "subtype.ml"]
