open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Nontrivial_lhs
  end

  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)

  module Implem : ImplemT.T = struct
    include Phase_utils.DefaultError

    module S = struct
      include Features.SUBTYPE.Id
    end

    let metadata = Phase_utils.Metadata.make TrivializeAssignLhs

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    [%%inline_defs dmutability + dty + dborrow_kind + dpat]

    let rec expr_of_lhs (lhs : A.lhs) (span : span) : B.expr =
      match lhs with
      | LhsLocalVar { var; typ } ->
          { e = LocalVar var; typ = dty span typ; span }
      | LhsFieldAccessor { e; typ; field; _ } ->
          let e = expr_of_lhs e span in
          {
            e =
              App
                {
                  f =
                    {
                      e = GlobalVar field;
                      typ = TArrow ([ e.typ ], dty span typ);
                      span;
                    };
                  args = [ e ];
                };
            typ = e.typ;
            span;
          }
      | LhsArrayAccessor { e; typ; index; _ } ->
          UB.call "core" "ops"
            [ "index"; "Index"; "index" ]
            [ expr_of_lhs e span; dexpr index ]
            span (dty span typ)
      | LhsArbitraryExpr _ -> raise @@ Error.E { kind = ArbitraryLHS; span }

    and updater_of_lhs (lhs : A.lhs) (rhs : B.expr) (span : span) :
        (LocalIdent.t * B.ty) * B.expr =
      match lhs with
      | LhsLocalVar { var; typ } -> ((var, dty span typ), rhs)
      | LhsFieldAccessor _ ->
          Diagnostics.failure ~context:DebugPrintRust ~span
            (Unimplemented { issue_id = Some 86; details = None })
      | LhsArrayAccessor { e; typ = _; index; _ } ->
          let lhs = expr_of_lhs e span in
          let rhs =
            UB.call "core" "ops"
              [ "index"; "IndexMut"; "update_at" ]
              [ lhs; dexpr index; rhs ]
              span lhs.typ
          in
          updater_of_lhs e rhs span
      | LhsArbitraryExpr _ -> raise @@ Error.E { kind = ArbitraryLHS; span }

    and dexpr (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | Assign { lhs; e; witness } ->
          let (var, typ), e = updater_of_lhs lhs (dexpr e) expr.span in
          let lhs : B.lhs = LhsLocalVar { var; typ } in
          {
            e = Assign { lhs; e; witness };
            span = expr.span;
            typ = dty expr.span expr.typ;
          }
      | [%inline_arms "dexpr'.*" - Assign] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })

    and dloop_kind = [%inline_body dloop_kind]
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
