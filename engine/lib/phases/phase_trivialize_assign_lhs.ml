open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
    include Features.Off.Nontrivial_lhs
    include Features.On.Construct_base
  end

  include
    Phase_utils.MakeBase (F) (FB)
      (struct
        let phase_id = Diagnostics.Phase.TrivializeAssignLhs
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module S = struct
      include Features.SUBTYPE.Id

      let construct_base _ = Features.On.construct_base
    end

    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)

    [%%inline_defs dmutability]

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
          UB.call Core__ops__index__Index__index
            [ expr_of_lhs e span; dexpr index ]
            span (dty span typ)
      | LhsArbitraryExpr _ -> Error.raise { kind = ArbitraryLHS; span }

    and updater_of_lhs (lhs : A.lhs) (rhs : B.expr) (span : span) :
        (LocalIdent.t * B.ty) * B.expr =
      match lhs with
      | LhsLocalVar { var; typ } -> ((var, dty span typ), rhs)
      | LhsFieldAccessor { e; typ; field; _ } -> (
          let lhs = expr_of_lhs e span in
          let field =
            match field with
            | `Projector field -> (field :> global_ident)
            | _ -> field
          in
          match lhs.typ with
          | TApp { ident; args } ->
              let rhs' =
                B.Construct
                  {
                    constructor = ident;
                    constructs_record = true;
                    fields = [ (field, rhs) ];
                    base = Some (lhs, Features.On.construct_base);
                  }
              in
              let rhs = { B.e = rhs'; typ = lhs.typ; span } in
              updater_of_lhs e rhs span
          | _ -> Error.raise { kind = ArbitraryLHS; span })
      | LhsArrayAccessor { e; typ = _; index; _ } ->
          let lhs = expr_of_lhs e span in
          let rhs =
            UB.call Hax__Array__update_at [ lhs; dexpr index; rhs ] span lhs.typ
          in
          updater_of_lhs e rhs span
      | LhsArbitraryExpr _ -> Error.raise { kind = ArbitraryLHS; span }

    and dexpr_unwrapped (expr : A.expr) : B.expr =
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
      [@@inline_ands bindings_of dexpr - dlhs - dexpr']

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
