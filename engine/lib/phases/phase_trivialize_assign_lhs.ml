open! Prelude

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

    let rec updater_of_lhs (lhs : A.lhs) (rhs : B.expr) (span : span) :
        (Local_ident.t * B.ty) * B.expr =
      match lhs with
      | LhsLocalVar { var; typ } -> ((var, dty span typ), rhs)
      | LhsFieldAccessor { e; field; _ } -> (
          let lhs = UA.expr_of_lhs span e |> dexpr in
          match lhs.typ with
          | TApp { ident; _ } ->
              let rhs' =
                B.Construct
                  {
                    constructor = ident;
                    is_record = true (* TODO: might not be, actually *);
                    is_struct = true;
                    fields = [ (field, rhs) ];
                    base = Some (lhs, Features.On.construct_base);
                  }
              in
              let rhs = { B.e = rhs'; typ = lhs.typ; span } in
              updater_of_lhs e rhs span
          | _ -> Error.raise { kind = ArbitraryLHS; span })
      | LhsArrayAccessor { e; typ = _; index; _ } ->
          let lhs = UA.expr_of_lhs span e |> dexpr in
          let rhs =
            UB.call Rust_primitives__hax__update_at
              [ lhs; dexpr index; rhs ]
              span lhs.typ
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
