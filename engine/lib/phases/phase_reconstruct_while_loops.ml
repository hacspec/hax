open! Prelude

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.On.While_loop
  end

  include
    Phase_utils.MakeBase (FA) (FB)
      (struct
        let phase_id = [%auto_phase_name auto]
      end)

  module Implem : ImplemT.T = struct
    let metadata = metadata

    module UA = Ast_utils.Make (FA)
    module UB = Ast_utils.Make (FB)

    module S = struct
      include Features.SUBTYPE.Id
      include Features.SUBTYPE.On.While_loop
    end

    module While = struct
      [@@@warning "-9"]

      open A

      type t = {
        condition : expr;
        body : expr;
        state : loop_state option;
        label : string option;
        witness : FA.loop;
      }
      [@@deriving show]

      let expect_never_to_any (e : expr) : expr option =
        match e.e with
        | App { f = { e = GlobalVar f }; args = [ x ]; _ }
          when Global_ident.eq_name Rust_primitives__hax__never_to_any f ->
            Some x
        | _ -> None

      let expect_break_unit (e : expr) : unit option =
        match e.e with
        | Break { e = { e = GlobalVar (`TupleCons 0) } } -> Some ()
        | _ -> None

      let strip_block (e : expr) : expr =
        match e.e with Block { e; safety_mode = Safe; _ } -> e | _ -> e

      let expect_ite (e : expr) : (expr * expr * expr option) option =
        match e.e with
        | If { cond; then_; else_ } -> Some (cond, then_, else_)
        | _ -> None

      let extract (e : expr) : t option =
        let e = UA.Mappers.normalize_borrow_mut#visit_expr () e in
        match e.e with
        | Loop { label; kind = UnconditionalLoop; state; witness; body; _ } ->
            let body = strip_block body in
            let* condition, body, else_ = expect_ite body in
            let* else_ = else_ in
            let else_ = strip_block else_ in
            let* else_ = expect_never_to_any else_ in
            let else_ = strip_block else_ in
            let* else_ = expect_never_to_any else_ in
            let* _ = expect_break_unit else_ in
            Some { condition; body; state; label; witness }
        | _ -> None
    end

    [%%inline_defs dmutability + dsafety_kind]

    let rec dexpr_unwrapped (expr : A.expr) : B.expr =
      let h = [%inline_body dexpr_unwrapped] in
      match While.extract expr with
      | Some { condition; body; state; label; witness } ->
          {
            e =
              Loop
                {
                  body = dexpr body;
                  kind =
                    WhileLoop
                      {
                        condition = dexpr condition;
                        witness = Features.On.while_loop;
                      };
                  state = Option.map ~f:(dloop_state expr.span) state;
                  label;
                  witness = S.loop expr.span witness;
                  control_flow = None;
                };
            span = expr.span;
            typ = UB.unit_typ;
          }
      | None -> h expr
    [@@inline_ands bindings_of dexpr]

    [%%inline_defs "Item.*"]
  end

  include Implem
  module FA = FA
end
[@@add "subtype.ml"]
