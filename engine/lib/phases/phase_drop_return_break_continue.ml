(* This phase removes `return`s in exit position. Inside loops,
   it replaces `return`, `break` and `continue` (in exit position)
   by their encoding in the `ControlFlow` enum. It replaces another
   expression in exit position by an equivalent `continue`.
   This phase should comae after `RewriteControlFlow` to ensure all
   control flow is in exit position. *)

open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.DropNeedlessReturns

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      type loop_info = { return_type : ty option; break_type : ty }

      let has_return =
        object (_self)
          inherit [_] Visitors.reduce as super
          method zero = { return_type = None; break_type = U.unit_typ }

          method plus li1 li2 =
            {
              return_type =
                (match (li1.return_type, li2.return_type) with
                | Some t, _ | _, Some t -> Some t
                | _ -> None);
              break_type =
                (if [%eq: ty] li1.break_type U.unit_typ then li2.break_type
                else li1.break_type);
            }

          method! visit_expr' () e =
            match e with
            | Return { e; _ } ->
                { return_type = Some e.typ; break_type = U.unit_typ }
            | Break { e; _ } -> { return_type = None; break_type = e.typ }
            | _ -> super#visit_expr' () e
        end

      let visitor =
        object (self)
          inherit [_] Visitors.map as _super

          method! visit_expr (in_loop : (loop_info * ty) option) e =
            match (e, in_loop) with
            | { e = Return { e; _ }; _ }, None -> e
            (* we know [e] is on an exit position: the return is
               thus useless, we can skip it *)
            | { e = Let { monadic = None; lhs; rhs; body }; _ }, _ ->
                let body = self#visit_expr in_loop body in
                {
                  e with
                  e = Let { monadic = None; lhs; rhs; body };
                  typ = body.typ;
                }
                (* If a let expression is an exit node, then it's body
                   is as well *)
            | { e = Match { scrutinee; arms }; _ }, _ ->
                let arms = List.map ~f:(self#visit_arm in_loop) arms in
                let typ =
                  match arms with
                  | { arm; _ } :: _ -> arm.body.typ
                  | [] -> e.typ
                in
                { e with e = Match { scrutinee; arms }; typ }
            | { e = If { cond; then_; else_ }; _ }, _ ->
                let then_ = self#visit_expr in_loop then_ in
                let else_ = Option.map ~f:(self#visit_expr in_loop) else_ in
                { e with e = If { cond; then_; else_ }; typ = then_.typ }
            | ( { e = Return { e; _ }; span; _ },
                Some ({ return_type; break_type }, acc_type) ) ->
                U.make_control_flow_expr ~return_type ~span ~break_type ~e
                  ~acc:{ e with typ = acc_type } `Return
            | ( { e = Break { e; acc = Some (_, acc); _ }; span; _ },
                Some ({ return_type; break_type }, _) ) ->
                U.make_control_flow_expr ~return_type ~span ~break_type ~e ~acc
                  `Break
            | ( { e = Continue { acc = Some (_, acc); _ }; span; _ },
                Some ({ return_type; break_type }, _) ) ->
                U.make_control_flow_expr ~return_type ~span ~break_type ~acc
                  `Continue
            | { span; _ }, Some ({ return_type; break_type }, _) ->
                U.make_control_flow_expr ~return_type ~span ~break_type ~acc:e
                  `Continue
            | _ -> e
          (** The invariant here is that [visit_expr] is called only
              on expressions that are on exit positions. [visit_expr]
              is first called on root expressions, which are (by
              definition) exit nodes. Then, [visit_expr] itself makes
              recursive calls to sub expressions that are themselves
              in exit nodes. **)
        end

      let loop_visitor =
        object (_self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e.e with
            | Loop ({ body; control_flow; _ } as loop) when control_flow ->
                let body =
                  visitor#visit_expr
                    (Some (has_return#visit_expr () body, e.typ))
                    body
                in
                super#visit_expr () { e with e = Loop { loop with body } }
            | _ -> super#visit_expr () e
        end

      let ditems =
        List.map ~f:(visitor#visit_item None >> loop_visitor#visit_item ())
    end)
