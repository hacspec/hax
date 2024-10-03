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

      let has_return =
        object (_self)
          inherit [_] Visitors.reduce as super
          method zero = false
          method plus = ( || )

          method! visit_expr' () e =
            match e with Return _ -> true | _ -> super#visit_expr' () e
        end

      let visitor =
        object (self)
          inherit [_] Visitors.map as _super

          method! visit_expr (in_loop : bool option) e =
            match (e, in_loop) with
            | { e = Return { e; _ }; _ }, None -> e
            (* we know [e] is on an exit position: the return is
               thus useless, we can skip it *)
            | { e = Let { monadic = None; lhs; rhs; body }; _ }, _ ->
                let body = self#visit_expr in_loop body in
                { e with e = Let { monadic = None; lhs; rhs; body } }
                (* If a let expression is an exit node, then it's body
                   is as well *)
            | { e = Match { scrutinee; arms }; _ }, _ ->
                let arms = List.map ~f:(self#visit_arm in_loop) arms in
                { e with e = Match { scrutinee; arms } }
            | { e = If { cond; then_; else_ }; _ }, _ ->
                let then_ = self#visit_expr in_loop then_ in
                let else_ = Option.map ~f:(self#visit_expr in_loop) else_ in
                { e with e = If { cond; then_; else_ } }
            | { e = Return { e; _ }; span; typ }, Some has_return ->
                U.make_control_flow_expr ~has_return ~span ~typ `Return e
            | { e = Break { e; _ }; span; typ }, Some has_return ->
                U.make_control_flow_expr ~has_return ~span ~typ `Break e
            | ( { e = Continue { e = Some (_, e); _ }; span; typ },
                Some has_return ) ->
                U.make_control_flow_expr ~has_return ~span ~typ `Continue e
            | { span; typ; _ }, Some has_return ->
                U.make_control_flow_expr ~has_return ~span ~typ `Continue e
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
                  visitor#visit_expr (Some (has_return#visit_expr () body)) body
                in
                super#visit_expr () { e with e = Loop { loop with body } }
            | _ -> super#visit_expr () e
        end

      let ditems =
        List.map ~f:(visitor#visit_item None >> loop_visitor#visit_item ())
    end)
