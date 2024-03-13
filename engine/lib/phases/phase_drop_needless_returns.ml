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

      let visitor =
        object (self)
          inherit [_] Visitors.map as _super

          method! visit_expr () e =
            match e with
            | { e = Return { e; _ }; _ } -> e
            (* we know [e] is on an exit position: the return is
               thus useless, we can skip it *)
            | { e = Let { monadic = None; lhs; rhs; body }; _ } ->
                let body = self#visit_expr () body in
                { e with e = Let { monadic = None; lhs; rhs; body } }
                (* If a let expression is an exit node, then it's body
                   is as well *)
            | { e = Match { scrutinee; arms }; _ } ->
                let arms = List.map ~f:(self#visit_arm ()) arms in
                { e with e = Match { scrutinee; arms } }
            | { e = If { cond; then_; else_ }; _ } ->
                let then_ = self#visit_expr () then_ in
                let else_ = Option.map ~f:(self#visit_expr ()) else_ in
                { e with e = If { cond; then_; else_ } }
            | _ -> e
          (** The invariant here is that [visit_expr] is called only
              on expressions that are on exit positions. [visit_expr]
              is first called on root expressions, which are (by
              definition) exit nodes. Then, [visit_expr] itself makes
              recursive calls to sub expressions that are themselves
              in exit nodes. **)
        end

      let ditems = List.map ~f:(visitor#visit_item ())
    end)
