(* This phase rewrites: `if c {return a}; b` as `if c {return a; b} else {b}`
   and does the equivalent transformation for pattern matchings. *)

open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.RewriteControlFlow

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

      let rewrite_control_flow =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e.e with
            | _ when not (has_return#visit_expr () e) -> e
            | Let
                {
                  monadic = None;
                  lhs;
                  rhs = { e = If { cond; then_; else_ }; _ } as rhs;
                  body;
                } ->
                let cond = self#visit_expr () cond in
                let then_has_return = has_return#visit_expr () then_ in
                let else_has_return =
                  Option.map else_ ~f:(has_return#visit_expr ())
                  |> Option.value ~default:false
                in
                let rewrite = then_has_return || else_has_return in
                if rewrite then
                  let then_ =
                    {
                      e with
                      e = Let { monadic = None; lhs; rhs = then_; body };
                    }
                  in
                  let then_ = self#visit_expr () then_ in
                  let else_ =
                    Some
                      (match else_ with
                      | Some else_ ->
                          self#visit_expr ()
                            {
                              e with
                              e = Let { monadic = None; lhs; rhs = else_; body };
                            }
                      | None -> body)
                  in

                  { rhs with e = If { cond; then_; else_ } }
                else
                  let body = self#visit_expr () body in
                  {
                    e with
                    e =
                      Let
                        {
                          monadic = None;
                          lhs;
                          rhs = { rhs with e = If { cond; then_; else_ } };
                          body;
                        };
                  }
            (* We need this case to make sure we take the `if` all the way up a sequence of nested `let`
               and not just one level. *)
            | Let { monadic = None; lhs; rhs = { e = Let _; _ } as rhs; body }
              -> (
                let body = self#visit_expr () body in
                match self#visit_expr () rhs with
                | { e = If { cond; then_; else_ = Some else_ }; _ } ->
                    (* In this case we know we already rewrote the rhs so we should take the `if` one level higher. *)
                    let rewrite_branch branch =
                      {
                        branch with
                        e = Let { monadic = None; lhs; rhs = branch; body };
                      }
                    in
                    {
                      rhs with
                      e =
                        If
                          {
                            cond;
                            then_ = rewrite_branch then_;
                            else_ = Some (rewrite_branch else_);
                          };
                    }
                | rhs -> { e with e = Let { monadic = None; lhs; rhs; body } })
            | Let
                {
                  monadic = None;
                  lhs;
                  rhs = { e = Match { scrutinee; arms }; _ };
                  body;
                } ->
                let rewrite =
                  List.fold arms ~init:false ~f:(fun acc (arm : arm) ->
                      acc || has_return#visit_arm () arm)
                in
                if rewrite then
                  {
                    e with
                    e =
                      Match
                        {
                          scrutinee = self#visit_expr () scrutinee;
                          arms =
                            List.map arms ~f:(fun arm ->
                                let arm_body = arm.arm.body in
                                let arm_body =
                                  {
                                    arm_body with
                                    e =
                                      Let
                                        {
                                          monadic = None;
                                          lhs;
                                          rhs = arm_body;
                                          body;
                                        };
                                  }
                                in
                                self#visit_arm ()
                                  {
                                    arm with
                                    arm = { arm.arm with body = arm_body };
                                  });
                        };
                  }
                else e
            | _ -> super#visit_expr () e
        end

      (* This visitor allows to remove instructions after a `return` so that `drop_needless_return` can simplify them. *)
      let remove_after_return =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e.e with
            | Let { monadic = None; lhs; rhs; body } -> (
                let rhs = self#visit_expr () rhs in
                let body = self#visit_expr () body in
                match rhs.e with
                | Return _ -> rhs
                | _ -> { e with e = Let { monadic = None; lhs; rhs; body } })
            | _ -> super#visit_expr () e
        end

      let ditems =
        List.map
          ~f:
            (rewrite_control_flow#visit_item ()
            >> remove_after_return#visit_item ())
    end)
