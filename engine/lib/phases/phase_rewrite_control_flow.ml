(* This phase rewrites: `if c {return a}; b` as `if c {return a; b} else {b}`
   and does the equivalent transformation for pattern matchings.
   It rewrites the body of loops considereing `break` and `continue`
   as `return` to place them in return position. If a loop contains
   a `return` it places it is rewritten inside a pattern matching over the result. *)

open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.RewriteControlFlow

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module M = Ast_builder.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let has_return =
        object (_self)
          inherit [_] Visitors.reduce as super
          method zero = false
          method plus = ( || )

          method! visit_expr' in_loop e =
            match e with
            | Return _ -> true
            | (Break _ | Continue _) when in_loop -> true
            | _ -> super#visit_expr' in_loop e
        end

      let loop_has_cf =
        object (_self)
          inherit [_] Visitors.reduce as super
          method zero = false
          method plus = ( || )

          method! visit_expr' () e =
            match e with
            | Return _ | Break _ | Continue _ -> true
            | Loop _ -> false
            | _ -> super#visit_expr' () e
        end

      let rewrite_control_flow =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr in_loop e =
            let loop_with_return (loop : expr) stmts_after final pat =
              let typ = loop.typ in
              let span = loop.span in
              (* wrong, we would need to propagate the return type (either by looking at the
                 return statements (and the type of the expression they contain) or at the return type of the function) *)
              let id = U.fresh_local_ident_in [] "ret" in
              let module MS = (val U.M.make span) in
              let mk_cf_pat = U.make_control_flow_pat ~span ~typ in
              let arms =
                [
                  MS.arm
                    (mk_cf_pat `Break (U.make_var_pat id typ span))
                    (MS.expr_LocalVar ~typ id);
                  MS.arm
                    (MS.pat_POr ~subpats:[ mk_cf_pat `Continue pat ] ~typ)
                    (U.make_lets stmts_after final);
                ]
              in
              MS.expr_Match ~scrutinee:loop ~arms ~typ
            in
            match e.e with
            (* This is supposed to improve performance but it might actually make it worse in some cases *)
            | _ when not (has_return#visit_expr true e) -> e
            | Loop loop ->
                let return_inside = has_return#visit_expr false loop.body in
                let control_flow =
                  return_inside || loop_has_cf#visit_expr () loop.body
                in
                let loop_expr =
                  {
                    e with
                    e =
                      Loop
                        {
                          loop with
                          body = self#visit_expr true loop.body;
                          control_flow;
                        };
                  }
                in
                if return_inside then
                  let id = U.fresh_local_ident_in [] "loop_res" in
                  let pat = U.make_var_pat id loop_expr.typ loop_expr.span in
                  let module MS = (val U.M.make loop_expr.span) in
                  let final = MS.expr_LocalVar ~typ:loop_expr.typ id in
                  loop_with_return loop_expr [] final pat
                else loop_expr
            | Let _ -> (
                (* Collect let bindings to get the sequence
                   of "statements", find the first "statement" that is a
                   control flow containing a return. Rewrite it.
                *)
                let stmts, final = U.collect_let_bindings e in
                let inline_in_branch branch p stmts_after final =
                  let branch_stmts, branch_final =
                    U.collect_let_bindings branch
                  in
                  let stmts_to_add =
                    match (p, branch_final) with
                    (* This avoids adding `let _ = ()` *)
                    | { p = PWild; _ }, { e = GlobalVar (`TupleCons 0); _ } ->
                        stmts_after
                    | stmt -> stmt :: stmts_after
                  in
                  U.make_lets (branch_stmts @ stmts_to_add) final
                in
                let stmts_before, stmt_and_stmts_after =
                  List.split_while stmts ~f:(fun (_, e) ->
                      match e.e with
                      | (If _ | Match _) when has_return#visit_expr in_loop e ->
                          false
                      | Loop _ when has_return#visit_expr false e -> false
                      | Return _ | Break _ | Continue _ -> false
                      | _ -> true)
                in
                match stmt_and_stmts_after with
                | (p, ({ e = Loop loop; _ } as rhs)) :: stmts_after ->
                    let loop_expr =
                      {
                        rhs with
                        e =
                          Loop
                            {
                              loop with
                              control_flow = true;
                              body = self#visit_expr true loop.body;
                            };
                      }
                    in
                    U.make_lets stmts_before
                      (loop_with_return loop_expr stmts_after final p)
                | (p, ({ e = If { cond; then_; else_ }; _ } as rhs))
                  :: stmts_after ->
                    (* We know there is no "return" in the condition
                       so we must rewrite the if *)
                    let then_ = inline_in_branch then_ p stmts_after final in
                    let else_ =
                      Some
                        (match else_ with
                        | Some else_ ->
                            inline_in_branch else_ p stmts_after final
                        | None -> U.make_lets stmts_after final)
                    in
                    U.make_lets stmts_before
                      { rhs with e = If { cond; then_; else_ } }
                    |> self#visit_expr in_loop
                | (p, ({ e = Match { scrutinee; arms }; _ } as rhs))
                  :: stmts_after ->
                    let arms =
                      List.map arms ~f:(fun arm ->
                          let body =
                            inline_in_branch arm.arm.body p stmts_after final
                          in
                          { arm with arm = { arm.arm with body } })
                    in
                    U.make_lets stmts_before
                      { rhs with e = Match { scrutinee; arms } }
                    |> self#visit_expr in_loop
                (* The statements coming after a "return" are useless. *)
                | (_, ({ e = Return _ | Break _ | Continue _; _ } as rhs)) :: _
                  ->
                    U.make_lets stmts_before rhs |> self#visit_expr in_loop
                | _ ->
                    let stmts =
                      List.map stmts ~f:(fun (p, e) ->
                          (p, self#visit_expr in_loop e))
                    in
                    U.make_lets stmts (self#visit_expr in_loop final))
            | _ -> super#visit_expr in_loop e
        end

      let ditems = List.map ~f:(rewrite_control_flow#visit_item false)
    end)
