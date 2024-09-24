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
            (* Returns in loops will be handled by issue #196 *)
            | Loop _ -> e
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
                  U.make_lets
                    (branch_stmts @ ((p, branch_final) :: stmts_after))
                    final
                in
                match
                  List.split_while stmts ~f:(fun (_, e) ->
                      match e.e with
                      | (If _ | Match _) when has_return#visit_expr () e ->
                          false
                      | Return _ -> false
                      | _ -> true)
                with
                | ( stmts_before,
                    (p, ({ e = If { cond; then_; else_ }; _ } as rhs))
                    :: stmts_after ) ->
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
                    |> self#visit_expr ()
                | ( stmts_before,
                    (p, ({ e = Match { scrutinee; arms }; _ } as rhs))
                    :: stmts_after ) ->
                    let arms =
                      List.map arms ~f:(fun arm ->
                          let body =
                            inline_in_branch arm.arm.body p stmts_after final
                          in
                          { arm with arm = { arm.arm with body } })
                    in
                    U.make_lets stmts_before
                      { rhs with e = Match { scrutinee; arms } }
                    |> self#visit_expr ()
                (* The statements coming after a "return" are useless. *)
                | stmts_before, (_, ({ e = Return _; _ } as rhs)) :: _ ->
                    U.make_lets stmts_before rhs |> self#visit_expr ()
                | _ ->
                    let stmts =
                      List.map stmts ~f:(fun (p, e) ->
                          (p, self#visit_expr () e))
                    in
                    U.make_lets stmts (self#visit_expr () final))
            | _ -> super#visit_expr () e
        end

      let ditems = List.map ~f:(rewrite_control_flow#visit_item ())
    end)
