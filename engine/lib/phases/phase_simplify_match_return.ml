open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.SimplifyMatchReturn

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let inline_matches =
        object
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e with
            | {
             e =
               Let
                 {
                   monadic = None;
                   lhs;
                   rhs =
                     {
                       e =
                         Match
                           {
                             scrutinee;
                             arms =
                               [
                                 arm;
                                 ({
                                    arm =
                                      {
                                        body =
                                          {
                                            e = Return _ as return;
                                            span = return_span;
                                            _;
                                          };
                                        _;
                                      };
                                    _;
                                  } as diverging_arm);
                               ];
                           };
                       _;
                     } as match_expr;
                   body;
                 };
             _;
            } ->
                let arm_body = arm.arm.body in
                let arm_pat = arm.arm.arm_pat in
                let arm_pat, let_expr =
                  ((* if the match produces only a variable *)
                   let* var =
                     match arm_body.e with LocalVar v -> Some v | _ -> None
                   in
                   let found = ref false in
                   let arm_pat =
                     (object
                        inherit [_] Visitors.map as super

                        method! visit_pat () p =
                          match p.p with
                          | PBinding b when [%eq: Local_ident.t] b.var var ->
                              found := true;
                              lhs
                          | _ -> super#visit_pat () p
                     end)
                       #visit_pat
                       () arm_pat
                   in
                   let*? _ = !found in
                   Some (arm_pat, body))
                  |> Option.value
                       ~default:
                         ( arm_pat,
                           {
                             e with
                             e =
                               Let { monadic = None; lhs; rhs = arm_body; body };
                           } )
                in
                let guard = arm.arm.guard in
                let arm = { arm with arm = { arm_pat; body = let_expr; guard = guard } } in
                let diverging_arm =
                  {
                    diverging_arm with
                    arm =
                      {
                        diverging_arm.arm with
                        body = { e = return; span = return_span; typ = e.typ };
                      };
                  }
                in
                let result =
                  let e' = Match { scrutinee; arms = [ arm; diverging_arm ] } in
                  let span = match_expr.span in
                  { span; typ = e.typ; e = e' }
                in
                super#visit_expr () result
            | _ -> super#visit_expr () e
        end

      let ditems = List.map ~f:(inline_matches#visit_item ())
    end)
