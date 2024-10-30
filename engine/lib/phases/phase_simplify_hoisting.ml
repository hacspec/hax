open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let inline_matches =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e with
            | {
             e =
               Let
                 {
                   monadic = None;
                   lhs =
                     {
                       p =
                         PBinding
                           {
                             mut = Immutable;
                             mode = ByValue;
                             var;
                             subpat = None;
                             _;
                           };
                       _;
                     };
                   rhs;
                   body;
                 };
             _;
            }
              when Local_ident.is_side_effect_hoist_var var ->
                let body, count =
                  (object
                     inherit [_] Visitors.mapreduce as super
                     method zero = 0
                     method plus = ( + )

                     method! visit_expr () e =
                       match e.e with
                       | LocalVar v when [%eq: Local_ident.t] v var -> (rhs, 1)
                       | _ -> super#visit_expr () e
                  end)
                    #visit_expr
                    () body
                in
                if [%eq: int] count 1 then self#visit_expr () body
                else super#visit_expr () e
            | _ -> super#visit_expr () e
        end

      let ditems = List.map ~f:(inline_matches#visit_item ())
    end)
