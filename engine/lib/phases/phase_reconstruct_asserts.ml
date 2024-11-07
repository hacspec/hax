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

      let reconstruct_assert =
        object (self)
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            let extract_block e =
              let* { e; _ } = U.D.expr_Block e in
              let* { f; args; _ } = U.D.expr_App e in
              let* nta = U.D.expr_GlobalVar f in
              match args with
              | [ { e = App { f = { e = GlobalVar panic; _ }; _ }; _ } ] ->
                  Some (nta, panic)
              | _ -> None
            in
            let extract_app e =
              let* { f; args; _ } = U.D.expr_App e in
              let* nta = U.D.expr_GlobalVar f in
              let* arg = U.D.list_1 args in
              let* { body; _ } = U.D.expr_Let arg in
              let* { e; _ } = U.D.expr_Block body in
              let* { f; _ } = U.D.expr_App e in
              let* panic = U.D.expr_GlobalVar f in
              Some (nta, panic)
            in
            let extract e =
              let* { cond; then_; _ } = U.D.expr_If e in
              let* nta, panic =
                extract_app then_ <|> fun _ -> extract_block then_
              in
              Some (panic, nta, cond)
            in
            match extract e with
            | Some (panic, nta, cond)
              when Ast.Global_ident.eq_name Rust_primitives__hax__never_to_any
                     nta
                   && (Ast.Global_ident.eq_name Core__panicking__panic panic
                      || Ast.Global_ident.eq_name Core__panicking__assert_failed
                           panic) ->
                let cond_expr = self#visit_expr () cond in

                let prop =
                  match cond_expr.e with
                  (* assert! and assert_eq! *)
                  | App { f = { e = GlobalVar fnot; _ }; args = [ prop ]; _ }
                    when Ast.Global_ident.eq_name Core__ops__bit__Not__not fnot
                    ->
                      prop
                  (* assert_ne! *)
                  | _ ->
                      {
                        cond_expr with
                        e =
                          App
                            {
                              f =
                                {
                                  e =
                                    GlobalVar
                                      (Ast.Global_ident.of_name Value
                                         Core__ops__bit__Not__not);
                                  span = cond_expr.span;
                                  typ = TArrow ([ TBool ], TBool);
                                };
                              args = [ cond_expr ];
                              generic_args = [];
                              bounds_impls = [];
                              trait = None;
                            };
                      }
                in

                {
                  e with
                  e =
                    App
                      {
                        f =
                          {
                            e =
                              GlobalVar
                                (Ast.Global_ident.of_name Value Hax_lib__assert);
                            span = e.span;
                            typ =
                              TArrow
                                ( [ TBool ],
                                  TApp { ident = `TupleType 0; args = [] } );
                          };
                        args = [ prop ];
                        generic_args = [];
                        bounds_impls = [];
                        trait = None;
                      };
                }
            | _ -> super#visit_expr () e
        end

      let ditems = List.map ~f:(reconstruct_assert#visit_item ())
    end)
