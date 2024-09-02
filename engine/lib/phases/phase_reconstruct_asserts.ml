open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.ResugarAsserts

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
            match e with
            | {
             e =
               If
                 {
                   cond;
                   then_ =
                     {
                       e =
                         ( App
                             {
                               f = { e = GlobalVar nta; _ };
                               args =
                                 [
                                   {
                                     e =
                                       Let
                                         {
                                           body =
                                             {
                                               e =
                                                 Block
                                                   ( {
                                                       e =
                                                         App
                                                           {
                                                             f =
                                                               {
                                                                 e =
                                                                   GlobalVar
                                                                     panic;
                                                                 _;
                                                               };
                                                             _;
                                                           };
                                                       _;
                                                     },
                                                     _ );
                                               _;
                                             };
                                           _;
                                         };
                                     _;
                                   };
                                 ];
                               _;
                             }
                         | Block
                             ( {
                                 e =
                                   App
                                     {
                                       f = { e = GlobalVar nta; _ };
                                       args =
                                         [
                                           {
                                             e =
                                               App
                                                 {
                                                   f =
                                                     { e = GlobalVar panic; _ };
                                                   _;
                                                 };
                                             _;
                                           };
                                         ];
                                       _;
                                     };
                                 _;
                               },
                               _ ) );
                       _;
                     };
                   _;
                 };
             _;
            }
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
