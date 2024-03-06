open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.DummyA

      module A = Ast.Make (F)
      module FB = F
      module B = Ast.Make (F)
      module U = Ast_utils.Make (F)
      module BVisitors = Ast_visitors.Make (F)
      open A

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let mk_name ident (kind : string) =
        Concrete_ident.Create.map_last ~f:(fun s -> s ^ "_" ^ kind) ident

      module Attrs = Attr_payloads.Make (F) (Error)

      let ditems (l : A.item list) : B.item list =
        let (module Attrs) = Attrs.with_items l in
        let f (item : item) : item =
          let v =
            match item.v with
            | Trait { name; generics; items } ->
                let f (item : trait_item) =
                  let mk kind =
                    let ti_ident = mk_name item.ti_ident kind in
                    {
                      item with
                      ti_ident;
                      ti_attrs =
                        [
                          Attr_payloads.to_attr TraitMethodNoPrePost
                            item.ti_span;
                        ];
                    }
                  in
                  match item.ti_v with
                  | TIFn (TArrow (inputs, output)) ->
                      [
                        { (mk "pre") with ti_v = TIFn (TArrow (inputs, TBool)) };
                        {
                          (mk "post") with
                          ti_v = TIFn (TArrow (inputs @ [ output ], TBool));
                        };
                      ]
                  | TIFn _ -> [ (* REFINEMENTS FOR CONSTANTS? *) ]
                  | TIType _ -> [ (* TODO REFINEMENTS FOR TYPES *) ]
                in
                let items =
                  List.concat_map ~f:(fun item -> f item @ [ item ]) items
                in
                Trait { name; generics; items }
            | Impl { generics; self_ty; of_trait; items; parent_bounds } ->
                let f (item : impl_item) =
                  let mk kind =
                    let ii_ident = mk_name item.ii_ident kind in
                    { item with ii_ident }
                  in
                  let default =
                    {
                      e = Literal (Bool true);
                      span = item.ii_span;
                      typ = TBool;
                    }
                  in
                  match item.ii_v with
                  | IIFn { params = []; _ } -> []
                  | IIFn { body; params } ->
                      let out_ident =
                        U.fresh_local_ident_in
                          (U.Reducers.collect_local_idents#visit_impl_item ()
                             item
                          |> Set.to_list)
                          "out"
                      in
                      let params_pat =
                        List.map ~f:(fun param -> param.pat) params
                      in
                      let pat = U.make_var_pat out_ident body.typ body.span in
                      let typ = body.typ in
                      let out = { pat; typ; typ_span = None; attrs = [] } in
                      [
                        {
                          (mk "pre") with
                          ii_v =
                            IIFn
                              {
                                body =
                                  Attrs.associated_expr_rebinding params_pat
                                    Requires item.ii_attrs
                                  |> Option.value ~default;
                                params;
                              };
                        };
                        {
                          (mk "post") with
                          ii_v =
                            IIFn
                              {
                                body =
                                  Attrs.associated_expr_rebinding
                                    (params_pat @ [ pat ]) Ensures item.ii_attrs
                                  |> Option.value ~default;
                                params = params @ [ out ];
                              };
                        };
                      ]
                  | IIType _ -> []
                in
                let items =
                  List.concat_map ~f:(fun item -> f item @ [ item ]) items
                in
                Impl { generics; self_ty; of_trait; items; parent_bounds }
            | v -> v
          in
          { item with v }
        in
        List.map ~f l
    end)
