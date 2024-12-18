open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      module A = Ast.Make (F)
      module FB = F
      module B = Ast.Make (F)
      module U = Ast_utils.Make (F)
      module BVisitors = Ast_visitors.Make (F)
      open A

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let mk_name ident kind = Concrete_ident.with_suffix kind ident

      module Attrs = Attr_payloads.Make (F) (Error)

      let ditems (l : A.item list) : B.item list =
        let (module Attrs) = Attrs.with_items l in
        let f' (item : item) : item =
          let v =
            match item.v with
            | Trait { name; generics; items; safety } ->
                let f attrs (item : trait_item) =
                  let mk role kind =
                    let ti_ident = mk_name item.ti_ident kind in
                    {
                      item with
                      ti_ident;
                      ti_attrs =
                        [
                          Attr_payloads.to_attr TraitMethodNoPrePost
                            item.ti_span;
                        ]
                        @ (List.filter
                             ~f:
                               [%matches?
                                 Types.AssociatedItem { role = role'; _ }, _ when 
                                 [%eq: Types.ha_assoc_role] role role']
                             attrs
                          |> List.map ~f:(uncurry Attr_payloads.to_attr));
                    }
                  in
                  match item.ti_v with
                  | TIFn (TArrow (inputs, output)) ->
                      [
                        {
                          (mk Types.Requires `Pre) with
                          ti_v = TIFn (TArrow (inputs, TBool));
                        };
                        {
                          (mk Types.Ensures `Post) with
                          ti_v = TIFn (TArrow (inputs @ [ output ], TBool));
                        };
                      ]
                  | TIFn _ -> [ (* REFINEMENTS FOR CONSTANTS? *) ]
                  | TIType _ -> [ (* TODO REFINEMENTS FOR TYPES *) ]
                  | TIDefault _ -> [ (* TODO REFINEMENTS FOR DEFAULT ITEMS *) ]
                in
                let items =
                  List.concat_map
                    ~f:(fun item ->
                      let attrs = Attr_payloads.payloads item.ti_attrs in
                      let ti_attrs =
                        attrs
                        |> List.filter
                             ~f:
                               (fst
                               >> [%matches?
                                    Types.AssociatedItem
                                      { role = Ensures | Requires; _ }]
                               >> not)
                        |> List.map ~f:(uncurry Attr_payloads.to_attr)
                      in
                      f attrs item @ [ { item with ti_attrs } ])
                    items
                in
                Trait { name; generics; items; safety }
            | Impl { generics; self_ty; of_trait; items; parent_bounds; safety }
              ->
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
                      (* We always need to produce a pre and a post
                         condition implementation for each method in
                         the impl. *)
                      [
                        (let params, body =
                           match Attrs.associated_fn Requires item.ii_attrs with
                           | Some (_, params, body) -> (params, body)
                           | None -> (params, default)
                         in
                         { (mk `Pre) with ii_v = IIFn { body; params } });
                        (let params, body =
                           match Attrs.associated_fn Ensures item.ii_attrs with
                           | Some (_, params, body) -> (params, body)
                           | None ->
                               (* There is no explicit post-condition
                                  on this method. We need to define a
                                  trivial one. *)
                               (* Post-condition *always* an extra
                                  argument in final position for the
                                  output. *)
                               let out_ident =
                                 U.fresh_local_ident_in
                                   (U.Reducers.collect_local_idents
                                      #visit_impl_item () item
                                   |> Set.to_list)
                                   "out"
                               in
                               let pat =
                                 U.make_var_pat out_ident body.typ body.span
                               in
                               let typ = body.typ in
                               let out =
                                 { pat; typ; typ_span = None; attrs = [] }
                               in
                               (params @ [ out ], default)
                         in
                         { (mk `Post) with ii_v = IIFn { body; params } });
                      ]
                  | IIType _ -> []
                in
                let items =
                  List.concat_map ~f:(fun item -> f item @ [ item ]) items
                in
                Impl
                  { generics; self_ty; of_trait; items; parent_bounds; safety }
            | v -> v
          in
          { item with v }
        in
        let f item =
          try f' item
          with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
            let error = Diagnostics.pretty_print_context_kind context kind in
            let msg = error in
            B.make_hax_error_item item.span item.ident msg
        in
        List.map ~f l
    end)
