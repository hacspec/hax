open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.NewtypeAsRefinement

      module A = Ast.Make (F)
      module Visitors = Ast_visitors.Make (F)
      open A

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.MakeBase (Error)

      let visitor =
        object
          inherit [_] Visitors.map as super

          method! visit_expr () e =
            match e.e with
            | App { f = { e = GlobalVar f; _ }; args = [ inner ]; _ }
              when Ast.Global_ident.eq_name Hax_lib__Refinement__new f
                   || Ast.Global_ident.eq_name Hax_lib__RefineAs__into_checked f
                   || Ast.Global_ident.eq_name Hax_lib__Refinement__get f ->
                { e with e = Ascription { typ = e.typ; e = inner } }
            | _ -> super#visit_expr () e

          method! visit_item () i =
            match i.v with
            | Type
                {
                  name;
                  generics;
                  variants = [ { arguments = [ (_, ty, _) ]; _ } ];
                  _;
                }
              when Attrs.find_unique_attr i.attrs
                     ~f:
                       ([%eq: Types.ha_payload] NewtypeAsRefinement
                       >> Fn.flip Option.some_if ())
                   |> Option.is_some ->
                { i with v = TyAlias { name; generics; ty } }
            | _ -> super#visit_item () i
        end

      let ditems = List.map ~f:(visitor#visit_item ())
    end)
