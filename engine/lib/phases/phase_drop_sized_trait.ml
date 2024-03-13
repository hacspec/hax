open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = Diagnostics.Phase.DropSizedTrait

      open Ast.Make (F)
      module U = Ast_utils.Make (F)
      module Visitors = Ast_visitors.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      let visitor =
        let keep (ii : impl_ident) =
          Concrete_ident.eq_name Core__marker__Sized ii.goal.trait |> not
        in
        object
          inherit [_] Visitors.map as super

          method! visit_generics () generics =
            let generics = super#visit_generics () generics in
            {
              generics with
              constraints =
                List.filter
                  ~f:(function GCType ii -> keep ii | _ -> true)
                  generics.constraints;
            }

          method! visit_item' () item' =
            let item' = super#visit_item' () item' in
            match item' with
            | Impl payload ->
                Impl
                  {
                    payload with
                    parent_bounds =
                      List.filter ~f:(snd >> keep) payload.parent_bounds;
                  }
            | _ -> item'

          method! visit_trait_item' () ti' =
            let ti' = super#visit_trait_item' () ti' in
            match ti' with
            | TIType impl_idents -> TIType (List.filter ~f:keep impl_idents)
            | _ -> ti'

          method! visit_impl_item' () ii' =
            let ii' = super#visit_impl_item' () ii' in
            match ii' with
            | IIType payload ->
                IIType
                  {
                    payload with
                    parent_bounds =
                      List.filter ~f:(snd >> keep) payload.parent_bounds;
                  }
            | _ -> ii'
        end

      let ditems = List.map ~f:(visitor#visit_item ())
    end)
