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

      let reject_anon_assoc_ty =
        object
          inherit [_] Visitors.map as super

          method! visit_ty span t =
            match t with
            | TAssociatedType { item; _ }
              when Concrete_ident.is_anon_assoc_ty item ->
                Error.unimplemented ~issue_id:1965
                  ~details:
                    "`impl` types are not supported in type signatures of \
                     associated items."
                  (Option.value_exn span)
            | _ -> super#visit_ty span t

          method! visit_item _ i =
            try super#visit_item (Some i.span) i
            with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
              let error = Diagnostics.pretty_print_context_kind context kind in
              make_hax_error_item i.span i.ident error
        end

      let ditems = List.map ~f:(reject_anon_assoc_ty#visit_item None)
    end)
