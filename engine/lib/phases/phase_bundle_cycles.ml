open! Prelude

module Make (F : Features.T) =
  Phase_utils.MakeMonomorphicPhase
    (F)
    (struct
      let phase_id = [%auto_phase_name auto]

      module A = Ast.Make (F)

      module Error = Phase_utils.MakeError (struct
        let ctx = Diagnostics.Context.Phase phase_id
      end)

      module Attrs = Attr_payloads.MakeBase (Error)

      let ditems items =
        let module DepGraph = Dependencies.Make (F) in
        DepGraph.bundle_cyclic_modules items
    end)
