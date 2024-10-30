(* This phase transforms deep disjunctive patterns in equivalent
   shallow ones. For example `Some(1 | 2)` becomes `Some(1) | Some(2)` *)

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

      let hoist_disjunctions =
        object (self)
          inherit [_] Visitors.map

          method! visit_pat () p =
            let return_pat p' = { p = p'; span = p.span; typ = p.typ } in

            (* When there is a list of subpaterns, we use the distributivity of nested
               disjunctions: (a | b, c | d) gives (a, c) | (a, d) | (b, c) | (b,d) *)
            let rec treat_args cases = function
              | { p = POr { subpats }; _ } :: tail ->
                  treat_args
                    (List.concat_map
                       ~f:(fun subpat ->
                         List.map ~f:(fun args -> subpat :: args) cases)
                       subpats)
                    tail
              | pat :: tail ->
                  let pat = self#visit_pat () pat in
                  treat_args (List.map ~f:(fun args -> pat :: args) cases) tail
              | [] -> cases
            in
            let subpats_to_disj subpats =
              match subpats with
              | [ pat ] -> pat
              | _ -> POr { subpats } |> return_pat
            in

            (* When there is one subpattern, we check if it is a disjunction,
               and if it is, we hoist it. *)
            let treat_subpat pat to_pattern =
              let subpat = self#visit_pat () pat in
              match subpat with
              | { p = POr { subpats }; span; _ } ->
                  return_pat
                    (POr
                       {
                         subpats =
                           List.map
                             ~f:(fun pat ->
                               { p = to_pattern pat; span; typ = p.typ })
                             subpats;
                       })
              | _ -> p
            in

            match p.p with
            | PConstruct { constructor; fields; is_record; is_struct } ->
                let fields_as_pat =
                  List.rev_map fields ~f:(fun arg -> self#visit_pat () arg.pat)
                in
                let subpats =
                  List.map (treat_args [ [] ] fields_as_pat)
                    ~f:(fun fields_as_pat ->
                      let fields =
                        List.map2_exn fields_as_pat fields
                          ~f:(fun pat { field; _ } -> { field; pat })
                      in
                      PConstruct { constructor; fields; is_record; is_struct }
                      |> return_pat)
                in

                subpats_to_disj subpats
            | PArray { args } ->
                let subpats =
                  List.map
                    ~f:(fun args -> PArray { args } |> return_pat)
                    (treat_args [ [] ]
                       (List.rev_map args ~f:(fun arg -> self#visit_pat () arg)))
                in
                subpats_to_disj subpats
            | POr { subpats } ->
                let subpats = List.map ~f:(self#visit_pat ()) subpats in
                POr
                  {
                    subpats =
                      List.concat_map
                        ~f:(function
                          | { p = POr { subpats }; _ } -> subpats | p -> [ p ])
                        subpats;
                  }
                |> return_pat
            | PAscription { typ; typ_span; pat } ->
                treat_subpat pat (fun pat -> PAscription { typ; typ_span; pat })
            | PBinding { subpat = Some (pat, as_pat); mut; mode; typ; var } ->
                treat_subpat pat (fun pat ->
                    PBinding
                      { subpat = Some (pat, as_pat); mut; mode; typ; var })
            | PDeref { subpat; witness } ->
                treat_subpat subpat (fun subpat -> PDeref { subpat; witness })
            | PWild | PConstant _ | PBinding { subpat = None; _ } -> p
        end

      let ditems = List.map ~f:(hoist_disjunctions#visit_item ())
    end)
