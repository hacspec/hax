open Hax_engine
open Base

let read_options_from_stdin (yojson_from_string : string -> Yojson.Safe.t) :
    Types.engine_options =
  In_channel.input_all In_channel.stdin
  |> yojson_from_string |> Types.parse_engine_options

let setup_logs (options : Types.engine_options) =
  let level : Logs.level option =
    match options.backend.verbose with
    | 0 -> None
    | 1 -> Some Info
    | _ -> Some Debug
  in
  Logs.set_level level;
  Logs.set_reporter @@ Logs.format_reporter ()

module Deps = Dependencies.Make (Features.Rust)

module Error : Phase_utils.ERROR = Phase_utils.MakeError (struct
  let ctx = Diagnostics.Context.ThirImport
end)

module Attrs = Attr_payloads.MakeBase (Error)

let import_thir_items (include_clauses : Types.inclusion_clause list)
    (items : Types.item_for__decorated_for__expr_kind list) : Ast.Rust.item list
    =
  let result = List.map ~f:Import_thir.import_item items |> List.map ~f:snd in
  let items = List.concat_map ~f:fst result in
  let ident_to_reports =
    List.concat_map
      ~f:(fun (items, reports) ->
        List.map ~f:(fun (item : Ast.Rust.item) -> (item.ident, reports)) items)
      result
    |> Map.of_alist_exn (module Concrete_ident)
  in
  let items = Deps.filter_by_inclusion_clauses include_clauses items in
  let items =
    List.filter
      ~f:(fun i ->
        match Attrs.status i.attrs with Included _ -> true | _ -> false)
      items
  in
  let items = Deps.sort items in
  let reports =
    List.concat_map
      ~f:(fun (item : Ast.Rust.item) ->
        Map.find_exn ident_to_reports item.ident)
      items
    |> List.dedup_and_sort ~compare:Diagnostics.compare
  in
  List.iter ~f:Diagnostics.Core.report reports;
  items

let run (options : Types.engine_options) : Types.output =
  setup_logs options;
  if options.backend.debug_engine |> Option.is_some then
    Phase_utils.DebugBindPhase.enable ();
  let run (type options_type)
      (module M : Backend.T with type BackendOptions.t = options_type)
      (backend_options : options_type) : Types.file list =
    let open M in
    Concrete_ident.ImplInfoStore.init options.impl_infos;
    let include_clauses =
      options.backend.translation_options.include_namespaces
    in
    let items = import_thir_items include_clauses options.input in
    Logs.info (fun m ->
        m "Applying phase for backend %s"
          ([%show: Diagnostics.Backend.t] M.backend));
    let items = apply_phases backend_options items in
    let with_items = Attrs.with_items items in
    let items =
      List.filter items ~f:(fun (i : AST.item) ->
          Attrs.late_skip i.attrs |> not)
    in
    Logs.info (fun m ->
        m "Translating items with backend %s"
          ([%show: Diagnostics.Backend.t] M.backend));
    let items = translate with_items backend_options items in
    items
  in
  let diagnostics, files =
    Diagnostics.try_ (fun () ->
        match options.backend.backend with
        | Fstar opts -> run (module Fstar_backend) opts
        | Coq -> run (module Coq_backend) ()
        | Easycrypt -> run (module Easycrypt_backend) ())
  in
  {
    diagnostics = List.map ~f:Diagnostics.to_thir_diagnostic diagnostics;
    files = Option.value ~default:[] files;
    debug_json = None;
  }

let main (options : Types.engine_options) =
  Printexc.record_backtrace true;
  let result =
    try Ok (run options) with e -> Error (e, Printexc.get_raw_backtrace ())
  in
  match result with
  | Ok results ->
      let debug_json = Phase_utils.DebugBindPhase.export () in
      let results = { results with debug_json } in
      Logs.info (fun m -> m "Outputting JSON");
      Types.to_json_output results
      |> Yojson.Safe.pretty_to_string |> print_endline;
      Logs.info (fun m -> m "Exiting Hax engine (success)")
  | Error (exn, bt) ->
      Logs.info (fun m -> m "Exiting Hax engine (with an unexpected failure)");
      Printexc.raise_with_backtrace exn bt
