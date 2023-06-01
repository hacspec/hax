open Hax_engine
open Base

let read_options_from_stdin () : Types.engine_options =
  In_channel.input_all In_channel.stdin
  |> Yojson.Safe.from_string |> Types.parse_engine_options

let setup_logs (options : Types.engine_options) =
  let level : Logs.level option =
    match options.backend.verbose with
    | 0 -> None
    | 1 -> Some Info
    | _ -> Some Debug
  in
  Logs.set_level level;
  Logs.set_reporter @@ Logs.format_reporter ()

let run () : Types.output =
  let options = read_options_from_stdin () in
  setup_logs options;
  (match options.backend.debug_engine with
  | Some path ->
      if not (Caml.Sys.file_exists path && Caml.Sys.is_directory path) then
        failwith
          [%string
            "Engine error: the environment variable HAX_ENGINE_DEBUG is set to \
             [%{path}] which was expected to be a valid existing directory. \
             Aborting."];
      Phase_utils.DebugBindPhase.enable path
  | None -> ());
  let run (type options_type)
      (module M : Backend.T with type BackendOptions.t = options_type)
      (backend_options : options_type) : Types.file list =
    let open M in
    let items =
      options.input
      |> List.concat_map ~f:(fun item ->
             try
               Result.map_error ~f:Import_thir.show_error
                 (Import_thir.c_item item)
               |> Result.ok_or_failwith
             with Failure e -> failwith e)
    in
    Logs.info (fun m ->
        m "Applying phase for backend %s"
          ([%show: Diagnostics.Backend.t] M.backend));
    let items = apply_phases backend_options items in
    Logs.info (fun m ->
        m "Translating items with backend %s"
          ([%show: Diagnostics.Backend.t] M.backend));
    let items = translate backend_options items in
    items
  in
  let diagnostics, files =
    Diagnostics.try_ (fun () ->
        match options.backend.backend with
        | Fstar -> run (module Fstar_backend) ()
        | Coq -> run (module Coq_backend) ()
        | Ssprove -> run (module Ssprove_backend) ()
        | Easycrypt -> run (module Easycrypt_backend) ())
  in
  {
    diagnostics = List.map ~f:Diagnostics.to_thir_diagnostic diagnostics;
    files = Option.value ~default:[] files;
  }

let main () =
  Printexc.record_backtrace true;
  let result =
    try Ok (run ()) with e -> Error (e, Printexc.get_raw_backtrace ())
  in
  Phase_utils.DebugBindPhase.export ();
  match result with
  | Ok results ->
      Logs.info (fun m -> m "Outputting JSON");
      Types.to_json_output results
      |> Yojson.Safe.pretty_to_string |> print_endline;
      Logs.info (fun m -> m "Exiting Hax engine (success)")
  | Error (exn, bt) ->
      Logs.info (fun m -> m "Exiting Hax engine (with an unexpected failure)");
      Printexc.raise_with_backtrace exn bt
