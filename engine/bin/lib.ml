open Hax_engine
open Base

let read_options_from_stdin () : Types.engine_options =
  In_channel.input_all In_channel.stdin
  |> Yojson.Safe.from_string |> Types.parse_engine_options

let run () : Types.output =
  let options = read_options_from_stdin () in
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
    options.input
    |> List.concat_map ~f:(fun item ->
           try
             Result.map_error ~f:Import_thir.show_error
               (Import_thir.c_item item)
             |> Result.ok_or_failwith
           with Failure e -> failwith e)
    |> apply_phases backend_options
    |> translate backend_options
  in
  let diagnostics, files =
    Diagnostics.try_ (fun () ->
        match options.backend.backend with
        | Fstar -> run (module Fstar_backend) ()
        | Coq -> run (module Coq_backend) ()
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
      Types.to_json_output results
      |> Yojson.Safe.pretty_to_string |> print_endline
  | Error (exn, bt) -> Printexc.raise_with_backtrace exn bt
