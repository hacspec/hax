open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab
open Desugar_utils

let import_options (o : Cli_types.options) (json_input : string) :
    Backend.Options.t =
  let d = Backend.Options.mk_default o.output_dir json_input in
  d

let run_with_backend (options : Cli_types.options) (input : string)
    (type options_type)
    (module M : Backend.T with type BackendOptions.t = options_type)
    (backend_options : options_type) =
  let open M in
  let o : Backend.Options.t = import_options options input in
  let items = Backend.read_json o.json_input in
  let items = List.concat_map ~f:(desugar o backend_options) items in
  let items =
    List.map
      ~f:(U.Mappers.rename_global_idents_item o.renamed_identifiers)
      items
  in
  translate o backend_options items

let () =
  match
    (Base.Sys.getenv "THIR_ELAB_OPTIONS", Base.Sys.getenv "THIR_ELAB_INPUT")
  with
  | Some options, Some input -> (
      let options =
        Cli_types.parse_options @@ Yojson.Safe.from_string options
      in
      let run (type options_type)
          (module M : Backend.T with type BackendOptions.t = options_type)
          (backend_options : options_type) =
        run_with_backend options input (module M) backend_options
      in
      match options.backend with
      | Fstar -> run (module Fstar_backend.FStarBackend) ()
      | Coq -> run (module Coq_backend.CoqBackend) ())
  | _ ->
     Fstar_backend.register;
     Coq_backend.register;
     Printexc.record_backtrace true;
     exit (Cmdliner.Cmd.eval (Backend.Registration.command ()))
