open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab.Print_fstar
open Thir_elab
open Desugar_utils

module DesugarToFStar = struct
  module D1 = Desugar_reject_mutable_references.Make (Features.Rust)
  module D2 = Desugar_direct_and_mut.Make (D1.FB)
  module D3 = Desugar_reject_mutable_references.MakeContinueReject (D2.FB)
  module D4 = Desugar_drop_references.Make (D3.FB)

  module D5 =
    Desugar_mutable_variable.Make
      (D4.FB)
      (struct
        let early_exit = Fn.id
      end)

  module D6 = Desugar_reject_mutable_references.EnsureIsFStar (D5.FB)

  include
    BindDesugar
      (BindDesugar (BindDesugar (BindDesugar (BindDesugar (D1) (D2)) (D3)) (D4)) (D5)) (D6)
end

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
    'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

let () = Printexc.record_backtrace true;;

let path =
  if Array.length Sys.argv <> 2 then (
    print_endline "Usage thir-elab /path/to/the/thir'/file.json";
    exit 1)
  else Sys.argv.(1)
in
let input = In_channel.read_all path |> Yojson.Safe.from_string in
try
  let items = parse_list_json parse_item input in
  prerr_endline "Parsed";
  let converted_items =
    List.map
      ~f:(fun item ->
        try Result.map_error ~f:Import_thir.show_error (Import_thir.c_item item)
        with Failure e -> Error e)
      items
  in
  prerr_endline "Converted";
  print_endline "module Example";
  List.iter
    ~f:(fun item ->
      print_endline "";
      print_endline
        (match item with
        | Ok item ->
            let item = DesugarToFStar.ditem item in
            decl_to_string (pitem item)
        | Error err -> "Convertion error: " ^ err))
    converted_items
with e -> print_endline (ParseError.pp e)
