open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Print_fstar

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
      'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

let () =
  let path =
    if Array.length Sys.argv <> 2 then (
      print_endline "Usage thir-elab /path/to/the/thir'/file.json";
      exit 1)
    else Sys.argv.(1)
  in
  let input = In_channel.read_all path |> Yojson.Safe.from_string in
  try
    let items = parse_list_json parse_item input in
    print_endline "Parsed";
    let converted_items =
      List.map
        ~f:(fun item ->
          print_endline "A";
          try
            Result.map_error ~f:Thir_elab.Import_thir.show_error
              (Thir_elab.Import_thir.c_item item)
          with Failure e -> Error e)
        items
    in
    print_endline "Converted";
    List.iter
      ~f:(fun item ->
        print_endline "\n----------------------------------------------------";
        print_endline
          (match item with
           | Ok item ->
              decl_to_string (pitem (Obj.magic item))
              (* let b = Buffer.create 50 in *)
              (* PPrint.ToBuffer.pretty 0.5 140 b (Thir_elab.Print.pitem item); *)
              (* Buffer.contents b *)
           | Error err -> "ERROR" ^ err))
      converted_items
  with e -> print_endline (ParseError.pp e)
