open Thir_elab.Raw_thir_ast
open Core
open Thir_elab.Utils
open Thir_elab
open Desugar_utils

module DesugarToFStar =
[%functor_application
Reject.RawOrMutPointer Features.Rust |> Resugar_for_loop.Make
|> Desugar_direct_and_mut.Make |> Reject.Continue
|> Desugar_drop_references.Make
|> (fun X ->
     (Desugar_mutable_variable.Make (module X))
       (module struct
         let early_exit = Fn.id
       end))
|> Reject.NotFStar |> Identity]

module U = Ast_utils.Make (DesugarToFStar.FB)

let rewrite_some_idents (item : DesugarToFStar.B.item) : DesugarToFStar.B.item =
  let h = function
    | `Concrete Ast.{ crate = "hacspec_lib" as crate; path } ->
        `Concrete Ast.{ crate; path = Non_empty_list.[ last path ] }
    | `Concrete
        Ast.{ crate = "secret_integers"; path = Non_empty_list.[ "U32" ] } ->
        `Concrete
          Ast.{ crate = "hacspec_lib"; path = Non_empty_list.[ "secret" ] }
    | `Concrete Ast.{ crate = "Dummy"; path } ->
        `Concrete
          Ast.{ crate = "hacspec_lib"; path = Non_empty_list.[ last path ] }
    | x -> x
  in
  Obj.magic (U.Mappers.rename_global_idents h)#visit_item () (Obj.magic item)

let parse_list_json (parse : Yojson.Safe.t -> 'a) (input : Yojson.Safe.t) :
    'a list =
  match input with
  | `List l -> List.map ~f:parse l
  | _ -> failwith "parse_list_json: not a list"

module RustAst = Ast.Make (Features.Rust)

module Namespace = struct
  module U = struct
    module T = struct
      type t = string * string list [@@deriving show, eq, compare, sexp, hash]
    end

    include Base.Comparator.Make (T)
    include T
  end

  include U
  module Map = Map.M (U)
end

let string_of_item (item : RustAst.item) : string =
  let (module Print) =
    Print_fstar.(make { current_namespace = item.parent_namespace })
  in
  let item =
    try
      let r = DesugarToFStar.ditem item in
      DebugBindDesugar.export ();
      r
    with e ->
      DebugBindDesugar.export ();
      raise e
  in
  Print.decl_to_string (Print.pitem @@ rewrite_some_idents item)

let string_of_items =
  List.map ~f:string_of_item
  >> List.filter ~f:(String.equal "let _ = ()" >> not)
  >> String.concat ~sep:"\n\n"

let items_by_module (items : RustAst.item list) :
    RustAst.item list Namespace.Map.t =
  let h = Hashtbl.create (module Namespace) in
  List.iter items ~f:(fun item ->
      let items =
        Hashtbl.find_or_add h item.parent_namespace ~default:(fun _ -> ref [])
      in
      items := !items @ [ item ]);
  Map.of_iteri_exn
    (module Namespace)
    ~iteri:(Hashtbl.map h ~f:( ! ) |> Hashtbl.iteri)

let main () =
  Printexc.record_backtrace true;
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
          try
            Result.map_error ~f:Import_thir.show_error (Import_thir.c_item item)
            |> Result.ok_or_failwith
          with Failure e -> failwith e)
        items
    in
    prerr_endline "Converted";
    let modules =
      items_by_module converted_items
      |> Map.to_alist
      |> List.map ~f:(fun (ns, items) ->
             let mod_name =
               String.concat ~sep:"."
                 (List.map
                    ~f:(map_first_letter String.uppercase)
                    (fst ns :: snd ns))
             in
             (mod_name, "module " ^ mod_name ^ "\n\n" ^ string_of_items items))
    in
    (* TODO out dir *)
    let out_dir = "out/" in
    (try Caml.Sys.mkdir out_dir 0o777 with Sys_error _ -> ());
    List.iter
      ~f:(fun (ns, data) ->
        if not (String.equal ns "Hacspec_lib") then (
          let file = out_dir ^ ns ^ ".fst" in
          Out_channel.write_all file ~data;
          print_endline @@ "Wrote " ^ file))
      modules
  with e -> print_endline (ParseError.pp e)

let () = main ()
