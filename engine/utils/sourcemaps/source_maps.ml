open Prelude
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
module Location = Location
include Mappings

type mapping = {
  gen : range;
  src : range;
  source : string;
  name : string option;
}

type t = {
  mappings : string;
  sourceRoot : string;
  sources : string list;
  sourcesContent : string option list;
  names : string list;
  version : int;
  file : string;
}
[@@deriving yojson]

let dedup_freq (l : string list) : string list =
  let hashtbl : (string, int) Hashtbl.t = Hashtbl.create (module String) in
  List.iter ~f:(Hashtbl.incr hashtbl) l;
  Hashtbl.to_alist hashtbl
  |> List.sort ~compare:(fun (_, x) (_, y) -> Int.(y - x))
  |> List.map ~f:fst

let mk ?(file = "") ?(sourceRoot = "") ?(sourcesContent = fun _ -> None)
    (mappings : mapping list) : t =
  let sources = List.map ~f:(fun x -> x.source) mappings |> dedup_freq in
  let names = List.filter_map ~f:(fun x -> x.name) mappings |> dedup_freq in
  let f { gen; src; source; name } =
    let file_offset, _ =
      List.findi_exn ~f:(fun _ -> String.equal source) sources
    in
    let name =
      Option.map
        ~f:(fun name ->
          List.findi_exn ~f:(fun _ -> String.equal name) names |> fst)
        name
    in
    let meta = { file_offset; name } in
    Chunk.{ gen; src; meta }
  in
  let mappings = List.map mappings ~f |> List.sort ~compare:Chunk.compare in
  Stdlib.prerr_endline @@ [%show: Chunk.t list] mappings;
  let mappings = Mappings.encode mappings in
  let sourcesContent = List.map ~f:sourcesContent sources in
  { mappings; sourceRoot; sourcesContent; sources; names; version = 3; file }

let to_json = [%yojson_of: t] >> Yojson.Safe.pretty_to_string
