open! Prelude

(** Rust shares one same `DefId` for the constructor of a struct and the type of the struct. We disambiguate that by creating a separate identifier here. *)
type kind = Regular | StructConstructor
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

module T = struct
  module Types = struct
    include Types

    let def_id_contents_of_yojson = Types.parse_def_id_contents
    let yojson_of_def_id_contents = Types.to_json_def_id_contents
  end

  type t = { kind : kind; def_id : Types.def_id_contents }
  [@@deriving show, yojson, hash, compare, sexp, hash, eq]
end

include T

let contents (did : Types.def_id) = did.contents.value
let parent' (did : Types.def_id_contents) = did.parent |> Option.map ~f:contents

let parent (did : t) =
  parent' did.def_id |> Option.map ~f:(fun def_id -> { kind = Regular; def_id })

let rec parents' (did : t) =
  did :: (parent did |> Option.map ~f:parents' |> Option.value ~default:[])

let parents = parents' >> List.drop_last_exn
let make' kind (def_id : Types.def_id) = { kind; def_id = contents def_id }
let state = Hash_set.create (module T)

let make kind def_id =
  let did = make' kind def_id in
  Hash_set.add state did;
  did

let def_id { def_id; _ } = def_id
let kind { kind; _ } = kind
let list_all () = Hash_set.to_list state
