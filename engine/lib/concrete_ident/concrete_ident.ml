open Base
open Utils
open Ppx_yojson_conv_lib.Yojson_conv.Primitives

module Imported = struct
  type def_id = { krate : string; path : disambiguated_def_path_item list }

  and disambiguated_def_path_item = {
    data : def_path_item;
    disambiguator : int;
  }

  and def_path_item =
    | CrateRoot
    | Impl
    | ForeignMod
    | Use
    | GlobalAsm
    | ClosureExpr
    | Ctor
    | AnonConst
    | ImplTrait
    | ImplTraitAssocTy
    | TypeNs of string
    | ValueNs of string
    | MacroNs of string
    | LifetimeNs of string
  [@@deriving show, yojson, compare, sexp, eq, hash]

  let of_def_path_item : Types.def_path_item -> def_path_item = function
    | CrateRoot -> CrateRoot
    | Impl -> Impl
    | ForeignMod -> ForeignMod
    | Use -> Use
    | GlobalAsm -> GlobalAsm
    | ClosureExpr -> ClosureExpr
    | Ctor -> Ctor
    | AnonConst -> AnonConst
    | ImplTrait -> ImplTrait
    | ImplTraitAssocTy -> ImplTraitAssocTy
    | TypeNs s -> TypeNs s
    | ValueNs s -> ValueNs s
    | MacroNs s -> MacroNs s
    | LifetimeNs s -> LifetimeNs s

  let of_disambiguated_def_path_item :
      Types.disambiguated_def_path_item -> disambiguated_def_path_item =
   fun Types.{ data; disambiguator } ->
    { data = of_def_path_item data; disambiguator }

  let of_def_id Types.{ krate; path } =
    { krate; path = List.map ~f:of_disambiguated_def_path_item path }
end

module Kind = struct
  type t =
    | Type
    | Value
    | Lifetime
    | Constructor
    | Field
    | Macro
    | Trait
    | Impl
  [@@deriving show, yojson, compare, sexp, eq, hash]

  let of_def_path_item : Imported.def_path_item -> t option = function
    | TypeNs _ -> Some Type
    | ValueNs _ -> Some Value
    | LifetimeNs _ -> Some Lifetime
    | _ -> None
end

type t = { def_id : Imported.def_id; kind : Kind.t }
[@@deriving show, yojson, sexp]

(* [kind] is really a metadata, it is not relevant, `def_id`s are unique *)
let equal x y = [%equal: Imported.def_id] x.def_id y.def_id
let compare x y = [%compare: Imported.def_id] x.def_id y.def_id
let of_def_id kind def_id = { def_id = Imported.of_def_id def_id; kind }

module View = struct
  type view = { crate : string; path : string list; definition : string }

  module Utils = struct
    let string_of_def_path_item : Imported.def_path_item -> string option =
      function
      | TypeNs s | ValueNs s | MacroNs s | LifetimeNs s -> Some s
      | _ -> None

    let string_of_disambiguated_def_path_item
        (x : Imported.disambiguated_def_path_item) : string option =
      string_of_def_path_item x.data
  end

  open Utils

  let to_view (def_id : Imported.def_id) : view =
    let path, definition = last_init def_id.path |> Option.value_exn in
    let kind = Kind.of_def_path_item definition.data |> Option.value_exn in
    let path = List.filter_map ~f:string_of_disambiguated_def_path_item path in
    let definition =
      string_of_disambiguated_def_path_item definition |> Option.value_exn
    in
    { crate = def_id.krate; path; definition }

  let to_view (x : t) : view = failwith "x"
  let to_definition_name x = (to_view x).definition
end

let show =
  View.to_view
  >> (fun View.{ crate; path; definition } -> crate :: (path @ [ definition ]))
  >> String.concat ~sep:"::"

let pp fmt = show >> Caml.Format.pp_print_string fmt

type name = Concrete_ident_generated.name

let of_name k = Concrete_ident_generated.def_id_of >> of_def_id k

let eq_name name id =
  let of_name = Concrete_ident_generated.def_id_of name |> Imported.of_def_id in
  [%equal: Imported.def_id] of_name id.def_id

include View
