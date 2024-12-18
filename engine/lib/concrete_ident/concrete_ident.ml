open! Prelude
module DefId = Concrete_ident_defid
module View = Concrete_ident_view
module FreshNamespace = Concrete_ident_fresh_ns

type reserved_suffix = [ `Cast | `Pre | `Post ]
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

module T = struct
  type t = {
    def_id : DefId.t;
    moved : FreshNamespace.t option;
    suffix : reserved_suffix option;
  }
  [@@deriving show, yojson, hash, compare, sexp, hash, eq]
  (** A `DefId` moved under a fresh namespace *)
end

include T
include Comparator.Make (T)

let to_debug_string = T.show

let fresh_namespace (path_hints : t list) (string_hints : string list) :
    FreshNamespace.t =
  let path_hints =
    List.concat_map
      ~f:(fun { def_id; moved; _ } ->
        def_id
        :: (Option.to_list moved
           |> List.concat_map ~f:(fun ns -> ns.FreshNamespace.path_hints)))
      path_hints
  in
  FreshNamespace.make path_hints string_hints

module Cache = struct
  let state = Hash_set.create (module T)
  let cached = Fn.id &&& Hash_set.add state >> fst
end

let make (def_id : DefId.t) (moved : FreshNamespace.t option)
    (suffix : reserved_suffix option) =
  { def_id; moved; suffix }

let of_def_id ?(suffix : reserved_suffix option = None) (kind : DefId.kind)
    (def_id : Types.def_id) =
  make (DefId.make kind def_id) None suffix |> Cache.cached

let move_to_fresh_namespace (i : t) (ns : FreshNamespace.t) =
  FreshNamespace.register ns i.def_id;
  { i with moved = Some ns } |> Cache.cached

let with_suffix (suffix : reserved_suffix) (i : t) : t =
  { i with suffix = Some suffix }

module type VIEW_RENDERER = sig
  val render_module : View.disambiguated_string -> string
  val render_name : View.Name.t list -> string
  val finalize : Concrete_ident_render_sig.rendered -> string
end

module MakeToString (R : VIEW_RENDERER) = struct
  open Concrete_ident_render_sig

  let render (i : t) : rendered =
    let Concrete_ident_view.{ path; name_path } = View.of_def_id i.def_id in
    let path = List.map ~f:R.render_module path in
    let name = R.render_name name_path in
    { path; name }

  let show (i : t) : string =
    let { path; name } = render i in
    let path =
      match i.moved with
      | Some ns -> FreshNamespace.get_path ns |> List.map ~f:R.render_module
      | _ -> path
    in
    let name =
      match i.suffix with
      | Some suffix -> (
          name ^ "_"
          ^
          match suffix with
          | `Pre -> "pre"
          | `Post -> "post"
          | `Cast -> "cast_to_repr")
      | _ -> name
    in
    R.finalize { path; name }
end

include Concrete_ident_render_sig.Make (T)

module MakeViewAPI (NP : NAME_POLICY) : RENDER_API = struct
  open Concrete_ident_render_sig

  module R : VIEW_RENDERER = struct
    let escape_sep =
      let re = Re.Pcre.regexp "_(e*)_" in
      let f group = "_e" ^ Re.Group.get group 1 ^ "_" in
      Re.replace ~all:true re ~f

    let sep = List.map ~f:escape_sep >> String.concat ~sep:"__"

    let disambiguator_escape s =
      match split_str ~on:"_" s |> List.rev with
      | hd :: _ :: _ when Int.of_string_opt hd |> Option.is_some -> s ^ "_"
      | _ -> s

    let render_disambiguated View.{ disambiguator; data } =
      if Int64.equal Int64.zero disambiguator then disambiguator_escape data
      else data ^ "_" ^ Int64.to_string disambiguator

    let render_module = render_disambiguated

    type extn = [ View.Name.t | `Type of View.disambiguated_string ]

    let disambiguate_name (n : View.Name.t) : (string, string) View.Name.poly =
      View.Name.add_strings n
      |> View.Name.map_poly render_disambiguated render_disambiguated

    let rec render_name_plain : View.Name.t -> string =
      View.Name.(disambiguate_name >> collect) >> sep

    let ( ^: ) x y = if String.is_empty x then y else sep [ x; y ]

    let rec render_last (prefix : string) (n : View.Name.t) : string =
      match n with
      | `AssociatedItem (item, (`Impl (_, `Inherent) as parent)) ->
          let trait = render_name_plain (parent :> Name.View.t) in
          let name = render_name_plain (item :> extn) in
          let s = prefix ^: trait ^: name in
          (* (match )
           *) failwith ""
      | `Impl (_, _) -> prefix ^: render_name_plain (n :> extn)
      | _ -> failwith ""

    let render_name = failwith ""
    let finalize = failwith ""
  end

  include MakeToString (R)

  let pp fmt = T.show >> Stdlib.Format.pp_print_string fmt

  let show id =
    let { path; name } = render id in
    path @ [ name ] |> String.concat ~sep:"::"

  let local_ident (li : Local_ident.t) : string =
    if Local_ident.is_final li then li.name
    else
      R.render_name [ `Fn View.{ disambiguator = Int64.zero; data = li.name } ]
end

(** Stateful store that maps [def_id]s to implementation informations
(which trait is implemented? for which type? under which constraints?) *)
module ImplInfoStore = struct
  let state : (Types.def_id_contents, Types.impl_infos) Hashtbl.t option ref =
    ref None

  module T = struct
    type t = Types.def_id_contents [@@deriving show, compare, sexp, eq, hash]
  end

  let init impl_infos =
    state :=
      impl_infos
      |> Hashtbl.of_alist_multi (module T)
      |> Hashtbl.map ~f:List.hd_exn |> Option.some

  let get_state () =
    match !state with
    | None -> failwith "ImplInfoStore was not initialized"
    | Some state -> state

  (** Given a [id] of type [def_id], [find id] will return [Some
            impl_info] when [id] is an (non-inherent[1]) impl. [impl_info]
            contains information about the trait being implemented and for
            which type.
      
            [1]: https://doc.rust-lang.org/reference/items/implementations.html#inherent-implementations
        *)
  let find k = Hashtbl.find (get_state ()) k

  let lookup_raw (impl : t) : Types.impl_infos option =
    find (DefId.def_id impl.def_id)
end

type name = Concrete_ident_generated.t
[@@deriving show, yojson, compare, sexp, eq, hash]

let of_name k = Concrete_ident_generated.def_id_of >> of_def_id k

let eq_name name id =
  let of_name = Concrete_ident_generated.def_id_of name in
  [%equal: Types.def_id_contents] of_name.contents.value
    (DefId.def_id id.def_id)
