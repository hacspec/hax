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

let of_def_id ?(suffix : reserved_suffix option = None) ~(value : bool)
    (def_id : Types.def_id) =
  let kind =
    match def_id.contents.value.kind with
    | Struct when value -> DefId.StructConstructor
    | _ -> Regular
  in
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

let to_view (ident : t) : Concrete_ident_view.t =
  let Concrete_ident_view.{ path; name_path } = View.of_def_id ident.def_id in
  let path =
    Option.map ~f:FreshNamespace.get_path ident.moved
    |> Option.value ~default:path
  in
  { path; name_path }

module MakeToString (R : VIEW_RENDERER) = struct
  open Concrete_ident_render_sig

  let per_module : (string list, (string, t) Hashtbl.t) Hashtbl.t =
    Hashtbl.create
      (module struct
        type t = string list [@@deriving hash, compare, sexp, eq]
      end)

  let render (i : t) : rendered =
    let Concrete_ident_view.{ path; name_path } = to_view i in
    let path = List.map ~f:R.render_module path in
    let name = R.render_name name_path in
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
    let name_map =
      Hashtbl.find_or_add per_module
        ~default:(fun _ -> Hashtbl.create (module String))
        path
    in
    let moved_into_fresh_ns = Option.is_none i.moved in
    let name =
      if moved_into_fresh_ns then
        let escape_sep =
          let re = Re.Pcre.regexp "__(e*)from__" in
          let f group = "__e" ^ Re.Group.get group 1 ^ "from__" in
          Re.replace ~all:true re ~f
        in
        escape_sep name
      else name
    in
    let name =
      match Hashtbl.find name_map name with
      | Some i' when [%equal: t] i i' -> name
      | None -> name
      | Some _i' when moved_into_fresh_ns ->
          failwith "TODO: report duplicate! R is incorrect"
      | Some i' ->
          let path : View.path = (View.of_def_id i.def_id).path in
          let path = List.map ~f:R.render_module path in
          List.folding_map ~init:[] (List.rev path) ~f:(fun acc chunk ->
              let acc = chunk :: acc in
              (acc, acc))
          |> List.map ~f:List.rev
          |> List.map ~f:(fun path ->
                 name ^ "__from__"
                 ^ String.concat ~sep:"__"
                     path (* This might shadow, we shoudl escape *))
          |> List.find ~f:(Hashtbl.mem name_map >> not)
          |> Option.value_exn
    in
    let _ignored = Hashtbl.add ~key:name ~data:i in
    { path; name }

  let show (i : t) : string =
    let { path; name } = render i in
    R.finalize { path; name }
end

module RenderSig = Concrete_ident_render_sig.Make (T)
include RenderSig

module type NAME_POLICY = Concrete_ident_render_sig.NAME_POLICY

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

    let disambiguate_name (n : View.Name.t) : (string, string) View.Name.poly =
      View.Name.add_strings n
      |> View.Name.map_poly render_disambiguated render_disambiguated

    let render_name_plain : View.Name.t -> string =
      View.Name.(disambiguate_name >> collect) >> sep

    let ( ^: ) x y = if String.is_empty x then y else sep [ x; y ]

    let allowed_prefixes =
      [ "impl"; "anon_const"; "t"; "C"; "v"; "f"; "i"; "discriminant" ]

    let escape_prefixes (s : string) : string =
      match String.lsplit2 ~on:'_' s with
      | Some (prefix, _)
        when List.mem ~equal:[%equal: string] allowed_prefixes prefix ->
          prefix ^ s
      | _ -> s

    (** This formats a string as [<prefix>_<s>] if [requiered_prefix] is true or if [s]'s first letter is uppercase while [prefix]'s first letter is lowercase or vice-versa. *)
    let format (prefix : string) (requiered_prefix : bool) (s : string) : string
        =
      let is_prefix_upper = prefix |> first_letter |> is_uppercase in
      let is_s_upper = s |> first_letter |> is_uppercase in
      if Bool.equal is_s_upper is_prefix_upper && not requiered_prefix then
        escape_prefixes s
      else prefix ^ "_" ^ s

    let rec render_last (extra : string) (n : View.Name.t) : string =
      let value_fmt = format "v" false in
      let type_fmt = format "t" true in
      let constructor_fmt ?(force_prefix = false) = format "C" force_prefix in
      match n with
      | `AssociatedItem (((`Type n | `Const n | `Fn n) as item), parent) -> (
          let impl = render_last extra (parent :> _ View.Name.poly) in
          let name = render_disambiguated n in
          let s = impl ^: name in
          match item with `Type _ -> type_fmt s | _ -> value_fmt s)
      | `Impl (d, _) ->
          (* TODO! *)
          format "impl" true (extra ^: Int64.to_string d)
      | `AnonConst d -> format "anon_const" true (extra ^: Int64.to_string d)
      | `Use n -> value_fmt (extra ^: render_disambiguated n)
      | `TraitAlias n | `Struct n | `Union n | `Enum n | `Opaque n ->
          type_fmt (extra ^: render_disambiguated n)
      | `Constructor (cons, `Struct _) ->
          let cons = extra ^: render_disambiguated cons in
          constructor_fmt
            ~force_prefix:(String.is_substring cons ~substring:"_")
            cons
      | `Constructor (cons, parent) ->
          let type_name =
            extra ^: render_name_plain (parent :> _ View.Name.poly)
          in
          if String.is_substring type_name ~substring:"_" then
            constructor_fmt ~force_prefix:true
              (type_name ^: render_disambiguated cons)
          else constructor_fmt (type_name ^ "_" ^ render_disambiguated cons)
      | `Foreign n | `Fn n | `Const n ->
          value_fmt (extra ^: render_disambiguated n)
      | _ -> failwith ""

    let render_name (n : View.Name.t list) =
      let fake_path, name = last_init n |> Option.value_exn in
      let extra = List.map ~f:render_name_plain fake_path |> sep in
      render_last extra name

    let finalize { path; name } =
      let path = List.map ~f:(map_first_letter String.uppercase) path in
      String.concat ~sep:"." (path @ [ name ])
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

let of_name ~value = Concrete_ident_generated.def_id_of >> of_def_id ~value

let eq_name name id =
  let of_name = Concrete_ident_generated.def_id_of name in
  [%equal: Types.def_id_contents] of_name.contents.value
    (DefId.def_id id.def_id)

module DefaultNamePolicy : NAME_POLICY = struct
  let reserved_words = Hash_set.create (module String)
  let index_field_transform = Fn.id
  let field_name_transform ~struct_name:_ = Fn.id
  let enum_constructor_name_transform ~enum_name:_ = Fn.id
  let struct_constructor_name_transform = Fn.id
end
