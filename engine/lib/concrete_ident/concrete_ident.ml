open! Prelude
module View = Concrete_ident_view

(** This module provides the global concrete identifiers. *)

module Fresh_module : sig
  (** This module provides a way of generating fresh modules paths. This can be
      used to reorganize locally definitions; the main motivation for this is
      recursive bundles, where we move definitions from multiple modules to
      one fresh module. This is fine because we re-expose all the original
      definitions.
    *)

  type t [@@deriving show, yojson, hash, compare, sexp, hash, eq]

  val fresh : label:string -> Explicit_def_id.t list -> t
  (** [fresh ~label hints] creates a fresh module out of the non-empty list of
      explicit definition identifiers hints [hints] and out of a label [label].

    The new module will have a unique path, close to [hints], and containing the
    label [label].
    *)

  val register : fresh_module:t -> Explicit_def_id.t -> unit
  (** [register ~fresh_module id] declares that [id] belongs to [fresh_module]. *)

  val get_path_hints : t -> Explicit_def_id.t list
  (** List path hints for a fresh module. *)

  val to_mod_path : t -> View.ModPath.t
  (** Compute a module path for a fresh module. *)
end = struct
  open View

  type t = { id : int; hints : Explicit_def_id.t list; label : string }
  [@@deriving show, yojson, hash, compare, sexp, hash, eq]

  let id_state = ref 0
  let map_state : _ Hashtbl.t = Hashtbl.create (module Int)

  let fresh ~label hints =
    id_state := !id_state + 1;
    assert (List.is_empty hints |> not);
    { id = !id_state; hints; label }

  let register ~(fresh_module : t) (did : Explicit_def_id.t) =
    let default = (Set.empty (module ModPath), None) in
    let f (set, opt) = (Set.add set (View.of_def_id did).mod_path, opt) in
    Hashtbl.update map_state fresh_module.id ~f:(Option.value ~default >> f)

  (** [compute_path_chunks fresh_module] returns [(mod_path, mod_name,
        suffixes)]. [suffixes] are optional suffixes to add to [mod_name] so
        that the resulting path is unique. *)
  let compute_path_chunks (m : t) =
    let mod_paths = List.map ~f:(fun d -> (of_def_id d).mod_path) m.hints in
    let base = List.longest_prefix ~eq:DisambiguatedString.equal mod_paths in
    assert (List.is_empty base |> not);
    let module_names =
      List.filter ~f:(List.length >> Int.equal (List.length base)) mod_paths
      |> List.filter_map ~f:List.last
      |> List.dedup_and_sort ~compare:[%compare: DisambiguatedString.t]
    in
    let hash =
      List.dedup_and_sort ~compare:[%compare: Explicit_def_id.t] m.hints
      |> [%hash: Explicit_def_id.t list] |> Int.to_string
      |> DisambiguatedString.pure
    in
    let label = DisambiguatedString.pure m.label in
    (base, label, module_names @ [ hash ])

  let all_paths =
    Explicit_def_id.State.list_all
    >> List.map ~f:(fun x -> (of_def_id x).mod_path)

  let compute_path (m : t) =
    let mod_path, mod_name, suffixes = compute_path_chunks m in
    let existing_names =
      all_paths ()
      |> List.filter_map ~f:last_init
      |> List.filter ~f:(fst >> [%eq: ModPath.t] mod_path)
      |> List.map ~f:snd
      |> List.map ~f:(fun m -> m.DisambiguatedString.data)
      |> Set.of_list (module String)
    in
    let mod_name =
      List.mapi ~f:(fun n _ -> mod_name :: List.take suffixes n) suffixes
      |> List.map ~f:(List.map ~f:(fun m -> m.DisambiguatedString.data))
      |> List.map ~f:(String.concat ~sep:"_")
      |> List.find ~f:(Set.mem existing_names)
      |> Option.value_exn
           ~message:
             "Broken invariant: in fresh modules the suffix is supposed to be \
              crafted so that it is unique."
      |> DisambiguatedString.pure
    in
    mod_path @ [ mod_name ]

  let to_mod_path m =
    Hashtbl.update_and_return map_state m.id
      ~f:
        ( Option.value ~default:(Set.empty (module ModPath), None)
        >> fun (paths, alloc) ->
          ( paths,
            alloc
            |> Option.value_or_thunk ~default:(fun () -> compute_path m)
            |> Option.some ) )
    |> snd |> Option.value_exn

  let get_path_hints { hints; _ } = hints
end

type reserved_suffix = [ `Cast | `Pre | `Post ]
[@@deriving show, yojson, hash, compare, sexp, hash, eq]
(** A concrete identifier can have a reserved suffix: this is useful to derive
  new identifiers from existing identifiers. *)

module T = struct
  type t = {
    def_id : Explicit_def_id.t;
    moved : Fresh_module.t option;
    suffix : reserved_suffix option;
  }
  [@@deriving show, yojson, hash, compare, sexp, hash, eq]
  (** A `DefId` moved under a fresh namespace *)
end

include T
include Comparator.Make (T)

let to_debug_string = T.show

let fresh_module ~label =
  List.concat_map ~f:(fun { def_id; moved; _ } ->
      def_id
      :: (Option.to_list moved |> List.concat_map ~f:Fresh_module.get_path_hints))
  >> Fresh_module.fresh ~label

module Cache = struct
  let state = Hash_set.create (module T)
  let cached = Fn.id &&& Hash_set.add state >> fst
end

let make (def_id : Explicit_def_id.t) (moved : Fresh_module.t option)
    (suffix : reserved_suffix option) =
  { def_id; moved; suffix }

let of_def_id ?(suffix : reserved_suffix option = None) ~(value : bool)
    (def_id : Types.def_id) =
  let constructor =
    (* A DefId is a constructor when it's a value and points to a variant, a union or a struct. *)
    value
    && [%matches? (Variant | Union | Struct : Types.def_kind)]
         def_id.contents.value.kind
  in
  make (Explicit_def_id.of_def_id_exn ~constructor def_id) None suffix
  |> Cache.cached

let move_to_fresh_module (fresh_module : Fresh_module.t) (i : t) =
  Fresh_module.register ~fresh_module i.def_id;
  Cache.cached { i with moved = Some fresh_module }

let with_suffix (suffix : reserved_suffix) (i : t) : t =
  { i with suffix = Some suffix }

module type VIEW_RENDERER = sig
  val render_module : View.DisambiguatedString.t -> string
  val render_name : View.RelPath.Chunk.t list -> string option
  val finalize : Concrete_ident_render_sig.rendered -> string
end

let to_view (ident : t) : Concrete_ident_view.t =
  let Concrete_ident_view.{ mod_path; rel_path } =
    View.of_def_id ident.def_id
  in
  let mod_path =
    Option.map ~f:Fresh_module.to_mod_path ident.moved
    |> Option.value ~default:mod_path
  in
  { mod_path; rel_path }

module MakeToString (R : VIEW_RENDERER) = struct
  open Concrete_ident_render_sig

  let per_module : (string list, (string, t) Hashtbl.t) Hashtbl.t =
    Hashtbl.create
      (module struct
        type t = string list [@@deriving hash, compare, sexp, eq]
      end)

  let render (i : t) : rendered =
    let Concrete_ident_view.{ mod_path; rel_path } = to_view i in
    let path = List.map ~f:R.render_module mod_path in
    let name =
      let* name = R.render_name rel_path in
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
        | Some _i' when not moved_into_fresh_ns ->
            failwith "TODO: report duplicate! R is incorrect"
        | Some _ ->
            let path : View.ModPath.t = (View.of_def_id i.def_id).mod_path in
            let path = List.map ~f:R.render_module path in
            List.folding_map ~init:[] (List.rev path) ~f:(fun acc chunk ->
                let acc = chunk :: acc in
                (acc, acc))
            |> List.map ~f:List.rev
            |> List.map ~f:(fun path ->
                   name ^ "__from__"
                   ^ String.concat ~sep:"__"
                       path (* This might shadow, we should escape *))
            |> List.find ~f:(Hashtbl.mem name_map >> not)
            |> Option.value_exn
      in
      let _ignored = Hashtbl.add ~key:name ~data:i in
      Some name
    in
    let name = name |> Option.value ~default:"" in
    { path; name }

  let show (i : t) : string =
    let { path; name } = render i in
    R.finalize { path; name }
end

module RenderSig = Concrete_ident_render_sig.Make (T)
include RenderSig

module type NAME_POLICY = Concrete_ident_render_sig.NAME_POLICY

(* TODO: rename to MakeRenderAPI *)
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

    let render_disambiguated View.DisambiguatedString.{ disambiguator; data } =
      if Int64.equal Int64.zero disambiguator then disambiguator_escape data
      else data ^ "_" ^ Int64.to_string disambiguator

    let render_module = render_disambiguated

    let disambiguate_name (n : View.RelPath.Chunk.t) :
        (string, string) View.RelPath.Chunk.poly =
      View.RelPath.Chunk.add_strings n
      |> View.RelPath.Chunk.map_poly render_disambiguated render_disambiguated

    let render_name_plain : View.RelPath.Chunk.t -> string =
      View.RelPath.Chunk.(disambiguate_name >> collect) >> sep

    let ( ^: ) x y = if String.is_empty x then y else sep [ x; y ]

    let allowed_prefixes =
      [
        "impl";
        "anon_const";
        "foreign";
        "use";
        "opaque";
        "t";
        "C";
        "v";
        "f";
        "i";
        "discriminant";
      ]

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

    let rec render_last (extra : string) (n : View.RelPath.Chunk.t) : string =
      let value_fmt = format "v" false in
      let type_fmt = format "t" true in
      let constructor_fmt ?(force_prefix = false) = format "C" force_prefix in
      match n with
      | `AssociatedItem (((`Type n | `Const n | `Fn n) as item), parent) -> (
          let impl = render_last extra (parent :> _ View.RelPath.Chunk.poly) in
          let name = render_disambiguated n in
          let s = impl ^: name in
          match item with `Type _ -> type_fmt s | _ -> value_fmt s)
      | `Impl (d, _) ->
          (* TODO! *)
          format "impl" true (extra ^: Int64.to_string d)
      | `AnonConst d -> format "anon_const" true (extra ^: Int64.to_string d)
      | `Use d -> format "use" true (extra ^: Int64.to_string d)
      | `Foreign d -> format "foreign" true (extra ^: Int64.to_string d)
      | `GlobalAsm d -> format "global_asm" true (extra ^: Int64.to_string d)
      | `Opaque d -> format "opaque" true (extra ^: Int64.to_string d)
      | `ExternCrate n
      | `Trait (n, _)
      | `ForeignTy n
      | `TraitAlias n
      | `Mod n
      | `Struct n
      | `Union n
      | `Enum n ->
          type_fmt (extra ^: render_disambiguated n)
      | `Constructor (cons, `Struct _) ->
          let cons = extra ^: render_disambiguated cons in
          constructor_fmt
            ~force_prefix:(String.is_substring cons ~substring:"_")
            cons
      | `Constructor (cons, parent) ->
          let type_name =
            extra ^: render_name_plain (parent :> _ View.RelPath.Chunk.poly)
          in
          if String.is_substring type_name ~substring:"_" then
            constructor_fmt ~force_prefix:true
              (type_name ^: render_disambiguated cons)
          else constructor_fmt (type_name ^ "_" ^ render_disambiguated cons)
      | `Macro n | `Static n | `Fn n | `Const n ->
          value_fmt (extra ^: render_disambiguated n)
      | `Field (n, _) -> value_fmt (extra ^: render_disambiguated n)

    let render_name (n : View.RelPath.t) =
      let* fake_path, name = last_init n in
      let extra = List.map ~f:render_name_plain fake_path |> sep in
      Some (render_last extra name)

    let finalize { path; name } =
      let path = List.map ~f:(map_first_letter String.uppercase) path in
      String.concat ~sep:"."
        (path @ if String.is_empty name then [] else [ name ])
  end

  include MakeToString (R)

  let pp fmt = T.show >> Stdlib.Format.pp_print_string fmt

  let show id =
    let { path; name } = render id in
    (path @ if String.is_empty name then [] else [ name ])
    |> String.concat ~sep:"::"

  let local_ident (li : Local_ident.t) : string =
    if Local_ident.is_final li then li.name
    else
      R.render_name
        [
          `Fn
            View.DisambiguatedString.
              { disambiguator = Int64.zero; data = li.name };
        ]
      |> Option.value_exn
end

(** Stateful store that maps [def_id]s to implementation informations
(which trait is implemented? for which type? under which constraints?) *)
module ImplInfoStore = struct
  let state : (Types.def_id_contents, Types.impl_infos) Hashtbl.t option ref =
    ref None

  module T = struct
    type t = Types.def_id_contents [@@deriving show, compare, sexp, eq, hash]
  end

  let init (impl_infos : (Types.def_id * Types.impl_infos) list) =
    state :=
      impl_infos
      |> List.map ~f:(fun ((id : Types.def_id), impl_infos) ->
             (id.contents.value, impl_infos))
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
    find (Explicit_def_id.to_def_id impl.def_id)
end

type name = Concrete_ident_generated.t
[@@deriving show, yojson, compare, sexp, eq, hash]

let of_name ~value = Concrete_ident_generated.def_id_of >> of_def_id ~value

let eq_name name id =
  let of_name = Concrete_ident_generated.def_id_of name in
  [%equal: Types.def_id_contents] of_name.contents.value
    (Explicit_def_id.to_def_id id.def_id)

module DefaultNamePolicy : NAME_POLICY = struct
  let reserved_words = Hash_set.create (module String)
  let index_field_transform = Fn.id
  let field_name_transform ~struct_name:_ = Fn.id
  let enum_constructor_name_transform ~enum_name:_ = Fn.id
  let struct_constructor_name_transform = Fn.id
end

module DefaultViewAPI = MakeViewAPI (DefaultNamePolicy)

let map_path_strings ~(f : string -> string) (did : t) : t =
  let constructor = did.def_id |> Explicit_def_id.is_constructor in
  let did : Types.def_id_contents = did.def_id |> Explicit_def_id.to_def_id in
  let path =
    did.path
    |> List.map ~f:(fun (chunk : Types.disambiguated_def_path_item) ->
           let data =
             match chunk.data with
             | TypeNs s -> Types.TypeNs (f s)
             | ValueNs s -> ValueNs (f s)
             | MacroNs s -> MacroNs (f s)
             | LifetimeNs s -> LifetimeNs (f s)
             | data -> data
           in
           { chunk with data })
  in
  let did = { did with path } in
  let def_id =
    Explicit_def_id.of_def_id_exn ~constructor
      { contents = { value = did; id = Base.Int64.zero } }
  in
  { def_id; moved = None; suffix = None }

let matches_namespace (ns : Types.namespace) (did : t) : bool =
  let did = Explicit_def_id.to_def_id did.def_id in
  let path : string option list =
    [ Some did.krate ]
    @ List.map
        ~f:(fun (chunk : Types.disambiguated_def_path_item) ->
          match chunk.data with
          | TypeNs s | ValueNs s | MacroNs s | LifetimeNs s -> Some s
          | _ -> None)
        did.path
  in
  let rec aux (pattern : Types.namespace_chunk list) (path : string option list)
      =
    match (pattern, path) with
    | [], [] -> true
    | Exact x :: pattern, Some y :: path ->
        [%equal: string] x y && aux pattern path
    | Glob One :: pattern, _ :: path -> aux pattern path
    | Glob Many :: pattern, [] -> aux pattern []
    | Glob Many :: pattern', _ :: path' ->
        aux pattern' path || aux pattern path'
    | _ -> false
  in
  aux ns.chunks path
