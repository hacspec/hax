open! Prelude
module View = Concrete_ident_view

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
      |> List.find ~f:(Set.mem existing_names >> not)
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
  (** A concrete identifier is defined as a  *)
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

  val render_name :
    namespace:View.ModPath.t -> View.RelPath.Chunk.t list -> string option

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

(** Stateful store that maps [def_id]s to implementation informations
(which trait is implemented? for which type? under which constraints?) *)
module ImplInfoStore = struct
  include Explicit_def_id.ImplInfoStore

  let lookup_raw (impl : t) : Types.impl_infos option = lookup_raw impl.def_id
end

module MakeToString (R : VIEW_RENDERER) = struct
  open Concrete_ident_render_sig

  (** For each module namespace, we store three different pieces of data:
      - a map from relative paths (i.e. the non-module part of a path) to full
        identifiers
      - an set of rendered names in this namespace
      - a memoization map from full identifiers to rendered names

      If an identifier was already rendered, we just use this already rendered
      name.

      Otherwise, when we print a name under a fresh module, we take a look at
      the first map: if there is already an identifier in the fresh module with
      the exact same relative path, then we have a collision, and we need to
      generate a fresh name.

      To generate a fresh name, we use the set of rendered names.
      *)
  let per_module :
      ( string list,
        (View.RelPath.t, t) Hashtbl.t
        * string Hash_set.t
        * (t, string) Hashtbl.t )
      Hashtbl.t =
    Hashtbl.create
      (module struct
        type t = string list [@@deriving hash, compare, sexp, eq]
      end)

  let render (i : t) : rendered =
    let Concrete_ident_view.{ mod_path; rel_path } = to_view i in
    let path = List.map ~f:R.render_module mod_path in
    let name =
      (* Retrieve the various maps. *)
      let rel_path_map, name_set, memo =
        Hashtbl.find_or_add per_module
          ~default:(fun _ ->
            ( Hashtbl.create (module View.RelPath),
              Hash_set.create (module String),
              Hashtbl.create (module T) ))
          path
      in
      (* If we rendered [i] already in the past, just use that. *)
      match Hashtbl.find memo i with
      | Some name -> Some name
      | None ->
          let* name = R.render_name ~namespace:mod_path rel_path in
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
          let moved_into_fresh_ns = Option.is_some i.moved in
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
            match Hashtbl.find rel_path_map rel_path with
            | Some _ when moved_into_fresh_ns ->
                let path : View.ModPath.t =
                  (View.of_def_id i.def_id).mod_path
                in
                let path = List.map ~f:R.render_module path in
                (* Generates the list of all prefixes of reversed `path` *)
                List.folding_map ~init:[] (List.rev path) ~f:(fun acc chunk ->
                    let acc = chunk :: acc in
                    (acc, acc))
                (* We want to try small prefixes first *)
                |> List.map ~f:List.rev
                (* We generate a fake path with module ancestors *)
                |> List.map ~f:(fun path ->
                       name ^ "__from__"
                       ^ String.concat ~sep:"__"
                           path (* This might shadow, we should escape *))
                   (* Find the shortest name that doesn't exist already *)
                |> List.find ~f:(Hash_set.mem name_set >> not)
                |> Option.value_exn
            | _ -> name
          in
          (* Update the maps and hashtables *)
          let _ = Hashtbl.add rel_path_map ~key:rel_path ~data:i in
          let _ = Hash_set.add name_set name in
          let _ = Hashtbl.add memo ~key:i ~data:name in
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

  let is_reserved_word : string -> bool = Hash_set.mem NP.reserved_words

  module R : VIEW_RENDERER = struct
    let disambiguator_escape s =
      match split_str ~on:"_" s |> List.rev with
      | hd :: _ :: _ when Int.of_string_opt hd |> Option.is_some -> s ^ "_"
      | _ -> s

    let render_disambiguated View.DisambiguatedString.{ disambiguator; data } =
      if Int64.equal Int64.zero disambiguator then disambiguator_escape data
      else data ^ "_" ^ Int64.to_string disambiguator

    let render_module = render_disambiguated

    module NameAst = struct
      module Separator = struct
        let separator = "__"
        let concat x y = x ^ separator ^ y

        let escape =
          let re = Re.Pcre.regexp "_(e*)_" in
          let f group = "_e" ^ Re.Group.get group 1 ^ "_" in
          Re.replace ~all:true re ~f
      end

      module Prefixes : sig
        type t = private string [@@deriving eq, show]

        val allowed : t list
        (** List of allowed reserved prefixes. *)

        val mk : string -> t
        (** Creates a prefix, if it is valid. *)

        val escape : string -> string
        (** Escapes reserved prefixes in a string *)
      end = struct
        type t = string [@@deriving eq, show]

        let allowed =
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

        let mem = List.mem ~equal:[%eq: string] allowed

        let mk s =
          if mem s then s
          else
            failwith ("broken invariant: [" ^ s ^ "] is not an allowed prefix")

        let escape_char = "e"

        let () =
          assert (
            (* Make sure there is no prefix `Cs` such that `C ^ "s"` is a prefix as well. *)
            List.for_all allowed ~f:(fun s -> not (mem (first_letter s ^ s))))

        let () = assert (mem "e" |> not)

        let rec escape (s : string) : string =
          match String.lsplit2 ~on:'_' s with
          | Some ("", rest) -> "e_" ^ escape rest
          | Some (prefix, rest)
            when List.mem ~equal:[%equal: string] allowed prefix ->
              first_letter prefix ^ prefix ^ "_" ^ escape rest
          | _ -> s
      end

      type policy = {
        prefix : Prefixes.t;
        disable_when : [ `SameCase ] list;
        mode : [ `Global | `Local | `Both ];
      }
      [@@deriving eq, show]

      type t =
        | Concat of (t * t)  (** Concatenate two names *)
        | Policy of (policy * t)
        | TrustedString of string  (** A string that is already escaped *)
        | UnsafeString of string  (** A string that needs escaping *)
        | Empty
      [@@deriving eq, show]

      let rec global_policy ast : _ =
        let filter =
          Option.filter ~f:(fun p -> [%matches? `Global | `Both] p.mode)
        in
        let ( <|> ) v f = match v with Some v -> Some v | None -> f () in
        match ast with
        | Policy (policy, contents) ->
            global_policy contents |> filter <|> fun _ ->
            policy |> Option.some |> filter
        | Concat (l, r) ->
            global_policy r |> filter <|> fun _ -> global_policy l |> filter
        | _ -> None

      let escape_unsafe_string = Prefixes.escape >> Separator.escape

      let apply_policy (leftmost : bool) (policy : policy) (escaped : string) =
        let prefix = (policy.prefix :> string) in
        let disable =
          List.exists policy.disable_when ~f:(function `SameCase ->
              let first_upper = first_letter >> is_uppercase in
              Bool.equal (first_upper prefix) (first_upper escaped))
        in
        if (not disable) || (leftmost && is_reserved_word escaped) then
          prefix ^ "_" ^ escaped
        else escaped

      let rec norm' = function
        | Concat (Empty, x) | Concat (x, Empty) -> x
        | Policy (_, Empty) -> Empty
        | Policy (p, x) -> Policy (p, norm' x)
        | Concat (x, y) -> Concat (norm' x, norm' y)
        | x -> x

      let rec norm x =
        let x' = norm' x in
        if [%eq: t] x x' then x else norm x'

      let concat_list =
        List.fold ~f:(fun l r -> Concat (l, r)) ~init:Empty >> norm

      let rec render' leftmost ast =
        match ast with
        | Concat (a, b) ->
            Separator.concat (render' leftmost a) (render' false b)
        | Policy (policy, a) when [%matches? `Global] policy.mode ->
            render' leftmost a
        | Policy (policy, a) ->
            render' leftmost a |> apply_policy leftmost policy
        | TrustedString s -> s
        | UnsafeString s -> escape_unsafe_string s
        | Empty -> ""

      let render ast =
        let policy = global_policy ast in
        let policy =
          Option.map ~f:(apply_policy true) policy
          |> Option.value ~default:Fn.id
        in
        let rendered = norm ast |> render' true |> policy in
        if is_reserved_word rendered then rendered ^ "_escape_reserved_word"
        else rendered
    end

    (** [pretty_impl_name ~namespace impl_infos] computes a pretty impl name given impl informations and a namespace.
        A pretty name can be computed when:
        - (1) the impl, (2) the type and (3) the trait implemented all live in the same namespace
        - the impl block has no generics
        - the type implemented is simple enough to be represented as a string (see module {!Thir_simple_types})
    *)
    let pretty_impl_name ~namespace (impl_infos : Types.impl_infos) =
      let* ty = Thir_simple_types.to_string ~namespace impl_infos.typ in
      let*? _no_generics = List.is_empty impl_infos.generics.params in
      match impl_infos.trait_ref with
      | None -> Some ty
      | Some { def_id = trait; generic_args = [ _self ] } ->
          let* trait = Explicit_def_id.of_def_id trait in
          let trait = View.of_def_id trait in
          let*? _same_ns = [%eq: View.ModPath.t] namespace trait.mod_path in
          let* trait =
            match trait.rel_path with
            | [ `Trait (n, _) ] when Int64.equal Int64.zero n.disambiguator ->
                Some n.data
            | _ -> None
          in
          let trait =
            let re = Re.Pcre.regexp "_((?:e_)*)for_" in
            let f group = "_e_" ^ Re.Group.get group 1 ^ "for_" in
            Re.replace ~all:true re ~f trait
          in
          Some (trait ^ "_for_" ^ ty)
      | _ -> None

    (** Produces a name for an impl block, only if it is necessary (e.g. the disambiguator is non-null) *)
    let impl_name ~namespace ?(always = false) disambiguator
        (impl_infos : Types.impl_infos option) =
      let pretty = impl_infos |> Option.bind ~f:(pretty_impl_name ~namespace) in
      let*? _ = always || Int64.equal Int64.zero disambiguator |> not in
      match pretty with
      | Some pretty -> Some pretty
      | None ->
          if Int64.equal Int64.zero disambiguator then None
          else Some (Int64.to_string disambiguator)

    (** Renders one chunk *)
    let rec render_chunk ~namespace (chunk : View.RelPath.Chunk.t) : NameAst.t =
      let prefix ?(global = false) ?(disable_when = []) s contents =
        NameAst.Policy
          ( {
              prefix = NameAst.Prefixes.mk s;
              mode = (if global then `Both else `Local);
              disable_when;
            },
            contents )
      in
      let prefix_d s d = prefix s (NameAst.UnsafeString (Int64.to_string d)) in
      let dstr s = NameAst.UnsafeString (render_disambiguated s) in
      let _render_chunk = render_chunk ~namespace in
      match chunk with
      | `AnonConst d -> prefix_d "anon_const" d
      | `Use d -> prefix_d "use" d
      | `Foreign d -> prefix_d "foreign" d
      | `GlobalAsm d -> prefix_d "global_asm" d
      | `Opaque d -> prefix_d "opaque" d
      (* The name of a trait impl *)
      | `Impl (d, _, impl_infos) -> (
          match impl_name ~namespace d impl_infos with
          | Some name -> prefix "impl" (UnsafeString name)
          | None -> TrustedString "impl")
      (* Print the name of an associated item in a inherent impl *)
      | `AssociatedItem
          ((`Type n | `Const n | `Fn n), `Impl (d, `Inherent, impl_infos)) ->
          let impl =
            match impl_name ~always:true ~namespace d impl_infos with
            | Some name -> prefix "impl" (UnsafeString name)
            | None -> TrustedString "impl"
          in
          Concat (impl, dstr n)
      (* Print the name of an associated item in a trait impl *)
      | `AssociatedItem
          ((`Type n | `Const n | `Fn n), (`Trait _ | `Impl (_, `Trait, _))) ->
          prefix "f" (dstr n)
      (* The constructor of a struct *)
      | `Constructor (cons, `Struct _) ->
          prefix ~global:true ~disable_when:[ `SameCase ] "C" (dstr cons)
      | `Constructor (cons, (`Enum n | `Union n)) ->
          (* [TODO] Here, we separate with `_` so that we keep the old behavior: this is dodgy. *)
          let n = render_disambiguated n ^ "_" ^ render_disambiguated cons in
          prefix ~global:true ~disable_when:[ `SameCase ] "C" (UnsafeString n)
      | `Field (n, _) -> prefix "f" (dstr n)
      (* Anything function-like *)
      | `Macro n | `Static n | `Fn n | `Const n ->
          prefix "v" ~disable_when:[ `SameCase ] (dstr n)
      (* Anything type-like *)
      | `ExternCrate n
      | `Trait (n, _)
      | `ForeignTy n
      | `TraitAlias n
      | `Mod n
      | `Struct n
      | `Union n
      | `Enum n ->
          prefix "t" (dstr n)

    let render_name ~namespace (rel_path : View.RelPath.t) =
      let rel_path =
        List.map ~f:(render_chunk ~namespace) rel_path |> NameAst.concat_list
      in
      Some (NameAst.render rel_path)

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
      R.render_name ~namespace:[]
        [
          `Fn
            View.DisambiguatedString.
              { disambiguator = Int64.zero; data = li.name };
        ]
      |> Option.value_exn
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
