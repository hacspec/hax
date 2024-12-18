open! Prelude
include Concrete_ident_view_types

module FromDefId = struct
  module DefId = Concrete_ident_defid

  (** Rust paths comes with invariants (e.g. a function is always a `ValueNs _`), this function raises an error if a path doesn't respect those. *)
  let broken_invariant (type t) msg (_did : DefId.t) : t =
    failwith
      ("DefId: an invariant have been broken. Expected " ^ msg ^ ".\n\ndid="
      ^ [%show: int] 0)

  let assert_parent did =
    DefId.parent did
    |> Option.value_or_thunk ~default:(fun _ ->
           broken_invariant "the DefId to have a parent" did)

  let assert_type_ns (did : DefId.t) =
    match List.last_exn (DefId.def_id did).path with
    | { data = TypeNs data; disambiguator } -> { data; disambiguator }
    | _ -> broken_invariant "TypeNs" did

  let assert_macro_ns (did : DefId.t) =
    match List.last_exn (DefId.def_id did).path with
    | { data = MacroNs data; disambiguator } -> { data; disambiguator }
    | _ -> broken_invariant "MacroNs" did

  let assert_value_ns (did : DefId.t) =
    match List.last_exn (DefId.def_id did).path with
    | { data = ValueNs data; disambiguator } -> { data; disambiguator }
    | _ -> broken_invariant "ValueNs" did

  let rec poly :
        'n 'd.
        into_n:(DefId.t -> disambiguated_string -> 'n) ->
        into_d:(DefId.t -> Int64.t -> 'd) ->
        DefId.t ->
        ('n, 'd) Name.poly =
   fun ~into_n ~into_d did ->
    let poly = poly ~into_n ~into_d in
    let mk_associated_item kind : ('n, 'd) Name.poly =
      `AssociatedItem
        ( kind,
          match assert_parent did |> poly with
          | (`Impl _ | `Trait _) as p -> p
          | _ -> broken_invariant "Impl | Trait" (assert_parent did) )
    in
    let assert_type_ns did = assert_type_ns did |> into_n did in
    let assert_value_ns did = assert_value_ns did |> into_n did in
    let assert_macro_ns did = assert_macro_ns did |> into_n did in
    match (DefId.def_id did).kind with
    | Struct when [%matches? DefId.StructConstructor] (DefId.kind did) ->
        let name = assert_type_ns did in
        `Constructor (name, `Struct name)
    | Variant | Ctor _ ->
        let parent = assert_parent did in
        let name = assert_type_ns did in
        `Constructor
          ( name,
            match poly parent with
            | (`Enum _ | `Struct _ | `Union _) as p -> p
            | _ -> broken_invariant "StandaloneTypeNs" parent )
    | AssocFn -> `Fn (assert_value_ns did) |> mk_associated_item
    | AssocConst -> `Const (assert_value_ns did) |> mk_associated_item
    | AssocTy -> `Type (assert_value_ns did) |> mk_associated_item
    | Field ->
        let constructor =
          match assert_parent did |> poly with
          | `Constructor _ as p -> p
          | _ -> failwith "Expected a Variant or a Standalone"
        in
        `Field (assert_type_ns did, constructor)
    | Trait -> `Trait (assert_type_ns did)
    | Macro _ -> `Macro (assert_macro_ns did)
    | Union -> `Union (assert_type_ns did)
    | Enum -> `Enum (assert_type_ns did)
    | Struct -> `Struct (assert_type_ns did)
    | AnonConst ->
        `AnonConst
          (match List.last_exn (DefId.def_id did).path with
          | { data = AnonConst; disambiguator } -> into_d did disambiguator
          | _ -> failwith "todo: invariant broken")
    | Impl { of_trait } ->
        `Impl
          (match List.last_exn (DefId.def_id did).path with
          | { data = Impl; disambiguator } ->
              (into_d did disambiguator, if of_trait then `Trait else `Inherent)
          | _ -> failwith "todo: invariant broken")
    | OpaqueTy -> `Opaque (assert_type_ns did)
    | _ -> failwith "x"

  let view_name : DefId.t -> Name.t =
    poly ~into_n:(fun _ n -> n) ~into_d:(fun _ d -> d)

  let view_name_did : DefId.t -> _ Name.poly =
    let mk x y = (x, y) in
    poly ~into_n:mk ~into_d:mk

  let decompose (did : DefId.t) : t =
    let ns_chunks, rest =
      List.split_while
        ~f:
          ( DefId.def_id >> fun def_id ->
            match def_id.kind with Mod -> true | _ -> false )
        (DefId.parents did |> List.rev)
    in
    let name_path =
      let rec f ids =
        match ids with
        | [] -> []
        | last :: _ ->
            let suffix = view_name_did last in
            Name.map_poly snd snd suffix
            :: (List.drop_while
                  ~f:
                    ([%eq: DefId.t]
                       (suffix |> Name.map_poly fst fst |> Name.root)
                    >> not)
                  ids
               |> f)
      in
      f rest
    in
    let path : disambiguated_string list =
      { data = (DefId.def_id did).krate; disambiguator = Int64.zero }
      :: List.map
           ~f:(fun (m : DefId.t) ->
             match (DefId.def_id m).path |> List.last_exn with
             | Types.{ disambiguator; data = TypeNs data } ->
                 { data; disambiguator }
             | _ -> failwith "todo: cannot handle anything but TypeNs")
           ns_chunks
    in
    { path; name_path }
end

let of_def_id = FromDefId.decompose
