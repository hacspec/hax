open! Prelude
open Ast

let payloads : attrs -> (Types.ha_payload * span) list =
  let parse =
    (* we have to parse ["JSON"]: first a string, then a ha_payload *)
    function
    | `String s -> Yojson.Safe.from_string s |> Types.parse_ha_payload
    | x ->
        Stdlib.failwith
        @@ "Attr_payloads: payloads: expected a string while parsing JSON, got "
        ^ Yojson.Safe.pretty_to_string x
        ^ "instead"
  in
  List.filter_map ~f:(fun attr ->
      match attr.kind with
      | Tool { path; tokens } when [%eq: string] path "_hax::json" ->
          Some (tokens, attr.span)
      | _ -> None)
  >> List.map ~f:(map_fst (Yojson.Safe.from_string >> parse))

module UId = struct
  module T = struct
    type t = UId of string [@@deriving show, yojson, compare, sexp, eq]
  end

  module M = struct
    include Base.Comparator.Make (T)
    include T
  end

  include M
  module Map = Map.M (M)

  let of_raw (uid : Types.ha_uid) : t = UId uid.uid
end

module AssocRole = struct
  module T = struct
    type t = Requires | Ensures | Decreases | Refine
    [@@deriving show, yojson, compare, sexp, eq]
  end

  module M = struct
    include Base.Comparator.Make (T)
    include T
  end

  include M
  module Map = Map.M (M)

  let of_raw : Types.ha_assoc_role -> t = function
    | Requires -> Requires
    | Ensures -> Ensures
    | Decreases -> Decreases
    | Refine -> Refine
end

module MakeBase (Error : Phase_utils.ERROR) = struct
  (* Given a predicate, finds an attribute that is not supposed to occur
     more than once. Returns `None` if no such attribute was found. *)
  let find_unique_attr (attrs : attrs) ~(f : Types.ha_payload -> 'a option) :
      'a option =
    match
      payloads attrs
      |> List.filter_map ~f:(fun (x, span) ->
             Option.map ~f:(fun x -> (x, span)) (f x))
    with
    | [ (attr, _) ] -> Some attr
    | [] -> None
    | (_, first) :: (_, second) :: _ ->
        Error.assertion_failure (Span.union first second)
          "This attribute is supposed to be unique"

  (* we should have multi span errors, basically make somethings really close to Rustc diagnostics! *)

  let status : attrs -> Types.ha_item_status =
    let f = function Types.ItemStatus is -> Some is | _ -> None in
    let default : Types.ha_item_status = Types.Included { late_skip = false } in
    find_unique_attr ~f >> Option.value ~default

  let late_skip : attrs -> bool =
    status >> [%matches? Types.Included { late_skip = true }]

  let uid : attrs -> UId.t option =
    let f = function Types.Uid uid -> Some (UId.of_raw uid) | _ -> None in
    find_unique_attr ~f

  let lemma : attrs -> bool =
    payloads >> List.exists ~f:(fst >> [%matches? Types.Lemma])

  (* User code can be *decorated* (e.g. attributes `ensures` or
     `refine`). A decoration is attached to a user code via an
     `AssociatedItem` attribute, that specifies an unique identifier
     (uid) and a role (Ensure, Decreases, Refine...) *)
  let raw_associated_item : attrs -> (AssocRole.t * UId.t) list =
    payloads >> List.map ~f:fst
    >> List.filter_map ~f:(function
         | Types.AssociatedItem { role; item } ->
             Some (AssocRole.of_raw role, UId.of_raw item)
         | _ -> None)
end

module Make (F : Features.T) (Error : Phase_utils.ERROR) = struct
  module AST = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open AST
  include MakeBase (Error)

  let attrs_field (i : item) = i.attrs

  (* TODO: Maybe rename me `graph` or something? *)
  module type WITH_ITEMS = sig
    val item_uid_map : item UId.Map.t
    val item_of_uid : UId.t -> item
    val associated_items : attrs -> item AssocRole.Map.t
    val associated_item : AssocRole.t -> attrs -> item option

    val associated_fn :
      AssocRole.t -> attrs -> (generics * param list * expr) option

    val associated_expr : AssocRole.t -> attrs -> expr option
    val associated_refinement_in_type : string list -> attrs -> expr option

    include module type of MakeBase (Error)
  end

  module WithItems (I : sig
    val items : item list
  end) : WITH_ITEMS = struct
    include MakeBase (Error)

    let map_of_alist (type a b cmp) (m : (a, cmp) Comparator.Module.t)
        (l : (a * b) list) ~(dup : a -> b list -> (a, b, cmp) Map.t) :
        (a, b, cmp) Map.t =
      let (module M) = m in
      let equal x y = Int.equal (M.comparator.compare x y) 0 in
      match Map.of_alist m l with
      | `Ok map -> map
      | `Duplicate_key key ->
          List.filter ~f:(fst >> equal key) l |> List.map ~f:snd |> dup key

    (* Useful for looking up decorations *)
    let item_uid_map : item UId.Map.t =
      let f item = uid item.attrs |> Option.map ~f:(fun id -> (id, item)) in
      let l = List.filter_map ~f I.items in
      let dup uid items =
        let span = List.map ~f:(fun i -> i.span) items |> Span.union_list in
        Error.assertion_failure span
        @@ "Two or more items share the same UID "
        ^ [%show: UId.t] uid
      in
      map_of_alist (module UId) l ~dup

    let item_of_uid (uid : UId.t) : item =
      Map.find item_uid_map uid
      |> Option.value_or_thunk ~default:(fun () ->
             Error.assertion_failure (Span.dummy ())
             @@ "Could not find item with UID "
             ^ [%show: UId.t] uid)

    let associated_items : attrs -> item AssocRole.Map.t =
      let dup role items =
        let span = List.map ~f:(fun i -> i.span) items |> Span.union_list in
        Error.assertion_failure span
        @@ "Cannot associate multiple "
        ^ [%show: AssocRole.t] role
      in
      raw_associated_item
      >> List.map ~f:(map_snd item_of_uid)
      >> map_of_alist (module AssocRole) ~dup

    let associated_item (role : AssocRole.t) (attrs : attrs) : item option =
      Map.find (associated_items attrs) role

    let associated_fn (role : AssocRole.t) :
        attrs -> (generics * param list * expr) option =
      associated_item role
      >> Option.map ~f:(function
           | { v = Fn { generics; params; body; _ }; _ } ->
               (generics, params, body)
           | { span; _ } ->
               Error.assertion_failure span
                 "this associated item was expected to be a `fn` item")

    let associated_expr (role : AssocRole.t) : attrs -> expr option =
      associated_fn role >> Option.map ~f:thd3

    (* For type, there is a special treatment. The name of fields are
       global identifiers, and thus are subject to rewriting by
       [Concrete_ident] at the moment of printing. In contrast, in the
       refinement `fn` item generated by the proc-macros, the
       arguments are local identifiers, and thus are rewrited in a
       different manner.

       Thus, [associated_refinement_in_type] takes a list of
       [free_variables]: those are already formatted strings as
       printed by the backend. Then, we rewrite identities in the
       refinement formula to match exactly this print policy, using
       *final* local identifiers (see `Local_ident.make_final`). *)
    let associated_refinement_in_type (free_variables : string list) :
        attrs -> expr option =
      associated_fn Refine
      >> Option.map ~f:(fun (_, params, body) ->
             let substs =
               List.zip_exn
                 (List.concat_map ~f:U.Reducers.variables_of_param params)
                 (List.map ~f:Local_ident.make_final free_variables)
             in
             let v =
               U.Mappers.rename_local_idents (fun i ->
                   match List.find ~f:(fst >> [%eq: local_ident] i) substs with
                   | None -> i
                   | Some (_, i) -> i)
             in
             v#visit_expr () body)
  end

  let with_items (items : item list) : (module WITH_ITEMS) =
    (module WithItems (struct
      let items = items
    end))
end
