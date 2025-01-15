open! Prelude

module T = struct
  type t = { is_constructor : bool; def_id : Types.def_id_contents }
  [@@deriving show, yojson, sexp]

  type repr = bool * string * Types.disambiguated_def_path_item list
  [@@deriving hash, compare, eq]

  let to_repr { is_constructor; def_id } =
    (is_constructor, def_id.krate, def_id.path)

  let hash = to_repr >> hash_repr
  let hash_fold_t s = to_repr >> hash_fold_repr s
  let equal x y = equal_repr (to_repr x) (to_repr y)
  let compare x y = compare_repr (to_repr x) (to_repr y)
end

include T

(** Helpers for dealing with Rust raw [Types.def_id]s *)
module H = struct
  let contents (did : Types.def_id) = did.contents.value

  (** Helper to get the parent of a [Types.def_id_contents] *)
  let parent (did : Types.def_id_contents) : Types.def_id_contents option =
    Option.map ~f:contents did.parent
end

(** A pure, def_id_contents version of [of_def_id]. This is not exposed publicly. *)
let pure_of_def_id ?constructor (def_id : Types.def_id_contents) : t option =
  let* _not_crate_root = def_id.path |> List.last in
  let path_without_ctor =
    (* Get rid of extra [Ctor] *)
    let* init, last = last_init def_id.path in
    let*? _ = [%matches? Types.Ctor] last.data in
    Some init
  in
  let parent = def_id.parent in
  let parent =
    if Option.is_some path_without_ctor then
      let* parent = parent in
      (H.contents parent).parent
    else parent
  in
  let path = Option.value path_without_ctor ~default:def_id.path in
  let def_id = { def_id with parent; path } in
  let constructor =
    if Option.is_some path_without_ctor then Some true else constructor
  in
  let*? _constructor_provided_if_union_or_struct =
    not
      (Option.is_none constructor
      && [%matches? (Union | Struct : Types.def_kind)] def_id.kind)
  in
  let is_constructor =
    [%matches? (Variant : Types.def_kind)] def_id.kind
    || [%matches? Some true] constructor
  in
  Some { is_constructor; def_id }

module State = struct
  let state = Hash_set.create (module T)

  let of_def_id' ?constructor def_id_contents =
    let* did = pure_of_def_id ?constructor def_id_contents in
    Hash_set.add state did;
    Some did

  let of_def_id ?constructor def_id =
    of_def_id' ?constructor (H.contents def_id)

  let list_all () = Hash_set.to_list state
end

let of_def_id = State.of_def_id

let of_def_id_exn ?constructor def_id =
  of_def_id ?constructor def_id |> Option.value_exn

let parent (did : t) : t option =
  let* parent = H.parent did.def_id in
  let*? _not_crate_root = List.is_empty parent.path |> not in
  let constructor = [%matches? (Field : Types.def_kind)] did.def_id.kind in
  State.of_def_id' ~constructor parent

let rec parents (did : t) =
  did :: (parent did |> Option.map ~f:parents |> Option.value ~default:[])

let to_def_id { def_id; _ } = def_id
let is_constructor { is_constructor; _ } = is_constructor

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

  let lookup_raw (impl_def_id : t) : Types.impl_infos option =
    find (to_def_id impl_def_id)
end
