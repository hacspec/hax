open! Prelude

type disambiguator = Int64.t
[@@deriving show, hash, compare, sexp, hash, eq, map]

type disambiguated_string = { disambiguator : disambiguator; data : string }
[@@deriving show, hash, compare, sexp, hash, eq, map]

module Name = struct
  type 'name type_definition =
    [ `Enum of 'name | `Struct of 'name | `Union of 'name ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type 'name constructor = [ `Constructor of 'name * 'name type_definition ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type 'name maybe_associated = [ `Fn of 'name | `Const of 'name ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type 'name associated = [ 'name maybe_associated | `Type of 'name ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type ('name, 'disambiguator) assoc_parent =
    [ `Impl of 'disambiguator * [ `Inherent | `Trait ] | `Trait of 'name ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type ('name, 'disambiguator) poly =
    [ 'name type_definition
    | 'name constructor
    | 'name maybe_associated
    | ('name, 'disambiguator) assoc_parent
    | `Use of 'name
    | `AnonConst of 'disambiguator
    | `TraitAlias of 'name
    | `Foreign of 'name
    | `Opaque of 'name
    | `Static of 'name
    | `Macro of 'name
    | `AssociatedItem of 'name associated * ('name, 'disambiguator) assoc_parent
    | `Field of 'name * 'name constructor ]
  [@@deriving show, hash, compare, sexp, hash, eq, enumerate, map]

  type t = (disambiguated_string, disambiguator) poly
  [@@deriving show, hash, compare, sexp, hash, eq]

  let add_strings ?(impl = "impl") ?(anon_const = "anon_const") (n : t) :
      (disambiguated_string, disambiguated_string) poly =
    let f disambiguator = { disambiguator; data = impl } in
    match map_poly Fn.id f n with
    | `AnonConst o -> `AnonConst { o with data = anon_const }
    | n -> n

  let only_disambiguators : t -> (Int64.t, Int64.t) poly =
    map_poly (fun ds -> ds.disambiguator) Fn.id

  (** Collects all the informations in a name, from the child to the parent. *)
  let rec collect_either : 'n 'd. ('n, 'd) poly -> [ `N of 'n | `D of 'd ] list
      = function
    | `AnonConst n | `Impl (n, _) -> [ `D n ]
    | `Use n | `TraitAlias n | `Foreign n -> [ `N n ]
    | `Opaque n | `Static n | `Macro n | `Enum n | `Struct n | `Union n ->
        [ `N n ]
    | `Fn n | `Const n | `Trait n -> [ `N n ]
    | `AssociatedItem ((`Fn a | `Const a | `Type a), b) ->
        `N a :: collect_either (b :> _ poly)
    | `Constructor (a, b) -> `N a :: collect_either (b :> _ poly)
    | `Field (a, b) -> `N a :: collect_either (b :> _ poly)

  (** Collects all the informations in a name, from the child to the parent. *)
  let collect : 'a. ('a, 'a) poly -> 'a list =
   fun n -> collect_either n |> List.map ~f:(function `D v | `N v -> v)

  let root : 'a. ('a, 'a) poly -> 'a = fun x -> collect x |> List.last_exn
end

type path = disambiguated_string list
[@@deriving show, hash, compare, sexp, hash, eq]

type t = { path : path; name_path : Name.t list }
[@@deriving show, hash, compare, sexp, hash, eq]
(** Invariant: [name_path] is non-empty *)
