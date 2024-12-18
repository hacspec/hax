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

  let add_strings ?(impl = "impl") ?(anon_const = "anon_const") (n : t) :
      (disambiguated_string, disambiguated_string) poly =
    let f disambiguator = { disambiguator; data = impl } in
    match map_poly Fn.id f n with
    | `AnonConst o -> `AnonConst { o with data = anon_const }
    | n -> n

  let rec collect : 'a. ('a, 'a) poly -> 'a list = function
    | `AnonConst n | `Impl (n, _) | `Use n | `TraitAlias n | `Foreign n -> [ n ]
    | `Opaque n | `Static n | `Macro n | `Enum n | `Struct n | `Union n -> [ n ]
    | `Fn n | `Const n | `Trait n -> [ n ]
    | `AssociatedItem ((`Fn a | `Const a | `Type a), b) ->
        a :: collect (b :> _ poly)
    | `Constructor (a, b) -> a :: collect (b :> _ poly)
    | `Field (a, b) -> a :: collect (b :> _ poly)

  let root : 'a. ('a, 'a) poly -> 'a = fun x -> collect x |> List.last_exn
end

type t = { path : disambiguated_string list; name_path : Name.t list }
