open! Prelude

module Imported = struct
  type def_id = { krate : string; path : path }
  and path = disambiguated_def_path_item list

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
end

module Kind = struct
  type t =
    | Type
    | Value
    | Lifetime
    | Constructor of { is_struct : bool }
    | Field
    | Macro
    | Trait
    | Impl
    | AssociatedItem of t
  [@@deriving show, yojson, compare, sexp, eq, hash]
end
