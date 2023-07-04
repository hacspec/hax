type t [@@deriving show, yojson, compare, sexp, eq, hash]
type name = Concrete_ident_generated.name

module Kind : sig
  type t =
    | Type
    | Value
    | Lifetime
    | Constructor of { is_struct : bool }
    | Field
    | Macro
    | Trait
    | Impl
  [@@deriving show, yojson, compare, sexp, eq, hash]
end

val of_def_id : Kind.t -> Types.def_id -> t
val of_name : Kind.t -> name -> t
val eq_name : name -> t -> bool
val to_debug_string : t -> string

type view = { crate : string; path : string list; definition : string }

val map_path_strings : f:(string -> string) -> t -> t

include module type of struct
  include Concrete_ident_sig.Make (struct
    type t_ = t
    type view_ = view
  end)
end

module MakeViewAPI (NP : NAME_POLICY) : VIEW_API
module DefaultNamePolicy : NAME_POLICY
module DefaultViewAPI : VIEW_API
