module T: sig
  type kind = Typ | Cnst | Expr | LILifetime | Final
  [@@deriving show, yojson, hash, compare, sexp, eq]

  type id [@@deriving show, yojson, hash, compare, sexp, eq]

  val mk_id : kind -> int -> id

  type t = { name : string; id : id }
  [@@deriving show, yojson, hash, compare, sexp, eq]

  (* Create a frozen final local identifier: such an indentifier won't be rewritten by a name policy *)
  val make_final : string -> t
  val is_final: t -> bool
end

include module type of struct
  include Base.Comparator.Make (T)
  include T
end

