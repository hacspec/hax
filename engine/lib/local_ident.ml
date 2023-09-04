open! Prelude

module T = struct
  type kind = Typ | Cnst | Expr | LILifetime | Final
  [@@deriving show, yojson, hash, compare, sexp, eq]

  type id = kind * int [@@deriving show, yojson, hash, compare, sexp, eq]

  let mk_id kind id = (kind, id)

  type t = { name : string; id : id }
  [@@deriving show, yojson, hash, compare, sexp, eq]

  let make_final name = { name; id = mk_id Final 0 }
  let is_final { id; _ } = [%matches? Final] @@ fst id
end

include Base.Comparator.Make (T)
include T
