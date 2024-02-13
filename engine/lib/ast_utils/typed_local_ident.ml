open! Prelude

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)

  module T = struct
    type t = Local_ident.t * AST.ty [@@deriving show, yojson]

    let sexp_of_t : t -> _ = fst >> Local_ident.sexp_of_t
    let compare (a : t) (b : t) = [%compare: Local_ident.t] (fst a) (fst b)
    let equal (a : t) (b : t) = [%eq: Local_ident.t] (fst a) (fst b)
  end

  include Base.Comparator.Make (T)
  include T
end
