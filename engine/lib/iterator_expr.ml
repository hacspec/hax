open! Prelude

module Make (F : Features.T) = struct
  module U = Ast_utils.Make (F)
  module AST = Ast.Make (F)
  open AST

  type kind =
    | Range of { min : expr; max : expr }
    | Enumerate of t
    | Zip of t * t
    | ChunksExact of { it : t; size : expr }
    | Indexable of expr  (** a slice, an array *)

  and t = { kind : kind; typ : ty }

  module Expect = struct
    include U.Expect

    let ( <|> ) (type a) (type b) (f: a -> b option) (g: a -> b option) x = match f x with Some r -> Some r | None -> g x

    let any_ref (typ : ty) : ty option =
      match typ with TRef { typ; _ } -> Some typ | _ -> None

    let array (typ : ty) : ty option =
      match typ with TArray { typ; _ } -> Some typ | _ -> None

    let slice (typ : ty) : ty option =
      match typ with TSlice { ty; _ } -> Some ty | _ -> None

    let into_iter : expr -> expr option =
      fun e -> concrete_app1 Core__iter__traits__collect__IntoIterator__into_iter e

    let concrete_app_n (f : Concrete_ident.name) (e : expr) : expr list option =
      match e.e with
      | App { f = { e = GlobalVar (`Concrete f'); _ }; args; _ }
        when Concrete_ident.eq_name f f' ->
          Some args
      | _ -> None

    let concrete_app2 (f : Concrete_ident.name) (e : expr) :
        (expr * expr) option =
      match concrete_app_n f e with
      | Some [ x; y ] -> Some (x, y)
      | _ -> None

    let indexable (e : expr) : t option =
      let* e = into_iter e in
      let* typ =
        any_ref e.typ |> Option.value ~default:e.typ |> (array <|> slice)
      in
      Some { kind = Indexable e; typ }

    let range (e : expr) : t option =
      let* e = into_iter e in
      let* min, max = concrete_app2 Core__ops__range__Range e in
      Some { kind = Range { min; max }; typ = min.typ }
  end

  (* let from (e: expr): t option = *)
  (*                              match e with *)
  (*                            | Core__iter__traits__collect__IntoIterator__into_iter *)
end
