open! Prelude
open Ast

module Misc (F : Features.T) : sig
  module AST : module type of Ast.Make (F)
  open AST

  val pat_is_expr : pat -> expr -> bool
end

module Construct (F : Features.T) : sig
  module AST : module type of Ast.Make (F)
  open AST

  val tuple_field_pat : int -> int -> pat -> field_pat

  module Ty : sig
    val never : ty
    val unit : ty
    val tuple' : ty list -> ty
    val tuple : ty list -> ty
    val hax_failure : ty
  end

  module Pat : sig
    val var : local_ident -> ty -> span -> pat
    val wild : ty -> span -> pat
    val tuple' : ?drop_tuple_1:bool -> span -> field_pat list -> pat
    val tuple : ?drop_tuple_1:bool -> ?span:span -> pat list -> pat
  end

  module Expr : sig
    val unit : span -> expr
    val string_lit : span -> string -> expr
    val let_ : pat -> expr -> expr -> expr
    val let_uncurried : local_ident * expr -> expr -> expr
    val multiple_lets : (local_ident * expr) list -> expr -> expr
    val seq : expr -> expr -> expr
    val tuple' : span:span -> expr list -> expr
    val tuple : span:span -> expr list -> expr

    val app' :
      ?impl:impl_expr -> Global_ident.t -> expr list -> span -> ty -> expr

    val app :
      ?impl:impl_expr ->
      ?kind:Concrete_ident.Kind.t ->
      Concrete_ident.name ->
      expr list ->
      span ->
      ty ->
      expr

    val hax_failure' :
      span -> ty -> Diagnostics.Context.t * Types.kind -> string -> expr

    val hax_failure :
      span -> ty -> Diagnostics.Context.t * Types.kind -> Ast.Full.expr -> expr

    val tuple_projector : span -> ty -> int -> int -> ty -> expr
  end

  val unit_param : span -> param
end

module Destruct (F : Features.T) : sig
  module AST : module type of Ast.Make (F)
  open AST

  module Item : sig
    val functions : item -> (concrete_ident * expr) list
  end

  module Expr : sig
    val mut_borrow : expr -> expr option
    val deref : expr -> expr option
    val concrete_app1 : Concrete_ident.name -> expr -> expr option
    val concrete_app' : expr' -> concrete_ident option
    val deref_mut_app : expr -> expr option
    val local_var : expr -> expr option
    val let_bindings' : expr -> (pat * expr * ty) list * expr
    val let_bindings : expr -> (pat * expr) list * expr
  end

  module Ty : sig
    val arrow : ty -> (ty list * ty) option
    val mut_ref : ty -> ty option
    val never : ty -> bool
    val unit : ty -> bool
  end
end
