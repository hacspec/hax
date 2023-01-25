open Base
open Utils

type todo = string [@@deriving show]
type loc = { col : int; line : int } [@@deriving show]

type span = Span of { file : string; hi : loc; lo : loc } | Dummy
[@@deriving show]

let show_span (s : span) : string = "<span>"

let span_pp (fmt : Format.formatter) (s : span) : unit =
  Format.pp_print_string fmt "<span>"

type concrete_ident = { crate : string; path : string Non_empty_list.t }
[@@deriving show]

type primitive_ident =
  | Box
  | Deref
  | Cast
  | BinOp of Raw_thir_ast.bin_op
  | UnOp of Raw_thir_ast.un_op
  | LogicalOp of Raw_thir_ast.logical_op
[@@deriving show]

type global_ident =
  [ `Concrete of concrete_ident
  | `Primitive of primitive_ident
  | `Tuple of int
  | `TupleField of int
  | `Projector of [ `Concrete of concrete_ident | `TupleField of int ] ]
[@@deriving show]

module LocalIdent = struct
  module T = struct
    type t = { name : string; id : int } [@@deriving show, compare, sexp]
  end

  include Base.Comparator.Make (T)
  include T
end

type local_ident = LocalIdent.t [@@deriving show, compare, sexp]
type size = S8 | S16 | S32 | S64 | S128 | SSize [@@deriving show, compare]
type signedness = Signed | Unsigned [@@deriving show, compare]

type int_kind = { size : size; signedness : signedness }
[@@deriving show, compare]

type literal =
  | String of string
  | Char of char
  | Int of { value : Bigint.t; kind : int_kind }
  | Float of float
  | Bool of bool
[@@deriving show]

type on = unit [@@deriving show]
type off = | [@@deriving show]

[%%type_collection
features
  ( loop,
    mutable_variable,
    mutable_reference,
    mutable_pointer,
    mutable_borrow,
    reference,
    slice,
    raw_pointer,
    early_exit,
    mem,
    macro,
    as_pattern,
    monadic )]

type 't spanned = { v : 't; span : span } [@@deriving show]

type 'mut_witness mutability = Mutable of 'mut_witness | Immutable
[@@deriving show]

type 'a borrow_kind = Shared | Unique | Mut of 'a mutable_borrow
type 'a binding_mode = ByValue | ByRef of 'a borrow_kind

type 'a ty =
  | Bool
  | Char
  | Int of int_kind
  | Float
  | Str
  | App of { ident : global_ident; args : 'a generic_arg list }
  | Array of { typ : 'a ty; length : int }
  | Slice of { witness : 'a slice; ty : 'a ty }
  | RawPointer of { witness : 'a raw_pointer } (* todo *)
  | Ref of {
      witness : 'a reference;
      region : todo;
      typ : 'a ty;
      mut : 'a mutable_reference mutability;
    }
  | False
  | Param of local_ident
  | Arrow of 'a ty list * 'a ty
  | ProjectedAssociatedType of string

and 'a generic_arg =
  | Lifetime of todo
  | Type of 'a ty
  | Const of todo
  constraint unit = 'a features_phantom
[@@deriving visitors { variety = "reduce"; name = "ty_reduce"; ancestors = [] }]

type ('a, 't) decorated = { v : 't; span : span; typ : 'a ty }

class virtual ['a] reduce_base =
  object (self : 'a)
    method visit_ty _ _ _ = self#zero
    method visit_t _ _ = self#zero
    method visit_spanned _ _ _ = self#zero
    method visit_mutability _ _ _ = self#zero
    method visit_literal _ _ = self#zero
    method visit_global_ident _ _ = self#zero
    method visit_binding_mode _ _ _ = self#zero
    method visit_as_pattern _ _ _ = self#zero
    method visit_'a _ _ = self#zero
  end

type 'a pat' =
  | Wild
  | PatAscription of { typ : 'a ty spanned; pat : 'a pat }
  | Variant of { name : global_ident; args : 'a field_pat list }
  | PatArray of { args : 'a pat list }
  | Deref of { subpat : 'a pat }
  | Constant of { lit : literal }
  | Binding of {
      mut : ('a mutable_variable[@opaque]) mutability;
      mode : 'a binding_mode;
      var : LocalIdent.t;
      typ : 'a ty;
      subpat : ('a pat * 'a as_pattern) option;
    }

and 'a pat = ('a, 'a pat') decorated

and 'a field_pat = {
  field : global_ident;
  pat : 'a pat;
}
  constraint unit = 'a features_phantom
[@@deriving
  visitors
    { variety = "reduce"; name = "pat_reduce"; ancestors = [ "reduce_base" ] }]

type 'a expr' =
  (* pure fragment *)
  | If of { cond : 'a expr; then_ : 'a expr; else_ : 'a expr option }
  | App of { f : 'a expr; args : 'a expr list (* ; f_span: span *) }
  | Literal of literal
  | Array of 'a expr list
  | Record of { fields : (global_ident * 'a expr) list; base : 'a expr option }
  | Match of { scrutinee : 'a expr; arms : 'a arm list }
  | Let of { lhs : 'a pat; rhs : 'a expr; body : 'a expr }
  | LocalVar of local_ident
  | GlobalVar of global_ident
  | Ascription of { e : 'a expr; typ : 'a ty }
  (* Macro *)
  | MacroInvokation of {
      macro : global_ident;
      args : string;
      witness : 'a macro;
    }
  (* Mut *)
  | Assign of { lhs : 'a lhs; e : 'a expr; witness : 'a mutable_variable }
  (* Loop *)
  | Loop of { body : 'a expr; label : string option; witness : 'a loop }
  (* ControlFlow *)
  | Break of {
      e : 'a expr option;
      label : string option;
      witness : 'a early_exit;
    }
  | Return of { e : 'a expr option; witness : 'a early_exit }
  | Continue of { label : string option; witness : 'a early_exit }
  (* Mem *)
  | Borrow of { kind : 'a borrow_kind; e : 'a expr }
  (* Raw borrow *)
  | AddressOf of {
      mut : 'a mutable_pointer mutability;
      e : 'a expr;
      witness : 'a raw_pointer;
    }
  | MonadicNode of { (* todo *) witness : 'a monadic }

and 'a expr = ('a, 'a expr') decorated

and 'a lhs =
  | FieldAccessor of { e : 'a expr; field : string }
  | ArrayAccessor of { e : 'a expr; index : 'a expr }
  | LhsLocalVar of LocalIdent.t
  constraint unit = 'a features_phantom

and 'a arm' = { pat : 'a pat; body : 'a expr }

and 'a arm = 'a arm' spanned constraint unit = 'a features_phantom
[@@deriving
  visitors
    { variety = "reduce"; name = "expr_reduce"; ancestors = [ "reduce_base" ] }]

type 'a param = { pat : 'a pat; typ : 'a ty; typ_span : span option }
[@@deriving visitors { variety = "reduce" }]

type 'a item' =
  | Fn of {
      name : global_ident;
      generics : unit;
      body : 'a expr;
      params : 'a param list;
    }
  | NotImplementedYet

and 'a item = {
  v : 'a item';
  span : span;
}
  constraint unit = 'a features_phantom
[@@deriving visitors { variety = "reduce" }]

type full =
  < as_pattern : on
  ; early_exit : on
  ; loop : on
  ; macro : on
  ; mem : on
  ; monadic : off
  ; mutable_borrow : on
  ; mutable_pointer : on
  ; mutable_reference : on
  ; mutable_variable : on
  ; raw_pointer : on
  ; reference : on
  ; slice : on >
