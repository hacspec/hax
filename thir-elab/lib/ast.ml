open Base
open Utils
module Non_empty_list = struct
  include Non_empty_list
  let t_of_yojson : (Yojson.Safe.t -> 'a) -> Yojson.Safe.t -> 'a t
      = fun f x -> list_of_yojson f x |> Non_empty_list.of_list_exn
  let yojson_of_t : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t
      = fun f x -> Non_empty_list.to_list x |> yojson_of_list f
end
module Bigint = struct
  include Bigint
  let t_of_yojson : Yojson.Safe.t -> t
      = fun x -> string_of_yojson x |> Bigint.of_string
  let yojson_of_t : t -> Yojson.Safe.t
      = fun x -> Bigint.to_string x |> yojson_of_string
end

type todo = string [@@deriving show, yojson, eq]
type loc = { col : int; line : int } [@@deriving show, yojson, eq]

type span = Span of { file : string; hi : loc; lo : loc } | Dummy
[@@deriving yojson, eq]
              
let show_span (s : span) : string = "<span>"

let pp_span (fmt : Format.formatter) (s : span) : unit =
  Format.pp_print_string fmt "<span>"

type concrete_ident = { crate : string; path : string Non_empty_list.t }
[@@deriving show, yojson, eq]

type primitive_ident =
  | Box
  | Deref
  | Cast
  | BinOp of (Raw_thir_ast.bin_op [@yojson.opaque])
  | UnOp of (Raw_thir_ast.un_op [@yojson.opaque])
  | LogicalOp of (Raw_thir_ast.logical_op [@yojson.opaque])
[@@deriving show, yojson, eq]

type global_ident =
  [ `Concrete of concrete_ident
  | `Primitive of primitive_ident
  | `Tuple of int
  | `TupleField of int * int
  | `Projector of [ `Concrete of concrete_ident | `TupleField of int * int ] ]
[@@deriving show, yojson, eq]

module LocalIdent = struct
  module T = struct
    type t = { name : string; id : int } [@@deriving show, yojson, compare, sexp, eq]
  end

  include Base.Comparator.Make (T)
  include T
end

type local_ident = LocalIdent.t [@@deriving show, yojson, compare, sexp, eq]
type size = S8 | S16 | S32 | S64 | S128 | SSize [@@deriving show, yojson, compare, eq]
type signedness = Signed | Unsigned [@@deriving show, yojson, compare, eq]

type int_kind = { size : size; signedness : signedness }
[@@deriving show, yojson, compare, eq]

type literal =
  | String of string
  | Char of char
  | Int of { value : Bigint.t; kind : int_kind }
  | Float of float
  | Bool of bool
[@@deriving show, yojson, eq]

type 't spanned = { v : 't; span : span } [@@deriving show, yojson, eq]

type 'mut_witness mutability = Mutable of 'mut_witness | Immutable [@@deriving show, yojson, eq]

module Make =
functor
  (F : Features.T)
  ->
  struct
    type borrow_kind = Shared | Unique | Mut of F.mutable_borrow [@@deriving show, yojson, eq]
    type binding_mode = ByValue | ByRef of borrow_kind[@@deriving show, yojson, eq]

    type ty =
      | Bool
      | Char
      | Int of int_kind
      | Float
      | Str
      | App of { ident : global_ident; args : generic_value list }
      | Array of { typ : ty; length : int }
      | Slice of { witness : F.slice; ty : ty }
      | RawPointer of { witness : F.raw_pointer } (* todo *)
      | Ref of {
          witness : F.reference;
          region : todo;
          typ : ty;
          mut : F.mutable_reference mutability;
        }
      | False
      | Param of local_ident
      | Arrow of ty list * ty
      | ProjectedAssociatedType of string

    and generic_value = Lifetime of {lt: todo; witness: F.lifetime} | Type of ty | Const of todo
      [@@deriving show, yojson, eq]
    (* [@@deriving visitors { variety = "reduce"; name = "ty_reduce"; ancestors = [] }] *)

    type 't decorated = { v : 't; span : span; typ : ty }
        [@@deriving show, yojson, eq]

    type pat' =
      | Wild
      | PatAscription of { typ : ty spanned; pat : pat }
      | Variant of { name : global_ident; args : field_pat list; record: bool }
      | PatArray of { args : pat list }
      | Deref of { subpat : pat }
      | Constant of { lit : literal }
      | Binding of {
          mut : F.mutable_variable mutability;
          mode : binding_mode;
          var : LocalIdent.t;
          typ : ty;
          subpat : (pat * F.as_pattern) option;
        }
                     [@@deriving show, yojson, eq]
    and pat = pat' decorated [@@deriving show, yojson, eq]
    and field_pat = { field : global_ident; pat : pat } [@@deriving show, yojson, eq]
    (* [@@deriving *)
    (*   visitors *)
    (*     { variety = "reduce"; name = "pat_reduce"; ancestors = [ "reduce_base" ] }] *)

    type expr' =
      (* pure fragment *)
      | If of { cond : expr; then_ : expr; else_ : expr option }
      | App of { f : expr; args : expr list (* ; f_span: span *) }
      | Literal of literal
      | Array of expr list
      | Construct of { constructor: global_ident
                     ; constructs_record: bool
                     ; fields : (global_ident * expr) list
                     ; base : expr option
                     }
      | Match of { scrutinee : expr; arms : arm list }
      | Let of { lhs : pat; rhs : expr; body : expr }
      | LocalVar of local_ident
      | GlobalVar of global_ident
      | Ascription of { e : expr; typ : ty }
      (* Macro *)
      | MacroInvokation of {
          macro : global_ident;
          args : string;
          witness : F.macro;
        }
      (* Mut *)
      | Assign of { lhs : lhs; e : expr; witness : F.mutable_variable }
      (* Loop *)
      | Loop of { body : expr; label : string option; witness : F.loop }
      (* ControlFlow *)
      | Break of {
          e : expr option;
          label : string option;
          witness : F.early_exit;
        }
      | Return of { e : expr option; witness : F.early_exit }
      | Continue of { label : string option; witness : F.early_exit }
      (* Mem *)
      | Borrow of { kind : borrow_kind; e : expr; witness: F.reference }
      (* Raw borrow *)
      | AddressOf of {
          mut : F.mutable_pointer mutability;
          e : expr;
          witness : F.raw_pointer;
        }
      | MonadicNode of { (* todo *) witness : F.monadic }
    [@@deriving show, yojson, eq]
            
    and expr = expr' decorated [@@deriving show, yojson, eq]

    and lhs =
      | FieldAccessor of { e : expr; field : string }
      | ArrayAccessor of { e : expr; index : expr }
      | LhsLocalVar of LocalIdent.t [@@deriving show, yojson, eq]

    and arm' = { pat : pat; body : expr } [@@deriving show, yojson, eq]
    and arm = arm' spanned [@@deriving show, yojson, eq]
    (* [@@deriving *)
    (*   visitors *)
    (* { variety = "reduce"; name = "expr_reduce"; ancestors = [ "reduce_base" ] }] *)

    type generic_param =
      | Lifetime of {ident: local_ident}
      | Type of {ident: local_ident; default: ty option}
      | Const of {ident: local_ident; typ: ty}
            [@@deriving show, yojson, eq]

    type trait_ref =
      {
        trait: global_ident;
        args: generic_value list;
        bindings: todo list;
      } [@@deriving show, yojson, eq]
    
    type generic_constraint =
      | Lifetime of todo
      | Type of { typ: ty; implements: trait_ref }
                  [@@deriving show, yojson, eq]
            
    type param = { pat : pat; typ : ty; typ_span : span option }
                   [@@deriving show, yojson, eq]
        
    type generics = {
        params: generic_param list;
        constraints: generic_constraint list;
      } [@@deriving show, yojson, eq]

    type variant = {
        name: global_ident;
        arguments: (global_ident * ty) list;
      } [@@deriving show, yojson, eq]
        
    type item' =
      (* Todo, topological sort, rec bundles *)
      | Fn of {
          name : global_ident;
          generics : generics;
          body : expr;
          params : param list;
        }
      | TyAlias of {
          name : global_ident;
          generics : generics;
          ty : ty;
        }
      | Type of {
          name: global_ident;
          generics : generics;
          variants: variant list
        }
      | NotImplementedYet

    and item = { v : item'; span : span }
        [@@deriving show, yojson, eq]
  end
