open Base
open Utils

module Non_empty_list = struct
  include Non_empty_list

  let t_of_yojson : (Yojson.Safe.t -> 'a) -> Yojson.Safe.t -> 'a t =
   fun f x -> list_of_yojson f x |> Non_empty_list.of_list_exn

  let yojson_of_t : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t =
   fun f x -> Non_empty_list.to_list x |> yojson_of_list f
end

module Bigint = struct
  include Bigint

  let t_of_yojson : Yojson.Safe.t -> t =
   fun x -> string_of_yojson x |> Bigint.of_string

  let yojson_of_t : t -> Yojson.Safe.t =
   fun x -> Bigint.to_string x |> yojson_of_string
end

type todo = string
[@@deriving
  show, yojson, eq, visitors { variety = "reduce"; name = "todo_reduce" }]

type loc = { col : int; line : int }
[@@deriving
  show, yojson, eq, visitors { variety = "reduce"; name = "loc_reduce" }]

type span =
  | Span of {
      file : (string[@yojson.opaque]);
      hi : (loc[@yojson.opaque]);
      lo : (loc[@yojson.opaque]);
    }
  | Dummy
[@@deriving
  yojson,
    eq,
    show,
    visitors
      { variety = "reduce"; name = "span_reduce"; ancestors = [ "loc_reduce" ] }]

let show_span (s : span) : string = "<span>"

let pp_span (fmt : Format.formatter) (s : span) : unit =
  Format.pp_print_string fmt "<span>"

type concrete_ident = { crate : string; path : string Non_empty_list.t }
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "concrete_ident_reduce" }]

type primitive_ident =
  | Box
  | Deref
  | Cast
  | BinOp of (Raw_thir_ast.bin_op[@yojson.opaque])
  | UnOp of (Raw_thir_ast.un_op[@yojson.opaque])
  | LogicalOp of (Raw_thir_ast.logical_op[@yojson.opaque])
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "primitive_ident_reduce" }]

module GlobalIdent = struct
  type t =
    [ `Concrete of concrete_ident
    | `Primitive of primitive_ident
    | `TupleType of int
    | `TupleCons of int
    | `TupleField of int * int
    | `Projector of [ `Concrete of concrete_ident | `TupleField of int * int ]
    ]
  [@@deriving show, yojson, eq]
end

type global_ident = (GlobalIdent.t[@visitors.opaque])
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "global_ident_reduce" }]

module LocalIdent = struct
  module T = struct
    type t = { name : string; id : int }
    [@@deriving show, yojson, compare, sexp, eq]
  end

  include Base.Comparator.Make (T)
  include T
end

type local_ident = (LocalIdent.t[@visitors.opaque])
[@@deriving
  show,
    yojson,
    compare,
    sexp,
    eq,
    visitors { variety = "reduce"; name = "local_ident_reduce" }]

type size = S8 | S16 | S32 | S64 | S128 | SSize
[@@deriving show, yojson, compare, eq]

type signedness = Signed | Unsigned [@@deriving show, yojson, compare, eq]

type int_kind = { size : size; signedness : signedness }
[@@deriving show, yojson, compare, eq]

type literal =
  | String of string
  | Char of char
  | Int of { value : Bigint.t; kind : (int_kind[@visitors.opaque]) }
  | Float of float
  | Bool of bool
[@@deriving
  show, yojson, eq, visitors { variety = "reduce"; name = "literal_reduce" }]

(* type 't spanned = { v : 't; span : span } [@@deriving show, yojson, eq, visitors { variety = "reduce"; name = "spanned_reduce" }] *)

type 'mut_witness mutability = Mutable of 'mut_witness | Immutable
[@@deriving show, yojson, eq]

type supported_monads = Option | Result | ControlFlow
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "supported_monads_reduce" }]

module Make =
functor
  (F : Features.T)
  ->
  struct
    type borrow_kind = Shared | Unique | Mut of F.mutable_borrow
    [@@deriving
      show,
        yojson,
        eq,
        visitors { variety = "reduce"; name = "borrow_kind_reduce" }]

    type binding_mode =
      | ByValue
      | ByRef of (borrow_kind * (F.reference[@visitors.opaque]))
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "binding_mode_reduce";
            ancestors = [ "borrow_kind_reduce" ];
          }]

    class virtual ['self] default_reduce_features =
      object (self : 'self)
        inherit [_] VisitorsRuntime.reduce

        (* todo: here I force unit to get rid of generalization issues
           Instead, TODO: split this class into multiple
        *)
        method visit_loop () (_ : F.loop) = self#zero
        method visit_continue () (_ : F.continue) = self#zero
        method visit_mutable_variable () (_ : F.mutable_variable) = self#zero
        method visit_mutable_reference () (_ : F.mutable_reference) = self#zero
        method visit_mutable_pointer () (_ : F.mutable_pointer) = self#zero
        method visit_mutable_borrow () (_ : F.mutable_borrow) = self#zero
        method visit_reference () (_ : F.reference) = self#zero
        method visit_slice () (_ : F.slice) = self#zero
        method visit_raw_pointer () (_ : F.raw_pointer) = self#zero
        method visit_early_exit () (_ : F.early_exit) = self#zero
        method visit_macro () (_ : F.macro) = self#zero
        method visit_as_pattern () (_ : F.as_pattern) = self#zero
        method visit_lifetime () (_ : F.lifetime) = self#zero
        method visit_monadic_action () (_ : F.monadic_action) = self#zero
        method visit_monadic_binding () (_ : F.monadic_binding) = self#zero

        (* move somewhere else *)
        method visit_span _ (_ : span) = self#zero
        method visit_literal _ (_ : literal) = self#zero
      end

    type ty =
      | TBool
      | TChar
      | TInt of (int_kind[@visitors.opaque])
      | TFloat
      | TStr
      | TApp of { ident : global_ident; args : generic_value list }
      | TArray of { typ : ty; length : int }
      | TSlice of { witness : F.slice; ty : ty }
      | TRawPointer of { witness : F.raw_pointer } (* todo *)
      | TRef of {
          witness : F.reference;
          region : todo;
          typ : ty;
          mut : (F.mutable_reference mutability[@visitors.opaque]);
        }
      | TFalse
      | TParam of local_ident
      | TArrow of ty list * ty
      | TProjectedAssociatedType of string

    and generic_value =
      | GLifetime of { lt : todo; witness : F.lifetime }
      | GType of ty
      | GConst of todo
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "ty_reduce";
            ancestors =
              [
                "global_ident_reduce";
                "todo_reduce";
                "local_ident_reduce";
                "default_reduce_features";
              ];
          }]
    (* [@@deriving visitors { variety = "reduce"; name = "ty_reduce"; ancestors = [] }] *)

    (* type 't decorated = { v : 't; span : span; typ : ty } *)
    (*     [@@deriving show, yojson, eq, visitors { variety = "reduce"; name = "decorated_reduce"; polymorphic = false }] *)

    type pat' =
      | PWild
      | PAscription of { typ : ty; typ_span : span; pat : pat }
      | PConstruct of {
          name : global_ident;
          args : field_pat list;
          record : bool;
        }
      | PArray of { args : pat list }
      | PDeref of { subpat : pat; witness : F.reference }
      | PConstant of { lit : literal }
      | PBinding of {
          mut : (F.mutable_variable mutability[@visitors.opaque]);
          mode : binding_mode;
          var : local_ident;
          typ : ty;
          subpat : (pat * F.as_pattern) option;
        }

    and pat = { p : pat'; span : span; typ : ty }

    and field_pat = { field : global_ident; pat : pat }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "pat_reduce";
            ancestors = [ "ty_reduce"; "binding_mode_reduce" ];
          }]

    type expr' =
      (* pure fragment *)
      | If of { cond : expr; then_ : expr; else_ : expr option }
      | App of { f : expr; args : expr list (* ; f_span: span *) }
      | Literal of literal
      | Array of expr list
      | Construct of {
          constructor : global_ident;
          constructs_record : bool;
          fields : (global_ident * expr) list;
          base : expr option;
        }
      | Match of { scrutinee : expr; arms : arm list }
      | Let of {
          monadic : (supported_monads * F.monadic_binding) option;
          lhs : pat;
          rhs : expr;
          body : expr;
        }
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
      | Break of { e : expr; label : string option; witness : F.loop }
      | Return of { e : expr; witness : F.early_exit }
      | Continue of { label : string option; witness : F.continue * F.loop }
      (* Mem *)
      | Borrow of { kind : borrow_kind; e : expr; witness : F.reference }
      (* Raw borrow *)
      | AddressOf of {
          mut : F.mutable_pointer mutability;
          e : expr;
          witness : F.raw_pointer;
        }
      | Closure of { params : pat list; body : expr; captures : expr list }
      | MonadicAction of { action : F.monadic_action; argument : expr }

    and expr = { e : expr'; span : span; typ : ty }

    and lhs =
      | FieldAccessor of { e : expr; field : string }
      | ArrayAccessor of { e : expr; index : expr }
      | LhsLocalVar of LocalIdent.t

    and arm' = { pat : pat; body : expr }

    and arm = { arm : arm'; span : span }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "expr_reduce";
            ancestors = [ "pat_reduce"; "supported_monads_reduce" ];
          }]
    (* [@@deriving *)
    (*   visitors *)
    (* { variety = "reduce"; name = "expr_reduce"; ancestors = [ "reduce_base" ] }] *)

    type generic_param =
      | Lifetime of {
          ident : local_ident;
          witness : (F.lifetime[@visitors.opaque]);
        }
      | Type of { ident : local_ident; default : ty option }
      | Const of { ident : local_ident; typ : ty }
    [@@deriving
      show,
        yojson,
        eq,
        visitors { variety = "reduce"; name = "generic_param_reduce" }]

    type trait_ref = {
      trait : global_ident;
      args : generic_value list;
      bindings : todo list;
    }
    [@@deriving show, yojson, eq]

    type generic_constraint =
      | Lifetime of todo * (F.lifetime[@visitors.opaque])
      | Type of { typ : ty; implements : trait_ref }
    [@@deriving show, yojson, eq]

    type param = { pat : pat; typ : ty; typ_span : span option }
    [@@deriving show, yojson, eq]

    type generics = {
      params : generic_param list;
      constraints : generic_constraint list;
    }
    [@@deriving show, yojson, eq]

    type variant = { name : global_ident; arguments : (global_ident * ty) list }
    [@@deriving show, yojson, eq]

    type item' =
      (* Todo, topological sort, rec bundles *)
      | Fn of {
          name : global_ident;
          generics : generics;
          body : expr;
          params : param list;
        }
      | TyAlias of { name : global_ident; generics : generics; ty : ty }
      | Type of {
          name : global_ident;
          generics : generics;
          variants : variant list;
          record : bool;
        }
      | NotImplementedYet

    and item = { v : item'; span : span }
    [@@deriving
      show, yojson, eq, visitors { variety = "reduce"; name = "item_reduce" }]

    type modul = item list
  end
