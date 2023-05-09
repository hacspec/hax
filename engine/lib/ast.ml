open Base
open Utils

module Non_empty_list = struct
  include Non_empty_list

  let t_of_yojson : (Yojson.Safe.t -> 'a) -> Yojson.Safe.t -> 'a t =
   fun f x -> list_of_yojson f x |> Non_empty_list.of_list_exn

  let yojson_of_t : ('a -> Yojson.Safe.t) -> 'a t -> Yojson.Safe.t =
   fun f x -> Non_empty_list.to_list x |> yojson_of_list f

  let t_of_sexp f s = List.t_of_sexp f s |> Non_empty_list.of_list_exn
  let sexp_of_t f x = Non_empty_list.to_list x |> List.sexp_of_t f
end

module Namespace = struct
  module U = struct
    module T = struct
      type t = string * string list
      [@@deriving show, eq, compare, sexp, hash, yojson]
    end

    include Base.Comparator.Make (T)
    include T
  end

  include U
  module Map = Map.M (U)
end

type todo = string
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "todo_reduce" },
    visitors { variety = "map"; name = "todo_map" }]

type loc = { col : int; line : int }
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "loc_reduce" },
    visitors { variety = "map"; name = "loc_map" }]

type span = Span of { file : string; hi : loc; lo : loc } | Dummy
[@@deriving
  yojson,
    eq,
    show,
    visitors
      { variety = "reduce"; name = "span_reduce"; ancestors = [ "loc_reduce" ] },
    visitors { variety = "map"; name = "span_map"; ancestors = [ "loc_map" ] }]

let show_span (_s : span) : string = "<span>"

let pp_span (fmt : Caml.Format.formatter) (s : span) : unit =
  Caml.Format.pp_print_string fmt @@ show_span s

let union_span (x : span) (y : span) : span =
  match (x, y) with
  | Dummy, _ | _, Dummy -> Dummy
  | Span x, Span y when String.(x.file <> y.file) ->
      failwith "TODO error: Bad span union"
  | Span { file; lo; _ }, Span { hi; _ } -> Span { file; lo; hi }

let union_spans : span list -> span =
  List.reduce ~f:union_span >> Option.value ~default:Dummy

type concrete_ident = { crate : string; path : string Non_empty_list.t }

and bin_op =
  | Add
  | Sub
  | Mul
  | Div
  | Rem
  | BitXor
  | BitAnd
  | BitOr
  | Shl
  | Shr
  | Eq
  | Lt
  | Le
  | Ne
  | Ge
  | Gt
  | Offset

and un_op = Not | Neg
and logical_op = And | Or

and primitive_ident =
  | Box
  | Deref
  | Cast
  | BinOp of bin_op
  | UnOp of un_op
  | LogicalOp of logical_op
[@@deriving
  show,
    yojson,
    compare,
    sexp,
    eq,
    visitors { variety = "reduce"; name = "primitive_ident_reduce" },
    visitors { variety = "map"; name = "primitive_ident_map" }]

let show_concrete_ident (s : concrete_ident) : string =
  s.crate ^ "::" ^ String.concat ~sep:"::" @@ Non_empty_list.to_list s.path

let pp_concrete_ident (fmt : Caml.Format.formatter) (s : concrete_ident) : unit
    =
  Caml.Format.pp_print_string fmt @@ show_concrete_ident s

module GlobalIdent = struct
  module T = struct
    type t =
      [ `Concrete of concrete_ident
      | `Primitive of primitive_ident
      | `TupleType of int
      | `TupleCons of int
      | `TupleField of int * int
      | `Projector of [ `Concrete of concrete_ident | `TupleField of int * int ]
      ]
    [@@deriving show, yojson, compare, sexp, eq]
  end

  module M = struct
    include Base.Comparator.Make (T)
    include T
  end

  include M
  module Map = Map.M (M)
  (* open Ppx_deriving_cmdliner_runtime *)

  let of_string : string -> [ `Error of string | `Ok of t ] =
    split_str ~on:"::" >> function
    | [] | [ _ ] -> `Error "A global ident is at least composed of two chunks"
    | crate :: path_hd :: path_tl ->
        `Ok (`Concrete Non_empty_list.{ crate; path = path_hd :: path_tl })

  let of_string_exn (s : string) : t =
    match of_string s with `Ok v -> v | `Error s -> failwith s

  let to_string : t -> string = [%show: t]

  let cmdliner_converter =
    (of_string, fun fmt t -> Caml.Format.fprintf fmt "%s" (to_string t))
end

type global_ident = (GlobalIdent.t[@visitors.opaque])
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "global_ident_reduce" },
    visitors { variety = "map"; name = "global_ident_map" }]

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
    visitors { variety = "reduce"; name = "local_ident_reduce" },
    visitors { variety = "map"; name = "local_ident_map" }]

type size = S8 | S16 | S32 | S64 | S128 | SSize
[@@deriving show, yojson, compare, eq]

type signedness = Signed | Unsigned [@@deriving show, yojson, compare, eq]

type int_kind = { size : size; signedness : signedness }
[@@deriving show, yojson, compare, eq]

type literal =
  | String of string
  | Char of char
  | Int of { value : string; kind : (int_kind[@visitors.opaque]) }
  | Float of float
  | Bool of bool
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "literal_reduce" },
    visitors { variety = "map"; name = "literal_map" }]

(* type 't spanned = { v : 't; span : span } [@@deriving show, yojson, eq, visitors { variety = "reduce"; name = "spanned_reduce" }] *)

type 'mut_witness mutability = Mutable of 'mut_witness | Immutable
[@@deriving show, yojson, eq]

type supported_monads = Option | Result | ControlFlow
[@@deriving
  show,
    yojson,
    eq,
    visitors { variety = "reduce"; name = "supported_monads_reduce" },
    visitors { variety = "map"; name = "supported_monads_map" }]

module Make =
functor
  (F : Features.T)
  ->
  struct
    type borrow_kind = Shared | Unique | Mut of F.mutable_reference
    [@@deriving
      show,
        yojson,
        eq,
        visitors { variety = "reduce"; name = "borrow_kind_reduce" },
        visitors { variety = "map"; name = "borrow_kind_map" }]

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
          },
        visitors
          {
            variety = "map";
            name = "binding_mode_map";
            ancestors = [ "borrow_kind_map" ];
          }]

    module DefaultClasses = Features.DefaultClasses (F)

    (* TODO: generate those classes automatically *)
    class virtual ['self] default_reduce_features =
      object (self : 'self)
        inherit [_] VisitorsRuntime.reduce
        method visit_span _ (_ : span) = self#zero
        method visit_literal _ (_ : literal) = self#zero
      end

    class virtual ['self] default_map_features =
      object (_self : 'self)
        inherit ['env] VisitorsRuntime.map
        method visit_span : 'env -> span -> span = Fn.const Fn.id
        method visit_literal : 'env -> literal -> literal = Fn.const Fn.id
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
                "DefaultClasses.default_reduce_features";
              ];
          },
        visitors
          {
            variety = "map";
            name = "ty_map";
            ancestors =
              [
                "global_ident_map";
                "todo_map";
                "local_ident_map";
                "default_map_features";
                "DefaultClasses.default_map_features";
              ];
          }]

    (* let show_ty (s : ty) : string = "<ty>" *)

    (* let pp_ty (fmt : Format.formatter) (s : ty) : unit = *)
    (*   Format.pp_print_string fmt @@ show_ty s *)

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
          },
        visitors
          {
            variety = "map";
            name = "pat_map";
            ancestors = [ "ty_map"; "binding_mode_map" ];
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
      | Loop of {
          body : expr;
          kind : loop_kind;
          state : loop_state option;
          label : string option;
          witness : F.loop;
        }
      (* ControlFlow *)
      | Break of { e : expr; label : string option; witness : F.loop }
      | Return of { e : expr; witness : F.early_exit }
      | Continue of {
          e : (F.state_passing_loop * expr) option;
          label : string option;
          witness : F.continue * F.loop;
        }
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

    and loop_kind =
      | UnconditionalLoop
      | ForLoop of {
          start : expr;
          end_ : expr;
          var : local_ident;
          var_typ : ty;
          witness : F.for_loop;
        }

    and loop_state = { init : expr; bpat : pat; witness : F.state_passing_loop }

    and lhs =
      | LhsLocalVar of { var : LocalIdent.t; typ : ty }
      | LhsArbitraryExpr of { e : expr; witness : F.arbitrary_lhs }
      | LhsFieldAccessor of { e : lhs; typ : ty; field : string }
      | LhsArrayAccessor of { e : lhs; typ : ty; index : expr }

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
          },
        visitors
          {
            variety = "map";
            name = "expr_map";
            ancestors = [ "pat_map"; "supported_monads_map" ];
          }]
    (* [@@deriving *)
    (*   visitors *)
    (* { variety = "reduce"; name = "expr_reduce"; ancestors = [ "reduce_base" ] }] *)

    type generic_param =
      | GPLifetime of {
          ident : local_ident;
          witness : (F.lifetime[@visitors.opaque]);
        }
      | GPType of { ident : local_ident; default : ty option }
      | GPConst of { ident : local_ident; typ : ty }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "generic_param_reduce";
            ancestors = [ "ty_reduce" ];
          },
        visitors
          {
            variety = "map";
            name = "generic_param_map";
            ancestors = [ "ty_map" ];
          }]

    type trait_ref = {
      trait : global_ident;
      args : generic_value list;
      bindings : todo list;
    }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "trait_ref_reduce";
            ancestors = [ "ty_reduce" ];
          },
        visitors
          { variety = "map"; name = "trait_ref_map"; ancestors = [ "ty_map" ] }]

    type generic_constraint =
      | GCLifetime of todo * (F.lifetime[@visitors.opaque])
      | GCType of { typ : ty; implements : trait_ref }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "generic_constraint_reduce";
            ancestors = [ "trait_ref_reduce" ];
          },
        visitors
          {
            variety = "map";
            name = "generic_constraint_map";
            ancestors = [ "trait_ref_map" ];
          }]

    type param = { pat : pat; typ : ty; typ_span : span option }

    and generics = {
      params : generic_param list;
      constraints : generic_constraint list;
    }

    and variant = { name : global_ident; arguments : (global_ident * ty) list }

    and item' =
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
      | IMacroInvokation of {
          macro : global_ident;
          argument : string;
          span : span;
          witness : F.macro;
        }
      | Trait of {
          name : global_ident;
          generics : generics;
          items : trait_item list;
        }
      | Impl of {
          generics : generics;
          self_ty : ty;
          of_trait : (global_ident * generic_value list) option;
          items : impl_item list;
        }
      | Use of {
          path : string list;
          is_external : bool;
          rename : string option;
        }
      | NotImplementedYet

    and item = {
      v : item';
      span : span;
      parent_namespace : (Namespace.t[@visitors.opaque]);
    }

    and impl_item' =
      | IIType of ty
      | IIFn of { body : expr; params : param list }

    and impl_item = {
      ii_span : span;
      ii_generics : generics;
      ii_v : impl_item';
      ii_name : string;
    }

    and trait_item' = TIType of trait_ref list | TIFn of ty

    and trait_item = {
      (* TODO: why do I need to prefix by `ti_` here? I guess visitors fail or something *)
      ti_span : span;
      ti_generics : generics;
      ti_v : trait_item';
      ti_name : string;
    }
    [@@deriving
      show,
        yojson,
        eq,
        visitors
          {
            variety = "reduce";
            name = "item_reduce";
            ancestors =
              [
                "generic_constraint_reduce";
                "expr_reduce";
                "generic_param_reduce";
              ];
          },
        visitors
          {
            variety = "map";
            name = "item_map";
            ancestors =
              [
                "generic_constraint_map";
                "expr_map";
                "ty_map";
                "generic_param_map";
              ];
          }]
    (* [@@deriving *)
    (*   show, yojson, eq, visitors { variety = "reduce"; name = "item_reduce" }, visitors { variety = "map"; name = "item_map" }] *)

    type modul = item list
  end

module type T = sig
  type item [@@deriving show, yojson]
end

module Rust = Make (Features.Rust)
