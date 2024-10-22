open! Prelude

type todo = string [@@deriving show, yojson, hash, compare, sexp, hash, eq]
type span = Span.t [@@deriving show, yojson, hash, compare, sexp, hash, eq]

type concrete_ident = Concrete_ident.t
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type logical_op = And | Or

and primitive_ident = Deref | Cast | LogicalOp of logical_op
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

module Global_ident = struct
  module T = struct
    type t =
      [ `Concrete of concrete_ident
      | `Primitive of primitive_ident
      | `TupleType of int
      | `TupleCons of int
      | `TupleField of int * int
      | `Projector of [ `Concrete of concrete_ident | `TupleField of int * int ]
      ]
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]
  end

  module M = struct
    include Base.Comparator.Make (T)
    include T
  end

  include M
  module Map = Map.M (M)

  let of_name kind n = `Concrete (Concrete_ident.of_name kind n)

  let eq_name name (x : t) : bool =
    match x with `Concrete x -> Concrete_ident.eq_name name x | _ -> false

  let to_string : t -> string = [%show: t]
end

type global_ident = Global_ident.t
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type attr_kind =
  | Tool of { path : string; tokens : string }
  | DocComment of { kind : doc_comment_kind; body : string }

and attr = { kind : attr_kind; span : span }
and doc_comment_kind = DCKLine | DCKBlock
and attrs = attr list [@@deriving show, yojson, hash, compare, sexp, hash, eq]

type local_ident = Local_ident.t
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type size = S8 | S16 | S32 | S64 | S128 | SSize
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

let int_of_size = function
  | S8 -> Some 8
  | S16 -> Some 16
  | S32 -> Some 32
  | S64 -> Some 64
  | S128 -> Some 128
  | _ -> None

let string_of_size = int_of_size >> Option.map ~f:Int.to_string

type signedness = Signed | Unsigned
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type int_kind = { size : size; signedness : signedness }
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

let show_int_kind { size; signedness } =
  (match signedness with Signed -> "i" | Unsigned -> "u")
  ^ (int_of_size size
    |> Option.map ~f:Int.to_string
    |> Option.value ~default:"size")

type float_kind = F16 | F32 | F64 | F128
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

let show_float_kind = function
  | F16 -> "f16"
  | F32 -> "f32"
  | F64 -> "f64"
  | F128 -> "f128"

type literal =
  | String of string
  | Char of char
  | Int of { value : string; negative : bool; kind : int_kind }
  | Float of { value : string; negative : bool; kind : float_kind }
  | Bool of bool
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

type 'mut_witness mutability = Mutable of 'mut_witness | Immutable
[@@deriving show, yojson, hash, compare, sexp, hash, eq]

module Make =
functor
  (F : Features.T)
  ->
  struct
    type safety_kind = Safe | Unsafe of F.unsafe
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type borrow_kind = Shared | Unique | Mut of F.mutable_reference
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type binding_mode = ByValue | ByRef of (borrow_kind * F.reference)
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type ty =
      | TBool
      | TChar
      | TInt of int_kind
      | TFloat of float_kind
      | TStr
      | TApp of { ident : global_ident; args : generic_value list }
      | TArray of { typ : ty; length : expr }
      | TSlice of { witness : F.slice; ty : ty }
      | TRawPointer of { witness : F.raw_pointer } (* todo *)
      | TRef of {
          witness : F.reference;
          region : todo;
          typ : ty;
          mut : F.mutable_reference mutability;
        }
      | TParam of local_ident
      | TArrow of ty list * ty
      | TAssociatedType of { impl : impl_expr; item : concrete_ident }
      | TOpaque of concrete_ident
      | TDyn of { witness : F.dyn; goals : dyn_trait_goal list }

    and generic_value =
      | GLifetime of { lt : todo; witness : F.lifetime }
      | GType of ty
      | GConst of expr

    and impl_expr = { kind : impl_expr_kind; goal : trait_goal }

    and impl_expr_kind =
      | Self
      | Concrete of trait_goal
      | LocalBound of { id : string }
      | Parent of { impl : impl_expr; ident : impl_ident }
      | Projection of {
          impl : impl_expr;
          item : concrete_ident;
          ident : impl_ident;
        }
      | ImplApp of { impl : impl_expr; args : impl_expr list }
      | Dyn
      | Builtin of trait_goal

    and trait_goal = { trait : concrete_ident; args : generic_value list }
    (** A fully applied trait: [Foo<SomeTy, T0, ..., Tn>] (or
      `SomeTy: Foo<T0, ..., Tn>`). An `impl_expr` "inhabits" a
      `trait_goal`. *)

    and dyn_trait_goal = {
      trait : concrete_ident;
      non_self_args : generic_value list;
    }
    (** A dyn trait: [Foo<_, T0, ..., Tn>]. The generic arguments are known 
      but the actual type implementing the trait is known only dynamically. *)

    and impl_ident = { goal : trait_goal; name : string }
    (** An impl identifier [{goal; name}] can be:
          {ul
              {- An in-scope variable [name] that inhabits [goal].}
              {- A field of some other impl expression [i]: [i.name] inhabits [goal]. This corresponds to parent bounds or associated type bounds.}
              {- An argument that introduces a variable [name] that inhabits [goal].}
          }
      *)

    and projection_predicate = {
      impl : impl_expr;
      assoc_item : concrete_ident;
      typ : ty;
    }
    (** Expresses a constraints over an associated type.
        For instance:
        [
        fn f<T : Foo<S = String>>(...)
                    ^^^^^^^^^^
        ]
        (provided the trait `Foo` has an associated type `S`).
      *)

    (* TODO: ADD SPAN! *)
    and pat' =
      | PWild
      | PAscription of { typ : ty; typ_span : span; pat : pat }
      | PConstruct of {
          constructor : global_ident;
          is_record : bool; (* are fields named? *)
          is_struct : bool; (* a struct has one constructor *)
          fields : field_pat list;
        }
      (* An or-pattern, e.g. `p | q`.
         Invariant: `List.length subpats >= 2`. *)
      | POr of { subpats : pat list }
      | PArray of { args : pat list }
      | PDeref of { subpat : pat; witness : F.reference }
      | PConstant of { lit : literal }
      | PBinding of {
          mut : F.mutable_variable mutability;
          mode : binding_mode;
          var : local_ident;
          typ : ty;
          subpat : (pat * F.as_pattern) option;
        }

    and pat = { p : pat'; span : span; typ : ty }
    and field_pat = { field : global_ident; pat : pat }

    and expr' =
      (* pure fragment *)
      | If of { cond : expr; then_ : expr; else_ : expr option }
      | App of {
          f : expr;
          args : expr list (* ; f_span: span *);
          generic_args : generic_value list;
          bounds_impls : impl_expr list;
          trait : (impl_expr * generic_value list) option;
        }
      | Literal of literal
      | Array of expr list
      | Construct of {
          constructor : global_ident;
          is_record : bool; (* are fields named? *)
          is_struct : bool; (* a struct has one constructor *)
          fields : (global_ident * expr) list;
          base : (expr * F.construct_base) option;
        }
      | Match of { scrutinee : expr; arms : arm list }
      | Let of {
          monadic : (supported_monads * F.monadic_binding) option;
          lhs : pat;
          rhs : expr;
          body : expr;
        }
      | Block of { e : expr; safety_mode : safety_kind; witness : F.block }
        (* Corresponds to `{e}`: this is important for places *)
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
      | Break of { e : expr; label : string option; witness : F.break * F.loop }
      | Return of { e : expr; witness : F.early_exit }
      | QuestionMark of { e : expr; return_typ : ty; witness : F.question_mark }
          (** The expression `e?`. In opposition to Rust, no implicit
      coercion is applied on the (potential) error payload of
      `e`. Coercion should be made explicit within `e`. *)
      | Continue of {
          e : (expr * F.state_passing_loop) option;
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
      | EffectAction of { action : F.monadic_action; argument : expr }
      | Quote of quote
          (** A quotation is an inlined piece of backend code
              interleaved with Rust code *)

    and expr = { e : expr'; span : span; typ : ty }

    and quote = {
      contents :
        [ `Verbatim of string | `Expr of expr | `Pat of pat | `Typ of ty ] list;
      witness : F.quote;
    }

    and supported_monads =
      | MException of ty
          (** a exception monad, which we use to handle early returns *)
      | MResult of ty  (** the [Result] monad *)
      | MOption  (** the [Option] monad *)

    and loop_kind =
      | UnconditionalLoop
      | WhileLoop of { condition : expr; witness : F.while_loop }
      | ForLoop of { pat : pat; it : expr; witness : F.for_loop }
      | ForIndexLoop of {
          start : expr;
          end_ : expr;
          var : local_ident;
          var_typ : ty;
          witness : F.for_index_loop;
        }

    and loop_state = { init : expr; bpat : pat; witness : F.state_passing_loop }

    (* | WhileLoop of { *)
    (*     condition: expr; *)
    (*     witness : F.while_loop; *)
    (*   } *)

    (* TODO: LHS should be places or "compositions" of places, see [assignee expression] in https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions (issue #222) *)
    and lhs =
      | LhsLocalVar of { var : Local_ident.t; typ : ty }
      | LhsArbitraryExpr of { e : expr; witness : F.arbitrary_lhs }
      | LhsFieldAccessor of {
          e : lhs;
          typ : ty;
          (* TODO: change type (see #316) *)
          field : global_ident;
          witness : F.nontrivial_lhs;
        }
      | LhsArrayAccessor of {
          e : lhs;
          typ : ty;
          index : expr;
          witness : F.nontrivial_lhs;
        }

    (* A guard is a condition on a pattern like: *)
    (* match x {.. if guard => .., ..}*)
    and guard = { guard : guard'; span : span }

    (* Only if-let guards are supported for now but other variants like regular if *)
    (* could be added later (regular if guards are for now desugared as IfLet) *)
    and guard' = IfLet of { lhs : pat; rhs : expr; witness : F.match_guard }

    (* OCaml + visitors is not happy with `pat`... hence `arm_pat`... *)
    and arm' = { arm_pat : pat; body : expr; guard : guard option }

    and arm = { arm : arm'; span : span }
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type generic_param = {
      ident : local_ident;
      span : span;
      attrs : attrs;
      kind : generic_param_kind;
    }

    and generic_param_kind =
      | GPLifetime of { witness : F.lifetime }
      | GPType
      | GPConst of { typ : ty }

    and generic_constraint =
      | GCLifetime of todo * F.lifetime
      | GCType of impl_ident
      | GCProjection of projection_predicate
          (** Trait or lifetime constraints. For instance, `A` and `B` in
    `fn f<T: A + B>()`. *)
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type param = { pat : pat; typ : ty; typ_span : span option; attrs : attrs }

    and generics = {
      params : generic_param list;
      constraints : generic_constraint list;
    }

    and variant = {
      name : concrete_ident;
      arguments : (concrete_ident * ty * attrs) list;
      is_record : bool;
      attrs : attrs;
    }

    and item' =
      (* Todo: topological sort, rec bundles *)
      | Fn of {
          name : concrete_ident;
          generics : generics;
          body : expr;
          params : param list;
          safety : safety_kind;
        }
      | TyAlias of { name : concrete_ident; generics : generics; ty : ty }
      | Type of {
          name : concrete_ident;
          generics : generics;
          variants : variant list;
          is_struct : bool;
        }
      | IMacroInvokation of {
          macro : concrete_ident;
          argument : string;
          span : span;
          witness : F.macro;
        }
      | Trait of {
          name : concrete_ident;
          generics : generics;
          items : trait_item list;
          safety : safety_kind;
        }
      | Impl of {
          generics : generics;
          self_ty : ty;
          of_trait : concrete_ident * generic_value list;
          items : impl_item list;
          parent_bounds : (impl_expr * impl_ident) list;
          safety : safety_kind;
        }
      | Alias of { name : concrete_ident; item : concrete_ident }
          (** `Alias {name; item}` is basically a `use
              <item> as _;` where `name` is the renamed ident. *)
      | Use of {
          path : string list;
          is_external : bool;
          rename : string option;
        }
      | Quote of quote
      | HaxError of string
      | NotImplementedYet

    and item = { v : item'; span : span; ident : concrete_ident; attrs : attrs }

    and impl_item' =
      | IIType of { typ : ty; parent_bounds : (impl_expr * impl_ident) list }
      | IIFn of { body : expr; params : param list }

    and impl_item = {
      ii_span : span;
      ii_generics : generics;
      ii_v : impl_item';
      ii_ident : concrete_ident;
      ii_attrs : attrs;
    }

    and trait_item' =
      | TIType of impl_ident list
      | TIFn of ty
      | TIDefault of {
          params : param list;
          body : expr;
          witness : F.trait_item_default;
        }

    and trait_item = {
      (* TODO: why do I need to prefix by `ti_` here? I guess visitors fail or something *)
      ti_span : span;
      ti_generics : generics;
      ti_v : trait_item';
      ti_ident : concrete_ident;
      ti_attrs : attrs;
    }
    [@@deriving show, yojson, hash, compare, sexp, hash, eq]

    type modul = item list

    let make_hax_error_item (span : span) (ident : Concrete_ident.t)
        (s : string) : item =
      { v = HaxError s; span; ident; attrs = [] }

    (* module F = F *)
  end

module type T = sig
  type expr [@@deriving show, compare, yojson]
  type item' [@@deriving show, compare, yojson]

  type item = {
    v : item';
    span : span;
    ident : Concrete_ident.t;
    attrs : attrs;
  }
  [@@deriving show, compare, yojson]

  val make_hax_error_item : span -> Concrete_ident.t -> string -> item
end

module Rust = Make (Features.Rust)
module Full = Make (Features.Full)
