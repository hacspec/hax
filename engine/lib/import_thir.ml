module Thir = struct
  include Types

  type item = item_for__decorated_for__expr_kind
  type item_kind = item_kind_for__decorated_for__expr_kind
  type impl_item = impl_item_for__decorated_for__expr_kind
  type impl_item_kind = impl_item_kind_for__decorated_for__expr_kind
  type generics = generics_for__decorated_for__expr_kind
  type trait_item_kind = trait_item_kind_for__decorated_for__expr_kind
  type generic_param = generic_param_for__decorated_for__expr_kind
  type generic_param_kind = generic_param_kind_for__decorated_for__expr_kind
  type trait_item = trait_item_for__decorated_for__expr_kind
end

open! Prelude
open Diagnostics

let assertion_failure (span : Thir.span list) (details : string) =
  let kind = T.AssertionFailure { details } in
  Diagnostics.SpanFreeError.raise ~span ThirImport kind

let unimplemented ~issue_id (span : Thir.span list) (details : string) =
  let kind =
    T.Unimplemented
      {
        issue_id = Some (MyInt64.of_int_exn issue_id);
        details = String.(if details = "" then None else Some details);
      }
  in
  Diagnostics.SpanFreeError.raise ~span ThirImport kind

module Ast = struct
  include Ast
  include Rust
end

module U = Ast_utils.Make (Features.Rust)
module W = Features.On
open Ast

let def_id kind (def_id : Thir.def_id) : global_ident =
  `Concrete (Concrete_ident.of_def_id kind def_id)

let local_ident kind (ident : Thir.local_ident) : local_ident =
  {
    name = ident.name;
    id = Local_ident.mk_id kind (Int.of_string ident.id.local_id);
  }

let int_ty_to_size : Thir.int_ty -> size = function
  | Isize -> SSize
  | I8 -> S8
  | I16 -> S16
  | I32 -> S32
  | I64 -> S64
  | I128 -> S128

let uint_ty_to_size : Thir.uint_ty -> size = function
  | Usize -> SSize
  | U8 -> S8
  | U16 -> S16
  | U32 -> S32
  | U64 -> S64
  | U128 -> S128

let c_int_ty (ty : Thir.int_ty) : int_kind =
  { size = int_ty_to_size ty; signedness = Signed }

let c_uint_ty (ty : Thir.uint_ty) : int_kind =
  { size = uint_ty_to_size ty; signedness = Unsigned }

let csafety (safety : Types.safety) : safety_kind =
  match safety with Safe -> Safe | Unsafe -> Unsafe W.unsafe

let c_mutability (witness : 'a) : bool -> 'a Ast.mutability = function
  | true -> Mutable witness
  | false -> Immutable

let c_borrow_kind span : Thir.borrow_kind -> borrow_kind = function
  | Shared -> Shared
  | Fake _ ->
      assertion_failure [ span ]
        "Got a shallow borrow node (`BorrowKind::Fake`). Those are generated \
         by the borrow checker and should be discarded after borrow checking: \
         we should never see such borrows."
  | Mut _ -> Mut W.mutable_reference

let c_binding_mode : Thir.by_ref -> binding_mode = function
  | No -> ByValue
  | Yes true -> ByRef (Mut W.mutable_reference, W.reference)
  | Yes false -> ByRef (Shared, W.reference)

let unit_typ : ty = TApp { ident = `TupleType 0; args = [] }

let unit_expr span : expr =
  { typ = unit_typ; span; e = Ast.GlobalVar (`TupleCons 0) }

let wild_pat span : ty -> pat = fun typ -> { typ; span; p = PWild }

let c_logical_op : Thir.logical_op -> logical_op = function
  | And -> And
  | Or -> Or

let c_attr (attr : Thir.attribute) : attr =
  let kind =
    match attr.kind with
    | DocComment (kind, body) ->
        let kind =
          match kind with Thir.Line -> DCKLine | Thir.Block -> DCKBlock
        in
        DocComment { kind; body }
    | Normal
        {
          item =
            { args = Eq (_, Hir { symbol; _ }); path = "doc"; tokens = None; _ };
          tokens = None;
        } ->
        DocComment { kind = DCKLine; body = symbol }
        (* Looks for `#[doc = "something"]` *)
    | Normal { item = { args; path; tokens = subtokens; _ }; tokens } ->
        let args_tokens =
          match args with Delimited { tokens; _ } -> Some tokens | _ -> None
        in
        let tokens =
          let ( || ) = Option.first_some in
          Option.value ~default:"" (args_tokens || tokens || subtokens)
        in
        Tool { path; tokens }
  in
  { kind; span = Span.of_thir attr.span }

let c_attrs : Thir.attribute list -> attrs = List.map ~f:c_attr

let c_item_attrs (attrs : Thir.item_attributes) : attrs =
  (* TODO: This is a quite coarse approximation, we need to reflect
     that parent/self structure in our AST. See
     https://github.com/hacspec/hax/issues/123. *)
  let self = c_attrs attrs.attributes in
  let parent =
    c_attrs attrs.parent_attributes
    |> List.filter ~f:([%matches? ({ kind = DocComment _; _ } : attr)] >> not)
    |> (* Repeating associateditem or uid is harmful, same for comments *)
    List.filter ~f:(fun payload ->
        match Attr_payloads.payloads [ payload ] with
        | [ ((Uid _ | AssociatedItem _), _) ] -> false
        | _ -> true)
  in
  self @ parent

type extended_literal =
  | EL_Lit of literal
  | EL_U8Array of literal list (* EL_U8Array only encodes arrays of [u8]s *)

let c_lit' span negative (lit : Thir.lit_kind) (ty : ty) : extended_literal =
  let mk l = EL_Lit l in
  let mku8 (n : int) =
    let kind = { size = S8; signedness = Unsigned } in
    Int { value = Int.to_string n; kind; negative = false }
  in
  let error kind =
    assertion_failure [ span ]
      ("[import_thir:literal] got a " ^ kind ^ " literal, expected " ^ kind
     ^ " type, got type ["
      ^ [%show: ty] ty
      ^ "] instead.")
  in
  match lit with
  | Err _ ->
      assertion_failure [ span ]
        "[import_thir:literal] got an error literal: this means the Rust \
         compiler or Hax's frontend probably reported errors above."
  | Str (str, _) -> mk @@ String str
  | CStr (l, _) | ByteStr (l, _) -> EL_U8Array (List.map ~f:mku8 l)
  | Byte n -> mk @@ mku8 n
  | Char s -> mk @@ Char s
  | Int (value, _kind) ->
      mk
      @@ Int
           {
             value;
             negative;
             kind = (match ty with TInt k -> k | _ -> error "integer");
           }
  | Float (value, _kind) ->
      mk
      @@ Float
           {
             value;
             negative;
             kind = (match ty with TFloat k -> k | _ -> error "float");
           }
  | Bool b -> mk @@ Bool b

let c_lit span neg (lit : Thir.spanned_for__lit_kind) : ty -> extended_literal =
  c_lit' span neg lit.node

let resugar_index_mut (e : expr) : (expr * expr) option =
  match (U.unbox_underef_expr e).e with
  | App
      {
        f = { e = GlobalVar (`Concrete meth); _ };
        args = [ { e = Borrow { e = x; _ }; _ }; index ];
        generic_args = _ (* TODO: see issue #328 *);
        trait = _ (* TODO: see issue #328 *);
        bounds_impls = _;
      }
    when Concrete_ident.eq_name Core__ops__index__IndexMut__index_mut meth ->
      Some (x, index)
  | App
      {
        f = { e = GlobalVar (`Concrete meth); _ };
        args = [ x; index ];
        generic_args = _ (* TODO: see issue #328 *);
        trait = _ (* TODO: see issue #328 *);
        bounds_impls = _;
      }
    when Concrete_ident.eq_name Core__ops__index__Index__index meth ->
      Some (x, index)
  | _ -> None

(** Name for the cast function from an ADT to its discriminant *)
let cast_name_for_type typ_name =
  Concrete_ident.Create.map_last ~f:(fun s -> s ^ "_cast_to_repr") typ_name

module type EXPR = sig
  val c_expr : Thir.decorated_for__expr_kind -> expr
  val c_expr_drop_body : Thir.decorated_for__expr_kind -> expr
  val c_ty : Thir.span -> Thir.ty -> ty
  val c_generic_value : Thir.span -> Thir.generic_arg -> generic_value
  val c_generics : Thir.generics -> generics
  val c_param : Thir.span -> Thir.param -> param
  val c_fn_params : Thir.span -> Thir.param list -> param list
  val c_trait_item' : Thir.trait_item -> Thir.trait_item_kind -> trait_item'
  val c_trait_ref : Thir.span -> Thir.trait_ref -> trait_goal
  val c_impl_expr : Thir.span -> Thir.impl_expr -> impl_expr
  val c_clause : Thir.span -> Thir.clause -> generic_constraint option
end

(* BinOp to [core::ops::*] overloaded functions *)

module Make (CTX : sig
  val is_core_item : bool
end) : EXPR = struct
  let c_binop (op : Thir.bin_op) (lhs : expr) (rhs : expr) (span : span)
      (typ : ty) =
    let overloaded_names_of_binop : Thir.bin_op -> Concrete_ident.name =
      function
      | Add -> Core__ops__arith__Add__add
      | Sub -> Core__ops__arith__Sub__sub
      | Mul -> Core__ops__arith__Mul__mul
      | Div -> Core__ops__arith__Div__div
      | Rem -> Core__ops__arith__Rem__rem
      | BitXor -> Core__ops__bit__BitXor__bitxor
      | BitAnd -> Core__ops__bit__BitAnd__bitand
      | BitOr -> Core__ops__bit__BitOr__bitor
      | Shl -> Core__ops__bit__Shl__shl
      | Shr -> Core__ops__bit__Shr__shr
      | Lt -> Core__cmp__PartialOrd__lt
      | Le -> Core__cmp__PartialOrd__le
      | Ne -> Core__cmp__PartialEq__ne
      | Ge -> Core__cmp__PartialOrd__ge
      | Gt -> Core__cmp__PartialOrd__gt
      | Eq -> Core__cmp__PartialEq__eq
      | AddWithOverflow | SubWithOverflow | MulWithOverflow ->
          assertion_failure (Span.to_thir span)
            "Overflowing binary operators are not suppored"
      | Cmp ->
          assertion_failure (Span.to_thir span)
            "`Cmp` binary operator is not suppored"
      | Offset -> Core__ptr__const_ptr__Impl__offset
    in
    let primitive_names_of_binop : Thir.bin_op -> Concrete_ident.name = function
      | Add -> Rust_primitives__u128__add
      | Sub -> Rust_primitives__u128__sub
      | Mul -> Rust_primitives__u128__mul
      | Div -> Rust_primitives__u128__div
      | Rem -> Rust_primitives__u128__rem
      | BitXor -> Rust_primitives__u128__bit_xor
      | BitAnd -> Rust_primitives__u128__bit_and
      | BitOr -> Rust_primitives__u128__bit_or
      | Shl -> Rust_primitives__u128__shl
      | Shr -> Rust_primitives__u128__shr
      | Lt -> Rust_primitives__u128__lt
      | Le -> Rust_primitives__u128__le
      | Ne -> Rust_primitives__u128__ne
      | Ge -> Rust_primitives__u128__ge
      | Gt -> Rust_primitives__u128__gt
      | Eq -> Rust_primitives__u128__eq
      | AddWithOverflow | SubWithOverflow | MulWithOverflow ->
          assertion_failure (Span.to_thir span)
            "Overflowing binary operators are not suppored"
      | Cmp ->
          assertion_failure (Span.to_thir span)
            "`Cmp` binary operator is not suppored"
      | Offset -> Rust_primitives__offset
    in
    let name =
      if CTX.is_core_item then
        let assert_type_eq t1 t2 =
          if not (U.ty_equality t1 t2) then
            assertion_failure (Span.to_thir span)
              ("Binary operation: expected LHS and RHS to have the same type, \
                instead LHS has type ["
              ^ [%show: ty] t1
              ^ "] while RHS has type ["
              ^ [%show: ty] t2
              ^ "]")
        in
        let int =
          ("int", function TInt k -> Some (show_int_kind k) | _ -> None)
        in
        let float =
          ("float", function TFloat k -> Some (show_float_kind k) | _ -> None)
        in
        let bool = ("bool", function TBool -> Some "bool" | _ -> None) in
        let concat_tup sep (x, y) = x ^ sep ^ y in
        let ( <*> ) (x, f) (y, g) =
          ( x ^ "*" ^ y,
            f *** g >> uncurry Option.both >> Option.map ~f:(concat_tup "_") )
        in
        let both (e, f) =
          ( e ^ "*" ^ e,
            fun (t1, t2) ->
              assert_type_eq t1 t2;
              f t1 )
        in
        let ( <|> ) (x, f) (y, g) =
          (x ^ " or" ^ y, fun v -> match f v with None -> g v | v -> v)
        in
        let name = primitive_names_of_binop op in
        let expected, f =
          match op with
          | Add | Sub | Mul | AddWithOverflow | SubWithOverflow
          | MulWithOverflow | Div ->
              both int <|> both float
          | Rem | Cmp -> both int
          | BitXor | BitAnd | BitOr -> both int <|> both bool
          | Shl | Shr -> int <*> int
          | Lt | Le | Ne | Ge | Gt -> both int <|> both float
          | Eq -> both int <|> both float <|> both bool
          | Offset -> ("", fun _ -> Some "")
        in
        match f (lhs.typ, rhs.typ) with
        | Some with_ ->
            Concrete_ident.of_name Value name
            |> Concrete_ident.map_path_strings ~f:(function
                 | "u128" -> with_
                 | s -> s)
        | None ->
            assertion_failure (Span.to_thir span)
              ("Binary operation: expected " ^ expected ^ " type, got "
              ^ [%show: ty] lhs.typ)
      else Concrete_ident.of_name Value @@ overloaded_names_of_binop op
    in
    U.call' (`Concrete name) [ lhs; rhs ] span typ

  let rec c_expr (e : Thir.decorated_for__expr_kind) : expr =
    try c_expr_unwrapped e
    with Diagnostics.SpanFreeError.Exn (Data (ctx, kind)) ->
      let typ : ty =
        try c_ty e.span e.ty
        with Diagnostics.SpanFreeError.Exn _ -> U.hax_failure_typ
      in
      let span = Span.of_thir e.span in
      U.hax_failure_expr' span typ (ctx, kind)
        ([%show: Thir.decorated_for__expr_kind] e)

  (** Extracts an expression as the global name `dropped_body`: this
      drops the computational part of the expression, but keeps a
      correct type and span. *)
  and c_expr_drop_body (e : Thir.decorated_for__expr_kind) : expr =
    let typ = c_ty e.span e.ty in
    let span = Span.of_thir e.span in
    let v = Global_ident.of_name Value Rust_primitives__hax__dropped_body in
    { span; typ; e = GlobalVar v }

  and c_block ~expr ~span ~stmts ~ty ~(safety_mode : Types.block_safety) : expr
      =
    let full_span = Span.of_thir span in
    let typ = c_ty span ty in
    let safety_mode =
      match safety_mode with
      | Safe -> Safe
      | BuiltinUnsafe | ExplicitUnsafe -> Unsafe W.unsafe
    in
    (* if there is no expression & the last expression is ⊥, just use that *)
    let lift_last_statement_as_expr_if_possible expr stmts (ty : Thir.ty) =
      match (ty.kind, expr, List.drop_last stmts, List.last stmts) with
      | ( Thir.Never,
          None,
          Some stmts,
          Some ({ kind = Thir.Expr { expr; _ }; _ } : Thir.stmt) ) ->
          (stmts, Some expr)
      | _ -> (stmts, expr)
    in
    let o_stmts, o_expr =
      lift_last_statement_as_expr_if_possible expr stmts ty
    in
    let init =
      Option.map
        ~f:(fun e ->
          let e = c_expr e in
          { e with e = Block { e; safety_mode; witness = W.block } })
        o_expr
      |> Option.value ~default:(unit_expr full_span)
    in
    List.fold_right o_stmts ~init ~f:(fun { kind; _ } body ->
        match kind with
        | Expr { expr = rhs; _ } ->
            let rhs = c_expr rhs in
            let e =
              Let { monadic = None; lhs = wild_pat rhs.span rhs.typ; rhs; body }
            in
            { e; typ; span = Span.union rhs.span body.span }
        | Let
            {
              else_block = Some { expr; span; stmts; safety_mode; _ };
              pattern = lhs;
              initializer' = Some rhs;
              _;
            } ->
            let lhs = c_pat lhs in
            let rhs = c_expr rhs in
            let else_block = c_block ~expr ~span ~stmts ~ty ~safety_mode in
            let lhs_body_span = Span.union lhs.span body.span in
            let e =
              Match
                {
                  arms =
                    [
                      U.M.arm lhs body ~span:lhs_body_span;
                      U.M.arm
                        { p = PWild; span = else_block.span; typ = lhs.typ }
                        { else_block with typ = body.typ }
                        ~span:else_block.span;
                    ];
                  scrutinee = rhs;
                }
            in
            { e; typ; span = full_span }
        | Let { initializer' = None; _ } ->
            unimplemented ~issue_id:156 [ span ]
              "Sorry, Hax does not support declare-first let bindings (see \
               https://doc.rust-lang.org/rust-by-example/variable_bindings/declare.html) \
               for now."
        | Let { pattern = lhs; initializer' = Some rhs; _ } ->
            let lhs = c_pat lhs in
            let rhs = c_expr rhs in
            let e = Let { monadic = None; lhs; rhs; body } in
            { e; typ; span = Span.union rhs.span body.span })

  and c_expr_unwrapped (e : Thir.decorated_for__expr_kind) : expr =
    (* TODO: eliminate that `call`, use the one from `ast_utils` *)
    let call f args =
      App
        {
          f;
          args = List.map ~f:c_expr args;
          generic_args = [];
          trait = None;
          bounds_impls = [];
        }
    in
    let typ = c_ty e.span e.ty in
    let span = Span.of_thir e.span in
    let mk_global typ v : expr = { span; typ; e = GlobalVar v } in
    let ( ->. ) a b = TArrow (a, b) in
    let (v : expr') =
      match e.contents with
      | MacroInvokation { argument; macro_ident; _ } ->
          MacroInvokation
            {
              args = argument;
              macro = def_id Macro macro_ident;
              witness = W.macro;
            }
      | If
          {
            cond = { contents = Let { expr = scrutinee; pat }; _ };
            else_opt;
            then';
            _;
          } ->
          let scrutinee = c_expr scrutinee in
          let arm_pat = c_pat pat in
          let then_ = c_expr then' in
          let else_ =
            Option.value ~default:(U.unit_expr span)
            @@ Option.map ~f:c_expr else_opt
          in
          let arm_then = U.M.arm arm_pat then_ ~span:then_.span in
          let arm_else =
            let arm_pat = { arm_pat with p = PWild } in
            U.M.arm arm_pat else_ ~span:else_.span
          in
          Match { scrutinee; arms = [ arm_then; arm_else ] }
      | If { cond; else_opt; then'; _ } ->
          let cond = c_expr cond in
          let then_ = c_expr then' in
          let else_ = Option.map ~f:c_expr else_opt in
          If { cond; else_; then_ }
      | Call
          {
            args;
            fn_span = _;
            trait;
            from_hir_call = _;
            fun';
            ty = _;
            generic_args;
            bounds_impls;
          } ->
          let args = List.map ~f:c_expr args in
          let bounds_impls = List.map ~f:(c_impl_expr e.span) bounds_impls in
          let c_generic_values = List.map ~f:(c_generic_value e.span) in
          let generic_args = c_generic_values generic_args in
          let f =
            let f = c_expr fun' in
            match (trait, fun'.contents) with
            | Some _, GlobalName { id } ->
                { f with e = GlobalVar (def_id (AssociatedItem Value) id) }
            | _ -> f
          in
          let args = if List.is_empty args then [ unit_expr span ] else args in
          App
            {
              f;
              args;
              generic_args;
              bounds_impls;
              trait =
                Option.map ~f:(c_impl_expr e.span *** c_generic_values) trait;
            }
      | Box { value } ->
          (U.call Rust_primitives__hax__box_new [ c_expr value ] span typ).e
      | Deref { arg } ->
          let inner_typ = c_ty arg.span arg.ty in
          call (mk_global ([ inner_typ ] ->. typ) @@ `Primitive Deref) [ arg ]
      | Binary { lhs; rhs; op } ->
          (c_binop op (c_expr lhs) (c_expr rhs) span typ).e
      | LogicalOp { lhs; rhs; op } ->
          let lhs_type = c_ty lhs.span lhs.ty in
          let rhs_type = c_ty rhs.span rhs.ty in
          call
            (mk_global ([ lhs_type; rhs_type ] ->. typ)
            @@ `Primitive (LogicalOp (c_logical_op op)))
            [ lhs; rhs ]
      | Unary { arg; op } ->
          (U.call
             (match op with
             | Not -> Core__ops__bit__Not__not
             | Neg -> Core__ops__arith__Neg__neg
             | PtrMetadata ->
                 assertion_failure (Span.to_thir span)
                   "Unsupported unary operator: `PtrMetadata`")
             [ c_expr arg ]
             span typ)
            .e
      | Cast { source } -> (
          let source_type = c_ty source.span source.ty in
          match source_type with
          (* Each inductive defines a cast function *)
          | TApp { ident = `Concrete ident; _ } ->
              (U.call'
                 (`Concrete (cast_name_for_type ident))
                 [ c_expr source ]
                 span typ)
                .e
          | _ ->
              call
                (mk_global ([ source_type ] ->. typ) @@ `Primitive Cast)
                [ source ])
      | Use { source } -> (c_expr source).e
      | NeverToAny { source } ->
          (U.call Rust_primitives__hax__never_to_any [ c_expr source ] span typ)
            .e
      (* TODO: this is incorrect (NeverToAny) *)
      | PointerCoercion { cast; source } -> c_pointer e typ span cast source
      | Loop { body } ->
          let body = c_expr body in
          Loop
            {
              body;
              kind = UnconditionalLoop;
              state = None;
              label = None;
              witness = W.loop;
            }
      | Match { scrutinee; arms } ->
          let scrutinee = c_expr scrutinee in
          let arms = List.map ~f:c_arm arms in
          Match { scrutinee; arms }
      | Let _ ->
          assertion_failure [ e.span ]
            "`Let` nodes are supposed to be pre-processed"
      | Block { expr; span; stmts; safety_mode; _ } ->
          let { e; _ } = c_block ~expr ~span ~stmts ~ty:e.ty ~safety_mode in
          e
      | Assign { lhs; rhs } ->
          let lhs = c_expr lhs in
          let rhs = c_expr rhs in
          c_expr_assign lhs rhs
      | AssignOp { lhs; op; rhs } ->
          let lhs = c_expr lhs in
          c_expr_assign lhs @@ c_binop op lhs (c_expr rhs) span lhs.typ
      | VarRef { id } -> LocalVar (local_ident Expr id)
      | Field { lhs; field } ->
          let lhs = c_expr lhs in
          let projector =
            GlobalVar
              (`Projector (`Concrete (Concrete_ident.of_def_id Field field)))
          in
          let span = Span.of_thir e.span in
          App
            {
              f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
              args = [ lhs ];
              generic_args = [] (* TODO: see issue #328 *);
              trait = None (* TODO: see issue #328 *);
              bounds_impls = [];
            }
      | TupleField { lhs; field } ->
          (* TODO: refactor *)
          let tuple_len = 0 (* todo, lookup type *) in
          let lhs = c_expr lhs in
          let projector =
            GlobalVar
              (`Projector (`TupleField (Int.of_string field, tuple_len)))
          in
          let span = Span.of_thir e.span in
          App
            {
              f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
              args = [ lhs ];
              generic_args = [] (* TODO: see issue #328 *);
              trait = None (* TODO: see issue #328 *);
              bounds_impls = [];
            }
      | GlobalName { id } -> GlobalVar (def_id Value id)
      | UpvarRef { var_hir_id = id; _ } -> LocalVar (local_ident Expr id)
      | Borrow { arg; borrow_kind = kind } ->
          let e' = c_expr arg in
          let kind = c_borrow_kind e.span kind in
          Borrow { kind; e = e'; witness = W.reference }
      | AddressOf { arg; mutability = mut } ->
          let e = c_expr arg in
          AddressOf
            {
              e;
              mut = c_mutability W.mutable_pointer mut;
              witness = W.raw_pointer;
            }
      | Break { value; _ } ->
          (* TODO: labels! *)
          let e = Option.map ~f:c_expr value in
          let e = Option.value ~default:(unit_expr span) e in
          Break { e; label = None; witness = (W.break, W.loop) }
      | Continue _ ->
          Continue { e = None; label = None; witness = (W.continue, W.loop) }
      | Return { value } ->
          let e = Option.map ~f:c_expr value in
          let e = Option.value ~default:(unit_expr span) e in
          Return { e; witness = W.early_exit }
      | ConstBlock _ -> unimplemented ~issue_id:923 [ e.span ] "ConstBlock"
      | ConstParam { param = id; _ } (* TODO: shadowing? *) | ConstRef { id } ->
          LocalVar
            {
              name = id.name;
              id = Local_ident.mk_id Cnst (MyInt64.to_int_exn id.index);
            }
      | Repeat { value; count } ->
          let value = c_expr value in
          let count = c_constant_expr count in
          let inner =
            U.call Rust_primitives__hax__repeat [ value; count ] span typ
          in
          (U.call Alloc__boxed__Impl__new [ inner ] span typ).e
      | Tuple { fields } ->
          (U.make_tuple_expr' ~span @@ List.map ~f:c_expr fields).e
      | Array { fields } -> Array (List.map ~f:c_expr fields)
      | Adt { info; base; fields; _ } ->
          let is_struct, is_record =
            match info.kind with
            | Struct { named } -> (true, named)
            | Enum { named; _ } -> (false, named)
            | Union ->
                unimplemented ~issue_id:998 [ e.span ]
                  "Construct union types: not supported"
          in
          let constructor = def_id (Constructor { is_struct }) info.variant in
          let base =
            Option.map
              ~f:(fun base -> (c_expr base.base, W.construct_base))
              base
          in
          let fields =
            List.map
              ~f:(fun f ->
                let field = def_id Field f.field in
                let value = c_expr f.value in
                (field, value))
              fields
          in
          Construct { is_record; is_struct; constructor; fields; base }
      | Literal { lit; neg; _ } -> (
          match c_lit e.span neg lit typ with
          | EL_Lit lit -> Literal lit
          | EL_U8Array l ->
              Array
                (List.map
                   ~f:(fun lit ->
                     {
                       e = Literal lit;
                       span;
                       typ = TInt { size = S8; signedness = Unsigned };
                     })
                   l))
      | NamedConst { def_id = id; impl; _ } -> (
          let kind : Concrete_ident.Kind.t =
            match impl with Some _ -> AssociatedItem Value | _ -> Value
          in
          let f = GlobalVar (def_id kind id) in
          match impl with
          | Some impl ->
              let trait = Some (c_impl_expr e.span impl, []) in
              let f = { e = f; span; typ = TArrow ([], typ) } in
              App { f; trait; args = []; generic_args = []; bounds_impls = [] }
          | _ -> f)
      | Closure { body; params; upvars; _ } ->
          let params =
            List.filter_map ~f:(fun p -> Option.map ~f:c_pat p.pat) params
          in
          let params =
            if List.is_empty params then
              [ U.M.pat_PWild ~typ:U.M.ty_unit ~span ]
            else params
          in
          let body = c_expr body in
          let upvars = List.map ~f:c_expr upvars in
          Closure { body; params; captures = upvars }
      | Index { index; lhs } ->
          let index_type = c_ty index.span index.ty in
          let lhs_type = c_ty lhs.span lhs.ty in
          call
            (mk_global ([ lhs_type; index_type ] ->. typ)
            @@ Global_ident.of_name Value Core__ops__index__Index__index)
            [ lhs; index ]
      | StaticRef { def_id = id; _ } -> GlobalVar (def_id Value id)
      | PlaceTypeAscription _ ->
          assertion_failure [ e.span ]
            "Got a unexpected node `PlaceTypeAscription`. Please report, we \
             were not able to figure out an expression yielding that node: a \
             bug report would be very valuable here!"
      | ValueTypeAscription { source; _ } -> (c_expr source).e
      | ZstLiteral _ ->
          assertion_failure [ e.span ]
            "`ZstLiteral` are expected to be handled before-hand"
      | Yield _ ->
          unimplemented ~issue_id:924 [ e.span ]
            "Got expression `Yield`: coroutines are not supported by hax"
      | Todo payload ->
          assertion_failure [ e.span ] ("expression Todo\n" ^ payload)
    in
    { e = v; span; typ }

  and c_lhs lhs =
    match lhs.e with
    | LocalVar var -> LhsLocalVar { var; typ = lhs.typ }
    | _ -> (
        match resugar_index_mut lhs with
        | Some (e, index) ->
            LhsArrayAccessor
              { e = c_lhs e; typ = lhs.typ; index; witness = W.nontrivial_lhs }
        | None -> (
            match (U.unbox_underef_expr lhs).e with
            | App
                {
                  f =
                    {
                      e = GlobalVar (`Projector _ as field);
                      typ = TArrow ([ _ ], _);
                      span = _;
                    };
                  args = [ e ];
                  generic_args = _;
                  trait = _;
                  bounds_impls = _;
                (* TODO: see issue #328 *)
                } ->
                LhsFieldAccessor
                  {
                    e = c_lhs e;
                    typ = lhs.typ;
                    field;
                    witness = W.nontrivial_lhs;
                  }
            | _ -> LhsArbitraryExpr { e = lhs; witness = W.arbitrary_lhs }))

  and c_expr_assign lhs rhs =
    Assign { lhs = c_lhs lhs; e = rhs; witness = W.mutable_variable }

  and c_constant_expr (ce : Thir.decorated_for__constant_expr_kind) : expr =
    let rec constant_expr_to_expr (ce : Thir.decorated_for__constant_expr_kind)
        : Thir.decorated_for__expr_kind =
      {
        attributes = ce.attributes;
        contents = constant_expr_kind_to_expr_kind ce.contents ce.span;
        hir_id = ce.hir_id;
        span = ce.span;
        ty = ce.ty;
      }
    and constant_expr_kind_to_expr_kind (ce : Thir.constant_expr_kind) span :
        Thir.expr_kind =
      match ce with
      | Literal lit ->
          let lit, neg = constant_lit_to_lit lit span in
          Literal { lit = { node = lit; span }; neg }
      | Adt { fields; info } ->
          let fields = List.map ~f:constant_field_expr fields in
          Adt { fields; info; base = None; user_ty = None }
      | Array { fields } ->
          Array { fields = List.map ~f:constant_expr_to_expr fields }
      | Tuple { fields } ->
          Tuple { fields = List.map ~f:constant_expr_to_expr fields }
      | GlobalName { id; _ } -> GlobalName { id }
      | Borrow arg ->
          Borrow { arg = constant_expr_to_expr arg; borrow_kind = Thir.Shared }
      | ConstRef { id } -> ConstRef { id }
      | MutPtr _ | TraitConst _ | FnPtr _ ->
          assertion_failure [ span ]
            "constant_lit_to_lit: TraitConst | FnPtr | MutPtr"
      | Todo _ -> assertion_failure [ span ] "ConstantExpr::Todo"
    and constant_lit_to_lit (l : Thir.constant_literal) _span :
        Thir.lit_kind * bool =
      match l with
      | Bool v -> (Bool v, false)
      | Char v -> (Char v, false)
      | Int (Int (v, ty)) -> (
          match String.chop_prefix v ~prefix:"-" with
          | Some v -> (Int (v, Signed ty), true)
          | None -> (Int (v, Signed ty), false))
      | Int (Uint (v, ty)) -> (Int (v, Unsigned ty), false)
      | Float (v, ty) -> (
          match String.chop_prefix v ~prefix:"-" with
          | Some v -> (Float (v, Suffixed ty), true)
          | None -> (Float (v, Suffixed ty), false))
      | Str (v, style) -> (Str (v, style), false)
      | ByteStr (v, style) -> (ByteStr (v, style), false)
    and constant_field_expr ({ field; value } : Thir.constant_field_expr) :
        Thir.field_expr =
      { field; value = constant_expr_to_expr value }
    in
    c_expr (constant_expr_to_expr ce)

  and c_pat (pat : Thir.decorated_for__pat_kind) : pat =
    let span = Span.of_thir pat.span in
    let typ = c_ty pat.span pat.ty in
    let v =
      match pat.contents with
      | Wild -> PWild
      | AscribeUserType { ascription = { annotation; _ }; subpattern } ->
          let typ, typ_span = c_canonical_user_type_annotation annotation in
          let pat = c_pat subpattern in
          PAscription { typ; typ_span; pat }
      | Binding { mode; subpattern; ty; var; _ } ->
          let mut = c_mutability W.mutable_variable mode.mutability in
          let subpat =
            Option.map ~f:(c_pat &&& Fn.const W.as_pattern) subpattern
          in
          let typ = c_ty pat.span ty in
          let mode = c_binding_mode mode.by_ref in
          let var = local_ident Expr var in
          PBinding { mut; mode; var; typ; subpat }
      | Variant { info; subpatterns; _ } ->
          let is_struct, is_record =
            match info.kind with
            | Struct { named } -> (true, named)
            | Enum { named; _ } -> (false, named)
            | Union ->
                unimplemented ~issue_id:998 [ pat.span ]
                  "Pattern match on union types: not supported"
          in
          let name = def_id (Constructor { is_struct }) info.variant in
          let args = List.map ~f:(c_field_pat info) subpatterns in
          PConstruct { name; args; is_record; is_struct }
      | Tuple { subpatterns } ->
          (List.map ~f:c_pat subpatterns |> U.make_tuple_pat').p
      | Deref { subpattern } ->
          PDeref { subpat = c_pat subpattern; witness = W.reference }
      | Constant { value } ->
          let rec pat_of_expr (e : expr) =
            { p = pat'_of_expr' e.e e.span; span = e.span; typ = e.typ }
          and pat'_of_expr' (e : expr') span =
            match e with
            | Literal lit -> PConstant { lit }
            | Array l -> PArray { args = List.map ~f:pat_of_expr l }
            | Borrow { kind = _; e; witness } ->
                PDeref { subpat = pat_of_expr e; witness }
            | _ ->
                assertion_failure (Span.to_thir span)
                  ("expected a pattern, got " ^ [%show: expr'] e)
          in
          (c_constant_expr value |> pat_of_expr).p
      | InlineConstant { subpattern; _ } -> (c_pat subpattern).p
      | Array _ -> unimplemented ~issue_id:804 [ pat.span ] "Pat:Array"
      | Or { pats } -> POr { subpats = List.map ~f:c_pat pats }
      | Slice _ -> unimplemented ~issue_id:804 [ pat.span ] "pat Slice"
      | Range _ -> unimplemented ~issue_id:925 [ pat.span ] "pat Range"
      | DerefPattern _ ->
          unimplemented ~issue_id:926 [ pat.span ] "pat DerefPattern"
      | Never -> unimplemented ~issue_id:927 [ pat.span ] "pat Never"
      | Error _ ->
          assertion_failure [ pat.span ]
            "`Error` node: Rust compilation failed. If Rust compilation was \
             fine, please file an issue."
    in
    { p = v; span; typ }

  and c_field_pat _info (field_pat : Thir.field_pat) : field_pat =
    { field = def_id Field field_pat.field; pat = c_pat field_pat.pattern }

  and extended_literal_of_expr (e : expr) : extended_literal =
    let not_a_literal () =
      assertion_failure (Span.to_thir e.span)
        ("expected a literal, got " ^ [%show: expr] e)
    in
    match e.e with
    | Literal lit -> EL_Lit lit
    | Array lits ->
        EL_U8Array
          (List.map
             ~f:(function
               | {
                   e =
                     Literal
                       (Int { kind = { size = S8; signedness = Unsigned }; _ }
                       as lit);
                   _;
                 } ->
                   lit
               | _ -> not_a_literal ())
             lits)
    | _ -> not_a_literal ()

  and c_canonical_user_type_annotation
      (annotation : Thir.canonical_user_type_annotation) : ty * span =
    (c_ty annotation.span annotation.inferred_ty, Span.of_thir annotation.span)

  and c_pointer e typ span cast source =
    match cast with
    | ClosureFnPointer Safe | ReifyFnPointer ->
        (* we have arrow types, we do not distinguish between top-level functions and closures *)
        (c_expr source).e
    | Unsize ->
        (* https://doc.rust-lang.org/std/marker/trait.Unsize.html *)
        (U.call Rust_primitives__unsize [ c_expr source ] span typ).e
        (* let source = c_expr source in *)
        (* let from_typ = source.typ in *)
        (* let to_typ = typ in *)
        (* match (U.Box.Ty.destruct from_typ, U.Box.Ty.destruct to_typ) with *)
        (* | Some _from_typ, Some to_typ -> ( *)
        (*     match U.Box.Expr.destruct source with *)
        (*     | Some source -> *)
        (*         (U.Box.Expr.make *)
        (*         @@ U.call "dummy" "unsize_cast" [] [ source ] span to_typ) *)
        (*           .e *)
        (*     | _ -> *)
        (*         unimplemented e.span *)
        (*           "[Pointer(Unsize)] cast from not directly boxed expression") *)
        (* | _ -> *)
        (*     unimplemented e.span *)
        (*       ("[Pointer(Unsize)] cast\n • from type [" *)
        (*       ^ [%show: ty] from_typ *)
        (*       ^ "]\n • to type [" *)
        (*       ^ [%show: ty] to_typ *)
        (*       ^ "]\n\nThe expression is: " *)
        (*       ^ [%show: expr] source)) *)
    | _ ->
        assertion_failure [ e.span ]
          ("Pointer, with [cast] being " ^ [%show: Thir.pointer_coercion] cast)

  and c_ty (span : Thir.span) (ty : Thir.ty) : ty =
    match ty.kind with
    | Bool -> TBool
    | Char -> TChar
    | Int k -> TInt (c_int_ty k)
    | Uint k -> TInt (c_uint_ty k)
    | Float k ->
        TFloat
          (match k with F16 -> F16 | F32 -> F32 | F64 -> F64 | F128 -> F128)
    | Arrow value ->
        let ({ inputs; output; _ } : Thir.ty_fn_sig) = value.value in
        let inputs =
          if List.is_empty inputs then [ U.unit_typ ]
          else List.map ~f:(c_ty span) inputs
        in
        TArrow (inputs, c_ty span output)
    | Adt { def_id = id; generic_args; _ } ->
        let ident = def_id Type id in
        let args = List.map ~f:(c_generic_value span) generic_args in
        TApp { ident; args }
    | Foreign _ -> unimplemented ~issue_id:928 [ span ] "Foreign"
    | Str -> TStr
    | Array (ty, len) ->
        TArray { typ = c_ty span ty; length = c_constant_expr len }
    | Slice ty ->
        let ty = c_ty span ty in
        TSlice { ty; witness = W.slice }
    | RawPtr _ -> TRawPointer { witness = W.raw_pointer }
    | Ref (_region, ty, mut) ->
        let typ = c_ty span ty in
        let mut = c_mutability W.mutable_reference mut in
        TRef { witness = W.reference; region = "todo"; typ; mut }
    | Never -> U.never_typ
    | Tuple types ->
        let types = List.map ~f:(fun ty -> GType (c_ty span ty)) types in
        TApp { ident = `TupleType (List.length types); args = types }
    | Alias { kind = Projection { assoc_item = _; impl_expr }; def_id; _ } ->
        let impl = c_impl_expr span impl_expr in
        let item = Concrete_ident.of_def_id (AssociatedItem Type) def_id in
        TAssociatedType { impl; item }
    | Alias { kind = Opaque _; def_id; _ } ->
        TOpaque (Concrete_ident.of_def_id Type def_id)
    | Alias { kind = Inherent; _ } ->
        assertion_failure [ span ] "Ty::Alias with AliasTyKind::Inherent"
    | Alias { kind = Weak; _ } ->
        assertion_failure [ span ] "Ty::Alias with AliasTyKind::Weak"
    | Param { index; name } ->
        (* TODO: [id] might not unique *)
        TParam { name; id = Local_ident.mk_id Typ (MyInt64.to_int_exn index) }
    | Error ->
        assertion_failure [ span ]
          "got type `Error`: Rust compilation probably failed."
    | Dynamic (predicates, _region, Dyn) -> (
        let goals, non_traits =
          List.partition_map
            ~f:(fun pred ->
              match pred.value with
              | Trait { args; def_id } ->
                  let goal : dyn_trait_goal =
                    {
                      trait = Concrete_ident.of_def_id Trait def_id;
                      non_self_args = List.map ~f:(c_generic_value span) args;
                    }
                  in
                  First goal
              | _ -> Second ())
            predicates
        in
        match non_traits with
        | [] -> TDyn { witness = W.dyn; goals }
        | _ -> assertion_failure [ span ] "type Dyn with non trait predicate")
    | Dynamic (_, _, DynStar) ->
        unimplemented ~issue_id:931 [ span ] "type DynStar"
    | Coroutine _ ->
        unimplemented ~issue_id:924 [ span ]
          "Got type `Coroutine`: coroutines are not supported by hax"
    | Placeholder _ ->
        assertion_failure [ span ]
          "type Placeholder: should be gone after typechecking"
    | Bound _ ->
        assertion_failure [ span ]
          "type Bound: should be gone after typechecking"
    | Infer _ ->
        assertion_failure [ span ]
          "type Infer: should be gone after typechecking"
    | Todo _ -> assertion_failure [ span ] "type Todo"
  (* fun _ -> Ok Bool *)

  and c_impl_expr (span : Thir.span) (ie : Thir.impl_expr) : impl_expr =
    let goal = c_trait_ref span ie.trait.value in
    let impl = { kind = c_impl_expr_atom span ie.impl; goal } in
    match ie.args with
    | [] -> impl
    | args ->
        let args = List.map ~f:(c_impl_expr span) args in
        { kind = ImplApp { impl; args }; goal }

  and c_trait_ref span (tr : Thir.trait_ref) : trait_goal =
    let trait = Concrete_ident.of_def_id Trait tr.def_id in
    let args = List.map ~f:(c_generic_value span) tr.generic_args in
    { trait; args }

  and c_impl_expr_atom (span : Thir.span) (ie : Thir.impl_expr_atom) :
      impl_expr_kind =
    let browse_path (item_kind : impl_expr_kind)
        (chunk : Thir.impl_expr_path_chunk) =
      match chunk with
      | AssocItem
          { item; predicate = { value = { trait_ref; _ }; _ }; predicate_id; _ }
        ->
          let ident =
            { goal = c_trait_ref span trait_ref; name = predicate_id }
          in
          let kind : Concrete_ident.Kind.t =
            match item.kind with Const | Fn -> Value | Type -> Type
          in
          let item = Concrete_ident.of_def_id kind item.def_id in
          let trait_ref = c_trait_ref span trait_ref in
          Projection
            { impl = { kind = item_kind; goal = trait_ref }; ident; item }
      | Parent { predicate = { value = { trait_ref; _ }; _ }; predicate_id; _ }
        ->
          let ident =
            { goal = c_trait_ref span trait_ref; name = predicate_id }
          in
          let trait_ref = c_trait_ref span trait_ref in
          Parent { impl = { kind = item_kind; goal = trait_ref }; ident }
    in
    match ie with
    | Concrete { id; generics } ->
        let trait = Concrete_ident.of_def_id Impl id in
        let args = List.map ~f:(c_generic_value span) generics in
        Concrete { trait; args }
    | LocalBound { predicate_id; path; _ } ->
        let init = LocalBound { id = predicate_id } in
        List.fold ~init ~f:browse_path path
    | Dyn -> Dyn
    | SelfImpl { path; _ } -> List.fold ~init:Self ~f:browse_path path
    | Builtin { trait } -> Builtin (c_trait_ref span trait.value)
    | Error str -> failwith @@ "impl_expr_atom: Error " ^ str

  and c_generic_value (span : Thir.span) (ty : Thir.generic_arg) : generic_value
      =
    match ty with
    | Type ty -> GType (c_ty span ty)
    | Const e -> GConst (c_constant_expr e)
    | _ -> GLifetime { lt = "todo generics"; witness = W.lifetime }

  and c_arm (arm : Thir.arm) : arm =
    let arm_pat = c_pat arm.pattern in
    let body = c_expr arm.body in
    let span = Span.of_thir arm.span in
    let guard =
      Option.map
        ~f:(fun (e : Thir.decorated_for__expr_kind) ->
          let guard =
            match e.contents with
            | Let { expr; pat } ->
                IfLet
                  {
                    lhs = c_pat pat;
                    rhs = c_expr expr;
                    witness = W.match_guard;
                  }
            | _ ->
                IfLet
                  {
                    lhs =
                      { p = PConstant { lit = Bool true }; span; typ = TBool };
                    rhs = c_expr e;
                    witness = W.match_guard;
                  }
          in
          { guard; span = Span.of_thir e.span })
        arm.guard
    in
    { arm = { arm_pat; body; guard }; span }

  and c_param span (param : Thir.param) : param =
    {
      typ_span = Option.map ~f:Span.of_thir param.ty_span;
      typ = c_ty (Option.value ~default:span param.ty_span) param.ty;
      pat = c_pat (Option.value_exn param.pat);
      attrs = c_attrs param.attributes;
    }

  let c_fn_params span (params : Thir.param list) : param list =
    if List.is_empty params then [ U.make_unit_param (Span.of_thir span) ]
    else List.map ~f:(c_param span) params

  let c_generic_param (param : Thir.generic_param) : generic_param =
    let ident =
      let kind =
        match (param.kind : Thir.generic_param_kind) with
        | Lifetime _ -> Local_ident.LILifetime
        | Type _ -> Local_ident.Typ
        | Const _ -> Local_ident.Cnst
      in
      match param.name with
      | Fresh ->
          (* fail with ("[Fresh] ident? " ^ Thir.show_generic_param param) *)
          (* TODO might be wrong to just have a wildcard here *)
          ({ name = "_"; id = Local_ident.mk_id kind 123 } : local_ident)
      | Error -> assertion_failure [ param.span ] "[Error] ident"
      | Plain n -> local_ident kind n
    in
    let kind =
      match (param.kind : Thir.generic_param_kind) with
      | Lifetime _ -> GPLifetime { witness = W.lifetime }
      | Type _ -> GPType
      (* Rustc always fills in const generics on use. Thus we can drop this information. *)
      | Const { default = _; ty } -> GPConst { typ = c_ty param.span ty }
    in
    let span = Span.of_thir param.span in
    let attrs = c_attrs param.attributes in
    { ident; span; attrs; kind }

  let c_clause_kind span id (kind : Thir.clause_kind) :
      generic_constraint option =
    match kind with
    | Trait { is_positive = true; trait_ref } ->
        let args = List.map ~f:(c_generic_value span) trait_ref.generic_args in
        let trait = Concrete_ident.of_def_id Trait trait_ref.def_id in
        Some (GCType { goal = { trait; args }; name = id })
    | Projection { impl_expr; assoc_item; ty } ->
        let impl = c_impl_expr span impl_expr in
        let assoc_item =
          Concrete_ident.of_def_id (AssociatedItem Type) assoc_item.def_id
        in
        let typ = c_ty span ty in
        Some (GCProjection { impl; assoc_item; typ })
    | _ -> None

  let c_clause span (p : Thir.clause) : generic_constraint option =
    let ({ kind; id } : Thir.clause) = p in
    c_clause_kind span id kind.value

  let list_dedup (equal : 'a -> 'a -> bool) : 'a list -> 'a list =
    let rec aux (seen : 'a list) (todo : 'a list) : 'a list =
      match todo with
      | hd :: tl ->
          if List.mem ~equal seen hd then aux seen tl
          else hd :: aux (hd :: seen) tl
      | _ -> todo
    in
    aux []

  let c_generics (generics : Thir.generics) : generics =
    let bounds = List.filter_map ~f:(c_clause generics.span) generics.bounds in
    {
      params = List.map ~f:c_generic_param generics.params;
      constraints = bounds |> list_dedup equal_generic_constraint;
    }

  let c_trait_item' (super : Thir.trait_item) (item : Thir.trait_item_kind) :
      trait_item' =
    let span = super.span in
    match item with
    | Const (_, Some default) ->
        TIDefault
          { params = []; body = c_expr default; witness = W.trait_item_default }
    | Const (ty, None) -> TIFn (c_ty span ty)
    | RequiredFn (sg, _) ->
        let (Thir.{ inputs; output; _ } : Thir.fn_decl) = sg.decl in
        let output =
          match output with
          | DefaultReturn _span -> unit_typ
          | Return ty -> c_ty span ty
        in
        let inputs =
          if List.is_empty inputs then [ U.unit_typ ]
          else List.map ~f:(c_ty span) inputs
        in
        TIFn (TArrow (inputs, output))
    | ProvidedFn (_, { params; body; _ }) ->
        TIDefault
          {
            params = c_fn_params span params;
            body = c_expr body;
            witness = W.trait_item_default;
          }
    | Type (bounds, None) ->
        let bounds =
          List.filter_map ~f:(c_clause span) bounds
          |> List.filter_map ~f:(fun bound ->
                 match bound with GCType impl -> Some impl | _ -> None)
        in
        TIType bounds
    | Type (_, Some _) ->
        unimplemented ~issue_id:929 [ span ]
          "Associated types defaults are not supported by hax yet (it is a \
           nightly feature)"
end

include struct
  open Make (struct
    let is_core_item = false
  end)

  let import_ty : Types.span -> Types.ty -> Ast.Rust.ty = c_ty

  let import_trait_ref : Types.span -> Types.trait_ref -> Ast.Rust.trait_goal =
    c_trait_ref

  let import_clause :
      Types.span -> Types.clause -> Ast.Rust.generic_constraint option =
    c_clause
end

(** Instantiate the functor for translating expressions. The crate
name can be configured (there are special handling related to `core`)
*)
let make ~krate : (module EXPR) =
  let is_core_item = String.(krate = "core" || krate = "core_hax_model") in
  let module M : EXPR = Make (struct
    let is_core_item = is_core_item
  end) in
  (module M)

let c_trait_item (item : Thir.trait_item) : trait_item =
  let open (val make ~krate:item.owner_id.krate : EXPR) in
  let { params; constraints } = c_generics item.generics in
  (* TODO: see TODO in impl items *)
  let ti_ident = Concrete_ident.of_def_id Field item.owner_id in
  {
    ti_span = Span.of_thir item.span;
    ti_generics = { params; constraints };
    ti_v = c_trait_item' item item.kind;
    ti_ident;
    ti_attrs = c_item_attrs item.attributes;
  }

let is_automatically_derived (attrs : Thir.attribute list) =
  List.exists (* We need something better here, see issue #108 *)
    ~f:(function
      | { kind = Normal { item = { path; _ }; _ }; _ } ->
          String.equal path "automatically_derived"
      | _ -> false)
    attrs

let is_hax_skip (attrs : Thir.attribute list) =
  List.exists
    ~f:(function
      | { kind = Normal { item = { path; _ }; _ }; _ } ->
          String.equal path "_hax::skip"
      | _ -> false)
    attrs

let should_skip (attrs : Thir.item_attributes) =
  let attrs = attrs.attributes @ attrs.parent_attributes in
  is_hax_skip attrs || is_automatically_derived attrs

(** Converts a generic parameter to a generic value. This assumes the
parameter is bound. *)
let generic_param_to_value ({ ident; kind; span; _ } : generic_param) :
    generic_value =
  match kind with
  | GPLifetime { witness } ->
      GLifetime { lt = [%show: local_ident] ident; witness }
  | GPType -> GType (TParam ident)
  | GPConst { typ } -> GConst { e = LocalVar ident; typ; span }

type discriminant_expr =
  | Lit of Int64.t
  | Exp of expr  (** Helper type for [cast_of_enum]. *)

(** Generate a cast function from an inductive to its represantant type. *)
let cast_of_enum typ_name generics typ thir_span
    (variants : (variant * Types.variant_for__decorated_for__expr_kind) list) :
    item =
  let self =
    TApp
      {
        ident = `Concrete typ_name;
        args = List.map ~f:generic_param_to_value generics.params;
      }
  in
  let span = Span.of_thir thir_span in
  let init = Lit (Int64.of_int 0) in
  let to_expr (n : Int64.t) : expr =
    match typ with
    | TInt kind ->
        let value = Int64.to_string n in
        {
          e = Literal (Int { value; negative = Int64.is_negative n; kind });
          span;
          typ;
        }
    | typ ->
        assertion_failure [ thir_span ]
        @@ "disc_literal_to_expr: got repr type "
        ^ [%show: ty] typ
  in
  let arms =
    List.folding_map variants ~init ~f:(fun acc (variant, thir_variant) ->
        let pat =
          PConstruct
            {
              is_record = variant.is_record;
              is_struct = false;
              args =
                List.map
                  ~f:(fun (cid, typ, _) ->
                    { field = `Concrete cid; pat = { p = PWild; typ; span } })
                  variant.arguments;
              name = `Concrete variant.name;
            }
        in
        let pat = { p = pat; typ = self; span } in
        match (acc, thir_variant.discr) with
        | Lit n, Relative m ->
            let acc = Lit Int64.(n + m) in
            (acc, (pat, acc))
        | _, Explicit did ->
            let acc = Exp { e = GlobalVar (def_id Value did); span; typ } in
            (acc, (pat, acc))
        | Exp e, Relative n ->
            let acc =
              Exp (U.call Core__ops__arith__Add__add [ e; to_expr n ] span typ)
            in
            (Exp e, (pat, acc)))
    |> List.map ~f:(Fn.id *** function Exp e -> e | Lit n -> to_expr n)
    |> List.map ~f:(fun (arm_pat, body) ->
           { arm = { arm_pat; body; guard = None }; span })
  in
  let scrutinee_var =
    Local_ident.{ name = "x"; id = Local_ident.mk_id Expr (-1) }
  in
  let scrutinee = { e = LocalVar scrutinee_var; typ = self; span } in
  let ident = cast_name_for_type typ_name in
  let v =
    Fn
      {
        name = ident;
        generics;
        body = { e = Match { scrutinee; arms }; typ; span };
        params =
          [
            {
              pat = U.make_var_pat scrutinee_var self span;
              typ = self;
              typ_span = None;
              attrs = [];
            };
          ];
        safety = Safe;
      }
  in
  { v; span; ident; attrs = [] }

let rec c_item ~ident ~drop_body (item : Thir.item) : item list =
  try c_item_unwrapped ~ident ~drop_body item
  with Diagnostics.SpanFreeError.Exn payload ->
    let context, kind = Diagnostics.SpanFreeError.payload payload in
    let error = Diagnostics.pretty_print_context_kind context kind in
    let span = Span.of_thir item.span in
    [ make_hax_error_item span ident error ]

and c_item_unwrapped ~ident ~drop_body (item : Thir.item) : item list =
  let open (val make ~krate:item.owner_id.krate : EXPR) in
  if should_skip item.attributes then []
  else
    let span = Span.of_thir item.span in
    let attrs = c_item_attrs item.attributes in
    let mk_one v = { span; v; ident; attrs } in
    let mk v = [ mk_one v ] in
    let drop_body =
      drop_body
      && Attr_payloads.payloads attrs
         |> List.exists
              ~f:(fst >> [%matches? (NeverDropBody : Types.ha_payload)])
         |> not
    in
    let c_body = if drop_body then c_expr_drop_body else c_expr in
    (* TODO: things might be unnamed (e.g. constants) *)
    match (item.kind : Thir.item_kind) with
    | Const (_, generics, body) ->
        mk
        @@ Fn
             {
               name =
                 Concrete_ident.of_def_id Value (Option.value_exn item.def_id);
               generics = c_generics generics;
               body = c_body body;
               params = [];
               safety = Safe;
             }
    | TyAlias (ty, generics) ->
        mk
        @@ TyAlias
             {
               name =
                 Concrete_ident.of_def_id Type (Option.value_exn item.def_id);
               generics = c_generics generics;
               ty = c_ty item.span ty;
             }
    | Fn (generics, { body; params; header = { safety; _ }; _ }) ->
        mk
        @@ Fn
             {
               name =
                 Concrete_ident.of_def_id Value (Option.value_exn item.def_id);
               generics = c_generics generics;
               body = c_body body;
               params = c_fn_params item.span params;
               safety = csafety safety;
             }
    | Enum (variants, generics, repr) ->
        let def_id = Option.value_exn item.def_id in
        let generics = c_generics generics in
        let is_struct = false in
        let kind = Concrete_ident.Kind.Constructor { is_struct } in
        let discs =
          (* Each variant might introduce a anonymous constant defining its discriminant integer  *)
          List.filter_map ~f:(fun v -> v.disr_expr) variants
          |> List.map ~f:(fun Types.{ def_id; body; _ } ->
                 let name = Concrete_ident.of_def_id kind def_id in
                 let generics = { params = []; constraints = [] } in
                 let body = c_expr body in
                 {
                   v = Fn { name; generics; body; params = []; safety = Safe };
                   span;
                   ident = name;
                   attrs = [];
                 })
        in
        let is_primitive =
          List.for_all
            ~f:(fun { data; _ } ->
              match data with
              | Unit _ | Tuple ([], _, _) | Struct { fields = []; _ } -> true
              | _ -> false)
            variants
        in
        let variants =
          List.map
            ~f:
              (fun ({ data; def_id = variant_id; attributes; _ } as original) ->
              let is_record =
                [%matches? (Struct { fields = _ :: _; _ } : Types.variant_data)]
                  data
              in
              let name = Concrete_ident.of_def_id kind variant_id in
              let arguments =
                match data with
                | Tuple (fields, _, _) | Struct { fields; _ } ->
                    List.map
                      ~f:(fun { def_id = id; ty; span; attributes; _ } ->
                        ( Concrete_ident.of_def_id Field id,
                          c_ty span ty,
                          c_attrs attributes ))
                      fields
                | Unit _ -> []
              in
              let attrs = c_attrs attributes in
              ({ name; arguments; is_record; attrs }, original))
            variants
        in
        let name = Concrete_ident.of_def_id Type def_id in
        let cast_fun =
          cast_of_enum name generics (c_ty item.span repr.typ) item.span
            variants
        in
        let variants, _ = List.unzip variants in
        let result =
          mk_one (Type { name; generics; variants; is_struct }) :: discs
        in
        if is_primitive then cast_fun :: result else result
    | Struct (v, generics) ->
        let generics = c_generics generics in
        let def_id = Option.value_exn item.def_id in
        let is_struct = true in
        (* repeating the attributes of the item in the variant: TODO is that ok? *)
        let v =
          let kind = Concrete_ident.Kind.Constructor { is_struct } in
          let name = Concrete_ident.of_def_id kind def_id in
          let name = Concrete_ident.Create.move_under name ~new_parent:name in
          let mk fields is_record =
            let arguments =
              List.map
                ~f:(fun Thir.{ def_id = id; ty; span; attributes; _ } ->
                  ( Concrete_ident.of_def_id Field id,
                    c_ty span ty,
                    c_attrs attributes ))
                fields
            in
            { name; arguments; is_record; attrs }
          in
          match v with
          | Tuple (fields, _, _) -> mk fields false
          | Struct { fields = _ :: _ as fields; _ } -> mk fields true
          | _ -> { name; arguments = []; is_record = false; attrs }
        in
        let variants = [ v ] in
        let name = Concrete_ident.of_def_id Type def_id in
        mk @@ Type { name; generics; variants; is_struct }
    | MacroInvokation { macro_ident; argument; span } ->
        mk
        @@ IMacroInvokation
             {
               macro = Concrete_ident.of_def_id Macro macro_ident;
               argument;
               span = Span.of_thir span;
               witness = W.macro;
             }
    | Trait (No, safety, generics, _bounds, items) ->
        let items =
          List.filter
            ~f:(fun { attributes; _ } -> not (should_skip attributes))
            items
        in
        let name =
          Concrete_ident.of_def_id Trait (Option.value_exn item.def_id)
        in
        let { params; constraints } = c_generics generics in
        let self =
          let id = Local_ident.mk_id Typ 0 (* todo *) in
          let ident = Local_ident.{ name = "Self"; id } in
          { ident; span; attrs = []; kind = GPType }
        in
        let params = self :: params in
        let generics = { params; constraints } in
        let items = List.map ~f:c_trait_item items in
        let safety = csafety safety in
        mk @@ Trait { name; generics; items; safety }
    | Trait (Yes, _, _, _, _) ->
        unimplemented ~issue_id:930 [ item.span ] "Auto trait"
    | Impl { of_trait = None; generics; items; _ } ->
        let items =
          List.filter
            ~f:(fun { attributes; _ } -> not (should_skip attributes))
            items
        in
        List.map
          ~f:(fun (item : Thir.impl_item) ->
            let item_def_id = Concrete_ident.of_def_id Impl item.owner_id in

            let v =
              match (item.kind : Thir.impl_item_kind) with
              | Fn { body; params; header = { safety; _ }; _ } ->
                  let params =
                    if List.is_empty params then [ U.make_unit_param span ]
                    else List.map ~f:(c_param item.span) params
                  in
                  Fn
                    {
                      name = item_def_id;
                      generics =
                        U.concat_generics (c_generics generics)
                          (c_generics item.generics);
                      body = c_expr body;
                      params;
                      safety = csafety safety;
                    }
              | Const (_ty, e) ->
                  Fn
                    {
                      name = item_def_id;
                      generics = c_generics generics;
                      (* does that make sense? can we have `const<T>`? *)
                      body = c_expr e;
                      params = [];
                      safety = Safe;
                    }
              | Type _ty ->
                  assertion_failure [ item.span ]
                    "Inherent implementations are not supposed to have \
                     associated types \
                     (https://doc.rust-lang.org/reference/items/implementations.html#inherent-implementations)."
            in
            let ident = Concrete_ident.of_def_id Value item.owner_id in
            let attrs = c_item_attrs item.attributes in
            { span = Span.of_thir item.span; v; ident; attrs })
          items
    | Impl
        {
          of_trait = Some of_trait;
          generics;
          self_ty;
          items;
          safety;
          parent_bounds;
          _;
        } ->
        let items =
          List.filter
            ~f:(fun { attributes; _ } -> not (should_skip attributes))
            items
        in
        mk
        @@ Impl
             {
               generics = c_generics generics;
               self_ty = c_ty item.span self_ty;
               of_trait =
                 ( def_id Trait of_trait.def_id,
                   List.map ~f:(c_generic_value item.span) of_trait.generic_args
                 );
               items =
                 List.map
                   ~f:(fun (item : Thir.impl_item) ->
                     (* TODO: introduce a Kind.TraitImplItem or
                        something. Otherwise we have to assume every
                        backend will see traits and impls as
                        records. See https://github.com/hacspec/hax/issues/271. *)
                     let ii_ident =
                       Concrete_ident.of_def_id Field item.owner_id
                     in
                     {
                       ii_span = Span.of_thir item.span;
                       ii_generics = c_generics item.generics;
                       ii_v =
                         (match (item.kind : Thir.impl_item_kind) with
                         | Fn { body; params; _ } ->
                             let params =
                               if List.is_empty params then
                                 [ U.make_unit_param span ]
                               else List.map ~f:(c_param item.span) params
                             in
                             IIFn { body = c_expr body; params }
                         | Const (_ty, e) ->
                             IIFn { body = c_expr e; params = [] }
                         | Type { ty; parent_bounds } ->
                             IIType
                               {
                                 typ = c_ty item.span ty;
                                 parent_bounds =
                                   List.filter_map
                                     ~f:(fun (clause, impl_expr, span) ->
                                       let* bound = c_clause span clause in
                                       match bound with
                                       | GCType trait_goal ->
                                           Some
                                             ( c_impl_expr span impl_expr,
                                               trait_goal )
                                       | _ -> None)
                                     parent_bounds;
                               });
                       ii_ident;
                       ii_attrs = c_item_attrs item.attributes;
                     })
                   items;
               parent_bounds =
                 List.filter_map
                   ~f:(fun (clause, impl_expr, span) ->
                     let* bound = c_clause span clause in
                     match bound with
                     | GCType trait_goal ->
                         Some (c_impl_expr span impl_expr, trait_goal)
                     | _ -> None)
                   parent_bounds;
               safety = csafety safety;
             }
    | Use ({ span = _; res; segments; rename }, _) ->
        let v =
          Use
            {
              path = List.map ~f:(fun x -> fst x.ident) segments;
              is_external =
                List.exists ~f:(function Err -> true | _ -> false) res;
              (* TODO: this should represent local/external? *)
              rename;
            }
        in
        (* ident is supposed to always be an actual item, thus here we need to cheat a bit *)
        (* TODO: is this DUMMY thing really needed? there's a `Use` segment (see #272) *)
        let def_id = item.owner_id in
        let def_id : Types.def_id =
          {
            def_id with
            path =
              def_id.path
              @ [
                  Types.
                    { data = ValueNs "DUMMY"; disambiguator = MyInt64.of_int 0 };
                ];
          }
        in
        [ { span; v; ident = Concrete_ident.of_def_id Value def_id; attrs } ]
    | Union _ ->
        unimplemented ~issue_id:998 [ item.span ] "Union types: not supported"
    | ExternCrate _ | Static _ | Macro _ | Mod _ | ForeignMod _ | GlobalAsm _
    | OpaqueTy _ | TraitAlias _ ->
        mk NotImplementedYet

let import_item ~drop_body (item : Thir.item) :
    concrete_ident * (item list * Diagnostics.t list) =
  let ident = Concrete_ident.of_def_id Value item.owner_id in
  let r, reports =
    let f =
      U.Mappers.rename_generic_constraints#visit_item
        (true, Hashtbl.create (module String))
      >> U.Reducers.disambiguate_local_idents
    in
    Diagnostics.Core.capture (fun _ ->
        c_item item ~ident ~drop_body |> List.map ~f)
  in
  (ident, (r, reports))
