module Thir = Types
open Utils
open Base
open Diagnostics

let assertion_failure (span : Thir.span) (details : string) =
  let kind = T.AssertionFailure { details } in
  report { span; kind; context = ThirImport };
  raise @@ Diagnostics.SpanFreeError (ThirImport, kind)

let unimplemented ?issue_id (span : Thir.span) (details : string) =
  let kind =
    T.Unimplemented
      {
        issue_id;
        details = String.(if details = "" then None else Some details);
      }
  in
  report { span; kind; context = ThirImport };
  raise @@ Diagnostics.SpanFreeError (ThirImport, kind)

let unsafe_block (span : Thir.span) =
  let kind = T.UnsafeBlock in
  report { span; kind; context = ThirImport };
  raise @@ Diagnostics.SpanFreeError (ThirImport, kind)

let todo (span : Thir.span) = unimplemented span "TODO"

module Ast = struct
  include Ast
  include Rust
end

module U = Ast_utils.Make (Features.Rust)
module W = Features.On
open Ast

type error =
  | UnsafeBlock
  | LetElse
  | LetWithoutInit
  | GotErrLiteral
  | BadSpanUnion
  | ShallowMutUnsupported
  | GotTypeInLitPat
  | IllTypedIntLiteral
[@@deriving show]

module Exn = struct
  let loc (loc : Thir.loc) : Ast.loc = { col = loc.col; line = loc.line }

  let def_id kind (def_id : Thir.def_id) : global_ident =
    `Concrete (Concrete_ident.of_def_id kind def_id)

  let local_ident (ident : Thir.local_ident) : local_ident =
    { name = ident.name; id = LocalIdent.var_id_of_int 123 (* todo! *) }

  let union_span (x : span) (y : span) : span =
    match (x, y) with
    | Dummy _, _ | _, Dummy _ -> Dummy { id = FreshSpanId.make () }
    | Span x, Span y when String.(x.file <> y.file) ->
        Dummy { id = FreshSpanId.make () }
    | Span { file; lo; _ }, Span { hi; _ } ->
        Span { file; lo; hi; id = FreshSpanId.make () }

  let c_span (span : Thir.span) : span =
    Span
      {
        lo = loc span.lo;
        hi = loc span.hi;
        file =
          (match span.filename with Real (LocalPath path) -> path | _ -> "?");
        id = FreshSpanId.make ();
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

  let c_mutability (witness : 'a) : bool -> 'a Ast.mutability = function
    | true -> Mutable witness
    | false -> Immutable

  let c_borrow_kind span : Thir.borrow_kind -> borrow_kind = function
    | Shared -> Shared
    | Shallow -> unimplemented span "Shallow borrows"
    | Unique -> Unique
    | Mut _ -> Mut W.mutable_reference

  let c_binding_mode span : Thir.binding_mode -> binding_mode = function
    | ByValue -> ByValue
    | ByRef k -> ByRef (c_borrow_kind span k, W.reference)

  let unit_typ : ty = TApp { ident = `TupleType 0; args = [] }

  let unit_expr span : expr =
    { typ = unit_typ; span; e = Ast.GlobalVar (`TupleCons 0) }

  let wild_pat span : ty -> pat = fun typ -> { typ; span; p = PWild }

  let c_logical_op : Thir.logical_op -> logical_op = function
    | And -> And
    | Or -> Or

  type extended_literal =
    | EL_Lit of literal
    | EL_U8Array of literal list (* EL_U8Array only encodes arrays of [u8]s *)

  let c_lit' span (lit : Thir.lit_kind) (ty : ty) : extended_literal =
    let mk l = EL_Lit l in
    let mku8 n =
      let kind = { size = S8; signedness = Unsigned } in
      Int { value = Int.to_string n; kind }
    in
    let error kind =
      assertion_failure span
        ("[import_thir:literal] got a " ^ kind ^ " literal, expected " ^ kind
       ^ " type, got type ["
        ^ [%show: ty] ty
        ^ "] instead.")
    in
    match lit with
    | Err ->
        assertion_failure span
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
               kind = (match ty with TInt k -> k | ty -> error "integer");
             }
    | Float (value, _kind) ->
        mk
        @@ Float
             {
               value;
               kind = (match ty with TFloat k -> k | ty -> error "float");
             }
    | Bool b -> mk @@ Bool b

  let c_lit span (lit : Thir.spanned_for__lit_kind) : ty -> extended_literal =
    c_lit' span lit.node

  let resugar_index_mut (e : expr) : (expr * expr) option =
    match (U.unbox_underef_expr e).e with
    | App
        {
          f = { e = GlobalVar (`Concrete meth); _ };
          args = [ { e = Borrow { e = x; _ }; _ }; index ];
        }
      when Concrete_ident.eq_name Core__ops__index__IndexMut__index_mut meth ->
        Some (x, index)
    | App { f = { e = GlobalVar (`Concrete meth); _ }; args = [ x; index ] }
      when Concrete_ident.eq_name Core__ops__index__Index__index meth ->
        Some (x, index)
    | _ -> None

  module type EXPR = sig
    val c_expr : Thir.decorated_for__expr_kind -> expr
    val c_ty : Thir.span -> Thir.ty -> ty
    val c_generic_value : Thir.span -> Thir.generic_arg -> generic_value
    val c_generics : Thir.generics -> generics
    val c_param : Thir.span -> Thir.param -> param
    val c_trait_item' : Thir.span -> Thir.trait_item_kind -> trait_item'
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
        | Offset -> Core__ptr__const_ptr__Impl__offset
      in
      let primitive_names_of_binop : Thir.bin_op -> Concrete_ident.name =
        function
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
        | Offset -> Rust_primitives__offset
      in
      let name =
        if CTX.is_core_item then
          let assert_type_eq t1 t2 =
            if not (U.ty_equality t1 t2) then
              assertion_failure
                (Diagnostics.to_thir_span span)
                ("Binary operation: expected LHS and RHS to have the same \
                  type, instead LHS has type ["
                ^ [%show: ty] t1
                ^ "] while RHS has type ["
                ^ [%show: ty] t2
                ^ "]")
          in
          let int =
            ("int", function TInt k -> Some (show_int_kind k) | _ -> None)
          in
          let float =
            ( "float",
              function TFloat k -> Some (show_float_kind k) | _ -> None )
          in
          let bool = ("bool", function TBool -> Some "bool" | _ -> None) in
          let concat_tup sep (x, y) = x ^ sep ^ y in
          let ( <*> ) (x, f) (y, g) =
            ( x ^ "*" ^ y,
              f *** g >> uncurry Option.both >> Option.map ~f:(concat_tup "_")
            )
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
            | Add | Sub | Mul | Div -> both int <|> both float
            | Rem -> both int
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
              assertion_failure
                (Diagnostics.to_thir_span span)
                ("Binary operation: expected " ^ expected ^ " type, got "
                ^ [%show: ty] lhs.typ)
        else Concrete_ident.of_name Value @@ overloaded_names_of_binop op
      in
      U.call' (`Concrete name) [ lhs; rhs ] span typ

    let rec c_expr (e : Thir.decorated_for__expr_kind) : expr =
      try c_expr_unwrapped e
      with Diagnostics.SpanFreeError report ->
        let typ : ty =
          try c_ty e.span e.ty
          with Diagnostics.SpanFreeError _ -> U.hax_failure_typ
        in
        let span = c_span e.span in
        U.hax_failure_expr' span typ report
          ([%show: Thir.decorated_for__expr_kind] e)

    and c_expr_unwrapped (e : Thir.decorated_for__expr_kind) : expr =
      let call f args = App { f; args = List.map ~f:c_expr args } in
      let typ = c_ty e.span e.ty in
      let span = c_span e.span in
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
            let arm_then =
              { arm = { arm_pat; body = then_ }; span = then_.span }
            in
            let arm_else =
              let arm_pat = { arm_pat with p = PWild } in
              { arm = { arm_pat; body = else_ }; span = else_.span }
            in
            Match { scrutinee; arms = [ arm_then; arm_else ] }
        | If { cond; else_opt; then'; _ } ->
            let cond = c_expr cond in
            let then_ = c_expr then' in
            let else_ = Option.map ~f:c_expr else_opt in
            If { cond; else_; then_ }
        | Call { args; fn_span = _; from_hir_call = _; fun'; ty = _ } ->
            let args = List.map ~f:c_expr args in
            let f = c_expr fun' in
            App { f; args }
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
               | Neg -> Core__ops__arith__Neg__neg)
               [ c_expr arg ]
               span typ)
              .e
        | Cast { source } ->
            let source_type = c_ty source.span source.ty in
            call
              (mk_global ([ source_type ] ->. typ) @@ `Primitive Cast)
              [ source ]
        | Use { source } -> (c_expr source).e
        | NeverToAny { source } -> (c_expr source).e
        (* TODO: this is incorrect (NeverToAny) *)
        | Pointer { cast; source } -> c_pointer e typ span cast source
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
        | Let _ -> unimplemented e.span "Let"
        | Block { safety_mode = BuiltinUnsafe | ExplicitUnsafe; _ } ->
            unsafe_block e.span
        | Block o ->
            (* if there is no expression & the last expression is ⊥, just use that *)
            let lift_last_statement_as_expr_if_possible expr stmts
                (ty : Thir.ty) =
              match (ty, expr, List.drop_last stmts, List.last stmts) with
              | ( Thir.Never,
                  None,
                  Some stmts,
                  Some ({ kind = Thir.Expr { expr; _ }; _ } : Thir.stmt) ) ->
                  (stmts, Some expr)
              | _ -> (stmts, expr)
            in
            let o_stmts, o_expr =
              lift_last_statement_as_expr_if_possible o.expr o.stmts e.ty
            in
            let init =
              Option.map ~f:c_expr o_expr
              |> Option.value ~default:(unit_expr span)
            in
            let { e; _ } =
              List.fold_right o_stmts ~init ~f:(fun { kind; _ } body ->
                  match kind with
                  | Expr { expr = rhs; _ } ->
                      let rhs = c_expr rhs in
                      let e =
                        Let
                          {
                            monadic = None;
                            lhs = wild_pat rhs.span rhs.typ;
                            rhs;
                            body;
                          }
                      in
                      let span = union_span rhs.span body.span in
                      { e; typ; span }
                  | Let { else_block = Some _; _ } ->
                      unimplemented ~issue_id:155 e.span
                        "Sorry, Hax does not support [let-else] (see \
                         https://doc.rust-lang.org/rust-by-example/flow_control/let_else.html) \
                         for now."
                  | Let { initializer' = None; _ } ->
                      unimplemented ~issue_id:156 e.span
                        "Sorry, Hax does not support declare-first let \
                         bindings (see \
                         https://doc.rust-lang.org/rust-by-example/variable_bindings/declare.html) \
                         for now."
                  | Let { pattern = lhs; initializer' = Some rhs; _ } ->
                      let lhs = c_pat lhs in
                      let rhs = c_expr rhs in
                      let e = Let { monadic = None; lhs; rhs; body } in
                      let span = union_span rhs.span body.span in
                      { e; typ; span })
            in
            e
        | Assign { lhs; rhs } ->
            let lhs = c_expr lhs in
            let rhs = c_expr rhs in
            c_expr_assign lhs rhs
        | AssignOp { lhs; op; rhs } ->
            let lhs = c_expr lhs in
            c_expr_assign lhs @@ c_binop op lhs (c_expr rhs) span typ
        | VarRef { id } -> LocalVar (local_ident id)
        | Field { lhs; field } ->
            let lhs = c_expr lhs in
            let projector =
              GlobalVar
                (`Projector (`Concrete (Concrete_ident.of_def_id Field field)))
            in
            let span = c_span e.span in
            App
              {
                f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
                args = [ lhs ];
              }
        | TupleField { lhs; field } ->
            (* TODO: refactor *)
            let tuple_len = 0 (* todo, lookup type *) in
            let lhs = c_expr lhs in
            let projector =
              GlobalVar (`Projector (`TupleField (field, tuple_len)))
            in
            let span = c_span e.span in
            App
              {
                f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
                args = [ lhs ];
              }
        | GlobalName { id } -> GlobalVar (def_id Value id)
        | UpvarRef { var_hir_id = id; _ } -> LocalVar (local_ident id)
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
            Break { e; label = None; witness = W.loop }
        | Continue _ ->
            Continue { e = None; label = None; witness = (W.continue, W.loop) }
        | Return { value } ->
            let e = Option.map ~f:c_expr value in
            let e = Option.value ~default:(unit_expr span) e in
            Return { e; witness = W.early_exit }
        | ConstBlock _ -> unimplemented e.span "ConstBlock"
        | ConstParam { param = id } (* TODO: shadowing? *) | ConstRef { id } ->
            LocalVar
              { name = id.name; id = LocalIdent.const_id_of_int id.index }
        | Repeat { value; count } ->
            let value = c_expr value in
            let count = c_expr count in
            let inner =
              U.call Rust_primitives__hax__repeat [ value; count ] span typ
            in
            (U.call Alloc__boxed__Impl__new [ inner ] span typ).e
        | Tuple { fields } ->
            (U.make_tuple_expr' ~span @@ List.map ~f:c_expr fields).e
        | Array { fields } -> Array (List.map ~f:c_expr fields)
        | Adt { info; base; fields; _ } ->
            let constructor =
              def_id
                (Constructor { is_struct = info.typ_is_struct })
                info.variant
            in
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
            Construct
              {
                is_record = info.variant_is_record;
                is_struct = info.typ_is_struct;
                constructor;
                fields;
                base;
              }
        | Literal { lit; _ } -> (
            match c_lit e.span lit typ with
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
        | NamedConst { def_id = id; _ } -> GlobalVar (def_id Value id)
        | Closure { body; params; upvars; _ } ->
            let params =
              List.filter_map ~f:(fun p -> Option.map ~f:c_pat p.pat) params
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
            unimplemented e.span "expression PlaceTypeAscription"
        | ValueTypeAscription _ ->
            unimplemented e.span "expression ValueTypeAscription"
        | NonHirLiteral _ -> unimplemented e.span "expression NonHirLiteral"
        | ZstLiteral _ -> unimplemented e.span "expression ZstLiteral"
        | Yield _ -> unimplemented e.span "expression Yield"
        | Todo _ -> unimplemented e.span "expression Todo"
      in
      { e = v; span; typ }

    and c_expr_assign lhs rhs =
      let rec mk_lhs lhs =
        match lhs.e with
        | LocalVar var -> LhsLocalVar { var; typ = lhs.typ }
        | _ -> (
            match resugar_index_mut lhs with
            | Some (e, index) ->
                LhsArrayAccessor
                  {
                    e = mk_lhs e;
                    typ = lhs.typ;
                    index;
                    witness = W.nontrivial_lhs;
                  }
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
                    } ->
                    LhsFieldAccessor
                      {
                        e = mk_lhs e;
                        typ = lhs.typ;
                        field;
                        witness = W.nontrivial_lhs;
                      }
                | _ -> LhsArbitraryExpr { e = lhs; witness = W.arbitrary_lhs }))
      in

      Assign { lhs = mk_lhs lhs; e = rhs; witness = W.mutable_variable }

    and c_pat (pat : Thir.decorated_for__pat_kind) : pat =
      let span = c_span pat.span in
      let typ = c_ty pat.span pat.ty in
      let v =
        match pat.contents with
        | Wild -> PWild
        | AscribeUserType { ascription = { annotation; _ }; subpattern } ->
            let typ, typ_span = c_canonical_user_type_annotation annotation in
            let pat = c_pat subpattern in
            PAscription { typ; typ_span; pat }
        | Binding { mode; mutability; subpattern; ty; var; _ } ->
            let mut = c_mutability W.mutable_variable mutability in
            let subpat =
              Option.map ~f:(c_pat &&& Fn.const W.as_pattern) subpattern
            in
            let typ = c_ty pat.span ty in
            let mode = c_binding_mode pat.span mode in
            let var = local_ident var in
            PBinding { mut; mode; var; typ; subpat }
        | Variant { info; subpatterns; _ } ->
            let name =
              def_id
                (Constructor { is_struct = info.typ_is_struct })
                info.variant
            in
            let args = List.map ~f:(c_field_pat info) subpatterns in
            PConstruct
              {
                name;
                args;
                is_record = info.variant_is_record;
                is_struct = info.typ_is_struct;
              }
        | Tuple { subpatterns } ->
            (List.map ~f:c_pat subpatterns |> U.make_tuple_pat').p
        | Deref { subpattern } ->
            PDeref { subpat = c_pat subpattern; witness = W.reference }
        | Constant { value } -> (
            match c_typed_constant_kind pat.span value with
            | EL_Lit lit -> PConstant { lit }
            | EL_U8Array l ->
                PArray
                  {
                    args =
                      List.map
                        ~f:(fun lit ->
                          {
                            p = PConstant { lit };
                            span;
                            typ = TInt { size = S8; signedness = Unsigned };
                          })
                        l;
                  })
        | Array _ -> unimplemented pat.span "Pat:Array"
        | Or _ -> unimplemented pat.span "Or"
        | Slice _ -> unimplemented pat.span "Slice"
        | Range _ -> unimplemented pat.span "Range"
      in
      { p = v; span; typ }

    and c_field_pat info (field_pat : Thir.field_pat) : field_pat =
      { field = def_id Field field_pat.field; pat = c_pat field_pat.pattern }

    and extended_literal_of_expr (e : expr) : extended_literal =
      let not_a_literal () =
        assertion_failure
          (Diagnostics.to_thir_span e.span)
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
                   } ->
                     lit
                 | _ -> not_a_literal ())
               lits)
      | _ -> not_a_literal ()

    and c_typed_constant_kind span (k : Thir.typed_constant_kind) :
        extended_literal =
      match k.constant_kind with
      | Ty e -> extended_literal_of_expr (c_expr e)
      | Lit lit -> c_lit' span lit (c_ty span k.typ)
      | Todo s -> unimplemented span ("TODO node: " ^ s)

    and c_canonical_user_type_annotation
        (annotation : Thir.canonical_user_type_annotation) : ty * span =
      (c_ty annotation.span annotation.inferred_ty, c_span annotation.span)

    and c_pointer e typ span cast source =
      match cast with
      | ReifyFnPointer ->
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
          unimplemented e.span
            ("Pointer, with [cast] being " ^ [%show: Thir.pointer_cast] cast)

    and c_ty (span : Thir.span) (ty : Thir.ty) : ty =
      match ty with
      | Bool -> TBool
      | Char -> TChar
      | Int k -> TInt (c_int_ty k)
      | Uint k -> TInt (c_uint_ty k)
      | Float k -> TFloat (match k with F32 -> F32 | F64 -> F64)
      | Arrow { params; ret } ->
          TArrow (List.map ~f:(c_ty span) params, c_ty span ret)
      | NamedType { def_id = id; generic_args } ->
          let ident = def_id Type id in
          let args = List.map ~f:(c_generic_value span) generic_args in
          TApp { ident; args }
      | Foreign _ -> unimplemented span "Foreign"
      | Str -> TStr
      | Array (ty, len) -> TArray { typ = c_ty span ty; length = c_expr len }
      | Slice ty ->
          let ty = c_ty span ty in
          TSlice { ty; witness = W.slice }
      | RawPtr _ -> TRawPointer { witness = W.raw_pointer }
      | Ref (_region, ty, mut) ->
          let typ = c_ty span ty in
          let mut = c_mutability W.mutable_reference mut in
          TRef { witness = W.reference; region = "todo"; typ; mut }
      | Never -> TFalse
      | Tuple types ->
          let types = List.map ~f:(fun ty -> GType (c_ty span ty)) types in
          TApp { ident = `TupleType (List.length types); args = types }
      | Alias _ -> TProjectedAssociatedType (Thir.show_ty ty)
      (* | Opaque _ -> unimplemented span "type Opaque" *)
      | Param { index; name } ->
          (* TODO: [id] might not unique *)
          TParam { name; id = LocalIdent.ty_param_id_of_int index }
      | Error -> unimplemented span "type Error"
      | Dynamic _ -> unimplemented span "type Dynamic"
      | Generator _ -> unimplemented span "type Generator"
      | Placeholder _ -> unimplemented span "type Placeholder"
      | Bound _ -> unimplemented span "type Bound"
      | Infer _ -> unimplemented span "type Infer"
      | Todo _ -> unimplemented span "type Todo"
    (* fun _ -> Ok Bool *)

    and c_generic_value (span : Thir.span) (ty : Thir.generic_arg) :
        generic_value =
      match ty with
      | Type ty -> GType (c_ty span ty)
      | Const _e -> unimplemented span "c_generic_value:Const"
      | _ -> GLifetime { lt = "todo generics"; witness = W.lifetime }

    and c_arm (arm : Thir.arm) : arm =
      let arm_pat = c_pat arm.pattern in
      let body = c_expr arm.body in
      let span = c_span arm.span in
      { arm = { arm_pat; body }; span }

    and c_param span (param : Thir.param) : param =
      {
        typ_span = Option.map ~f:c_span param.ty_span;
        typ = c_ty (Option.value ~default:span param.ty_span) param.ty;
        pat = c_pat (Option.value_exn param.pat);
      }

    let c_generic_param (param : Thir.generic_param) : generic_param =
      let ident =
        match param.name with
        | Fresh ->
            (* fail with ("[Fresh] ident? " ^ Thir.show_generic_param param) *)
            (* TODO might be wrong to just have a wildcard here *)
            ({ name = "_"; id = LocalIdent.ty_param_id_of_int 123 }
              : local_ident)
        | Error -> assertion_failure param.span "[Error] ident"
        | Plain n -> local_ident n
      in
      match (param.kind : Thir.generic_param_kind) with
      | Lifetime _ -> GPLifetime { ident; witness = W.lifetime }
      | Type { default; _ } ->
          let default = Option.map ~f:(c_ty param.span) default in
          GPType { ident; default }
      | Const { default = Some _; _ } ->
          unimplemented param.span "c_generic_param:Const with a default"
      | Const { default = None; ty } ->
          GPConst { ident; typ = c_ty param.span ty }

    let c_predicate_kind span (p : Thir.predicate_kind) : trait_ref option =
      match p with
      | Clause (Trait { is_positive = true; is_const = _; trait_ref }) ->
          let args =
            List.map ~f:(c_generic_value span) trait_ref.generic_args
          in
          Some
            {
              trait = Concrete_ident.of_def_id Trait trait_ref.def_id;
              args;
              bindings = [];
            }
      | _ -> None

    let c_constraint span (c : Thir.where_predicate) : generic_constraint list =
      match c with
      | BoundPredicate { bounded_ty; bounds; span; _ } ->
          let typ = c_ty span bounded_ty in
          let traits = List.map ~f:(c_predicate_kind span) bounds in
          let traits = List.filter_map ~f:Fn.id traits in
          List.map
            ~f:(fun trait : generic_constraint ->
              GCType { typ; implements = trait })
            traits
      | RegionPredicate _ -> unimplemented span "region prediate"
      | EqPredicate _ -> unimplemented span "EqPredicate"

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
      {
        params = List.map ~f:c_generic_param generics.params;
        constraints =
          List.concat_map ~f:(c_constraint generics.span) generics.predicates
          |> list_dedup equal_generic_constraint;
      }

    let c_trait_item' span (item : Thir.trait_item_kind) : trait_item' =
      match item with
      | Const (_, Some _) ->
          unimplemented span
            "TODO: traits: no support for defaults in traits for now"
      | Const (ty, None) -> TIFn (c_ty span ty)
      | ProvidedFn _ ->
          unimplemented span
            "TODO: traits: no support for defaults in funcitons for now"
      | RequiredFn (sg, _) ->
          let Thir.{ inputs; output; _ } = sg.decl in
          let output =
            match output with
            | DefaultReturn _span -> unit_typ
            | Return ty -> c_ty span ty
          in
          TIFn (TArrow (List.map ~f:(c_ty span) inputs, output))
      | Type (bounds, None) ->
          let bounds = List.filter_map ~f:(c_predicate_kind span) bounds in
          TIType bounds
      | Type (_, Some _) ->
          unimplemented span
            "TODO: traits: no support for defaults in type for now"
  end

  let make ~krate : (module EXPR) =
    let is_core_item = String.(krate = "core" || krate = "core_hax_model") in
    let module M : EXPR = Make (struct
      let is_core_item = is_core_item
    end) in
    (module M)

  let c_trait_item (item : Thir.trait_item) : trait_item =
    let open (val make ~krate:item.owner_id.krate : EXPR) in
    let { params; constraints } = c_generics item.generics in
    {
      ti_span = c_span item.span;
      ti_generics = { params; constraints };
      ti_v = c_trait_item' item.span item.kind;
      ti_name = fst item.ident;
    }

  let rec c_item (item : Thir.item) : item list =
    try c_item_unwrapped item with Diagnostics.SpanFreeError _kind -> []

  and c_item_unwrapped (item : Thir.item) : item list =
    let open (val make ~krate:item.owner_id.krate : EXPR) in
    if
      (* We need something better here, see issue #108 *)
      List.exists
        ~f:(function
          | { kind = Normal { item = { path; _ }; _ }; _ } ->
              String.equal path "automatically_derived"
          | _ -> false)
        item.attributes
    then []
    else
      let span = c_span item.span in
      let mk_one v =
        { span; v; ident = Concrete_ident.of_def_id Value item.owner_id }
      in
      let mk v = [ mk_one v ] in
      (* TODO: things might be unnamed (e.g. constants) *)
      match (item.kind : Thir.item_kind) with
      | Const (_, body) ->
          mk
          @@ Fn
               {
                 name =
                   Concrete_ident.of_def_id Value (Option.value_exn item.def_id);
                 generics = { params = []; constraints = [] };
                 body = c_expr body;
                 params = [];
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
      | Fn (generics, { body; params; _ }) ->
          mk
          @@ Fn
               {
                 name =
                   Concrete_ident.of_def_id Value (Option.value_exn item.def_id);
                 generics = c_generics generics;
                 body = c_expr body;
                 params = List.map ~f:(c_param item.span) params;
               }
      | Enum (variants, generics) ->
          let def_id = Option.value_exn item.def_id in
          let generics = c_generics generics in
          let is_struct = false in
          let variants =
            let kind = Concrete_ident.Kind.Constructor { is_struct } in
            List.map
              ~f:(fun { data; def_id = variant_id; _ } ->
                let is_record = [%matches? Types.Struct (_ :: _, _)] data in
                let name = Concrete_ident.of_def_id kind variant_id in
                let arguments =
                  match data with
                  | Tuple (fields, _, _) | Struct (fields, _) ->
                      List.map
                        ~f:(fun { def_id = id; ty; span; _ } ->
                          (Concrete_ident.of_def_id Field id, c_ty span ty))
                        fields
                  | Unit (_, name) -> []
                in
                { name; arguments; is_record })
              variants
          in
          let name = Concrete_ident.of_def_id Type def_id in
          mk @@ Type { name; generics; variants; is_struct }
      | Struct (v, generics) ->
          let generics = c_generics generics in
          let def_id = Option.value_exn item.def_id in
          let is_struct = true in
          let v =
            let kind = Concrete_ident.Kind.Constructor { is_struct } in
            let name = Concrete_ident.of_def_id kind def_id in
            let mk fields is_record =
              let arguments =
                List.map
                  ~f:(fun Thir.{ def_id = id; ty; span; _ } ->
                    (Concrete_ident.of_def_id Field id, c_ty span ty))
                  fields
              in
              { name; arguments; is_record }
            in
            match v with
            | Tuple (fields, _, _) -> mk fields false
            | Struct ((_ :: _ as fields), _) -> mk fields true
            | _ -> { name; arguments = []; is_record = false }
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
                 span = c_span span;
                 witness = W.macro;
               }
      | Trait (No, Normal, generics, _bounds, items) ->
          let name =
            Concrete_ident.of_def_id Trait (Option.value_exn item.def_id)
          in
          let { params; constraints } = c_generics generics in
          let params =
            GPType
              {
                ident =
                  {
                    name = "Self";
                    id = LocalIdent.ty_param_id_of_int 0 (* todo *);
                  };
                default = None;
              }
            :: params
          in
          mk
          @@ Trait
               {
                 name;
                 generics = { params; constraints };
                 items = List.map ~f:c_trait_item items;
               }
      | Trait (Yes, _, _, _, _) -> unimplemented item.span "Auto trait"
      | Trait (_, Unsafe, _, _, _) -> unimplemented item.span "Unsafe trait"
      | Impl { of_trait = None; generics; items; _ } ->
          List.map
            ~f:(fun (item : Thir.impl_item) ->
              let item_def_id = Concrete_ident.of_def_id Impl item.owner_id in
              let v =
                match (item.kind : Thir.impl_item_kind) with
                | Fn { body; params; _ } ->
                    Fn
                      {
                        name = item_def_id;
                        generics = c_generics generics;
                        body = c_expr body;
                        params = List.map ~f:(c_param item.span) params;
                      }
                | Const (_ty, e) ->
                    Fn
                      {
                        name = item_def_id;
                        generics = c_generics generics;
                        (* does that make sense? can we have `const<T>`? *)
                        body = c_expr e;
                        params = [];
                      }
                | Type ty ->
                    assertion_failure item.span
                      "Inherent implementations are not supposed to have \
                       associated types \
                       (https://doc.rust-lang.org/reference/items/implementations.html#inherent-implementations)."
              in
              let ident = Concrete_ident.of_def_id Value item.owner_id in
              { span = c_span item.span; v; ident })
            items
      | Impl ({ of_trait = Some of_trait } as i) ->
          mk
          @@ Impl
               {
                 generics = c_generics i.generics;
                 self_ty = c_ty item.span i.self_ty;
                 of_trait =
                   ( def_id Trait of_trait.def_id,
                     List.map
                       ~f:(c_generic_value item.span)
                       of_trait.generic_args );
                 items =
                   List.map
                     ~f:(fun (item : Thir.impl_item) ->
                       {
                         ii_span = c_span item.span;
                         ii_generics = c_generics item.generics;
                         ii_v =
                           (match (item.kind : Thir.impl_item_kind) with
                           | Fn { body; params; _ } ->
                               IIFn
                                 {
                                   body = c_expr body;
                                   params =
                                     List.map ~f:(c_param item.span) params;
                                 }
                           | Const (_ty, e) ->
                               IIFn { body = c_expr e; params = [] }
                           | Type ty -> IIType (c_ty item.span ty));
                         ii_name = fst item.ident;
                       })
                     i.items;
               }
      | Use ({ span = _; res; segments; rename }, t) ->
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
          let def_id = item.owner_id in
          let def_id : Types.def_id =
            {
              def_id with
              path =
                def_id.path
                @ [ Types.{ data = ValueNs "DUMMY"; disambiguator = 0 } ];
            }
          in
          [ { span; v; ident = Concrete_ident.of_def_id Value def_id } ]
      | ExternCrate _ | Static _ | Macro _ | Mod _ | ForeignMod _ | GlobalAsm _
      | OpaqueTy _ | Union _ | TraitAlias _ ->
          mk NotImplementedYet
end

let c_item (item : Thir.item) : (item list, error) Result.t =
  Exn.c_item item |> Result.return
