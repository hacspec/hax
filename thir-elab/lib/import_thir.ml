module Thir = Raw_thir_ast
open Utils
open Base

module Ast = struct
  include Ast
  include Ast.Make (Features.Rust)
end

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
  exception ImportError of error

  open struct
    let raise e = raise @@ ImportError e
  end

  let loc (loc : Thir.loc) : Ast.loc = { col = loc.col; line = loc.line }

  let string_of_def_path_item : Thir.def_path_item -> string option = function
    | TypeNs s | ValueNs s | MacroNs s | LifetimeNs s -> Some s
    | _ -> None

  let namespace_of_def_id (def_id : Thir.def_id) : string * string list =
    ( def_id.krate,
      def_id.path |> List.drop_last_exn
      |> List.filter_map ~f:string_of_def_path_item )

  let concrete_of_def_id (def_id : Thir.def_id) : concrete_ident =
    {
      crate = def_id.krate;
      path =
        def_id.path
        |> List.filter_map ~f:string_of_def_path_item
        |> Non_empty_list.of_list_exn;
    }

  let def_id (def_id : Thir.def_id) : global_ident =
    `Concrete (concrete_of_def_id def_id)

  let local_ident (ident : Thir.local_ident) : local_ident =
    { name = ident.name; id = 123 (* todo! *) }

  let union_span (x : span) (y : span) : span =
    match (x, y) with
    | Dummy, _ | _, Dummy -> Dummy
    | Span x, Span y when String.(x.file <> y.file) -> raise BadSpanUnion
    | Span { file; lo }, Span { hi } -> Span { file; lo; hi }

  let c_span (span : Thir.span) : span =
    Span
      {
        lo = loc span.lo;
        hi = loc span.hi;
        file =
          (match span.filename with Real (LocalPath path) -> path | _ -> "?");
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

  module W = Features.On

  let c_borrow_kind : Thir.borrow_kind -> borrow_kind = function
    | Shared -> Shared
    | Shallow -> raise ShallowMutUnsupported
    | Unique -> Unique
    | Mut _ -> Mut W.mutable_reference

  let c_binding_mode : Thir.binding_mode -> binding_mode = function
    | ByValue -> ByValue
    | ByRef k -> ByRef (c_borrow_kind k, W.reference)

  let unit_typ : ty = TApp { ident = `TupleType 0; args = [] }

  let unit_expr span : expr =
    { typ = unit_typ; span; e = Ast.GlobalVar (`TupleCons 0) }

  let wild_pat span : ty -> pat = fun typ -> { typ; span; p = PWild }

  let c_binop : Thir.bin_op -> bin_op = function
    | Add -> Add
    | Sub -> Sub
    | Mul -> Mul
    | Div -> Div
    | Rem -> Rem
    | BitXor -> BitXor
    | BitAnd -> BitAnd
    | BitOr -> BitOr
    | Shl -> Shl
    | Shr -> Shr
    | Eq -> Eq
    | Lt -> Lt
    | Le -> Le
    | Ne -> Ne
    | Ge -> Ge
    | Gt -> Gt
    | Offset -> Offset

  let c_un_op : Thir.un_op -> un_op = function Not -> Not | Neg -> Neg

  let c_logical_op : Thir.logical_op -> logical_op = function
    | And -> And
    | Or -> Or

  let c_lit_type (t : Thir.lit_int_type) : int_kind =
    match t with
    | Unsuffixed -> failwith "Got an untyped int literal which is `Unsuffixed`"
    | Signed ty -> { size = int_ty_to_size ty; signedness = Signed }
    | Unsigned ty -> { size = uint_ty_to_size ty; signedness = Unsigned }

  let c_lit' (lit : Thir.lit_kind) (ty : ty option) : literal =
    match lit with
    | Err -> raise GotErrLiteral
    | Str (str, _) -> String str
    | ByteStr _ -> failwith "todo"
    | Byte _ -> failwith "todo"
    | Char s -> Char s
    | Int (i, t) ->
        Int
          {
            value = i;
            kind =
              (match ty with
              | Some (TInt k) -> k
              | Some _ -> raise IllTypedIntLiteral
              | None ->
                  failwith "TODO" { size = S8; signedness = Unsigned }
                  (* kind = (match t with _ -> failwith "lit: int" (\* TODO *\)); *));
          }
    | Float _ -> failwith "todo float"
    | Bool b -> Bool b

  let c_lit (lit : Thir.spanned_for__lit_kind) : ty option -> literal =
    c_lit' lit.node

  let append_to_thir_def_id (def_id : Thir.def_id) (item : Thir.def_path_item) =
    { def_id with path = def_id.path @ [ item ] }

  let variant_id_of_variant_informations (info : Thir.variant_informations) =
    let is_def_id_prefix (x : Thir.def_id) (y : Thir.def_id) : bool =
      String.(x.krate = y.krate)
      && List.is_prefix ~prefix:x.path ~equal:Thir.equal_def_path_item y.path
    in
    if not (is_def_id_prefix info.type_namespace info.variant) then
      failwith
        ("variant_id_of_variant_informations: ["
        ^ Thir.show_def_id info.type_namespace
        ^ "] is not a prefix of ["
        ^ Thir.show_def_id info.variant
        ^ "]");
    append_to_thir_def_id info.type_namespace (List.last_exn info.variant.path)

  let unbox_underef_expr (e : expr) : expr =
    match e.e with
    | App
        {
          f = { e = GlobalVar (`Primitive (Ast.Box | Ast.Deref)) };
          args = [ e ];
        } ->
        e
    | _ -> e

  let resugar_index_mut (e : expr) : (expr * expr) option =
    match (unbox_underef_expr e).e with
    | App
        {
          f =
            {
              e =
                GlobalVar
                  (`Concrete
                    {
                      crate = "core";
                      path =
                        Non_empty_list.(
                          "ops" :: [ "index"; "IndexMut"; "index_mut" ]);
                    });
            };
          args = [ { e = Borrow { e = x } }; index ];
        } ->
        Some (x, index)
    | _ -> None

  let rec c_expr (e : Thir.decorated_for__expr_kind) : expr =
    let call f args = App { f; args = List.map ~f:c_expr args } in
    let typ = c_ty e.ty in
    let span = c_span e.span in
    let mk typ e : expr = { span; typ; e } in
    let mk_global typ v : expr = { span; typ; e = GlobalVar v } in
    let ( ->. ) a b = TArrow (a, b) in
    let (v : expr') =
      match e.contents with
      | Box { value } ->
          let inner_typ = c_ty e.ty in
          call (mk_global ([ inner_typ ] ->. typ) @@ `Primitive Box) [ value ]
      | MacroInvokation { argument; macro_ident } ->
          MacroInvokation
            { args = argument; macro = def_id macro_ident; witness = W.macro }
      | If { cond; if_then_scope = _; else_opt; then' } ->
          let cond = c_expr cond in
          let then_ = c_expr then' in
          let else_ = Option.map ~f:c_expr else_opt in
          If { cond; else_; then_ }
      | Call { args; fn_span = _; from_hir_call = _; fun'; ty = _ } ->
          let args = List.map ~f:c_expr args in
          let f = c_expr fun' in
          App { f; args }
      | Deref { arg } ->
          let inner_typ = c_ty e.ty in
          call (mk_global ([ inner_typ ] ->. typ) @@ `Primitive Deref) [ arg ]
      | Binary { lhs; rhs; op } ->
          let lty = c_ty lhs.ty in
          let rty = c_ty rhs.ty in
          call
            (mk_global ([ lty; rty ] ->. typ) @@ `Primitive (BinOp (c_binop op)))
            [ lhs; rhs ]
      | LogicalOp { lhs; rhs; op } ->
          let lhs_type = c_ty lhs.ty in
          let rhs_type = c_ty rhs.ty in
          call
            (mk_global ([ lhs_type; rhs_type ] ->. typ) @@ `Primitive Deref)
            [ lhs; rhs ]
      | Unary { arg; op } ->
          let arg_type = c_ty arg.ty in
          call (mk_global ([ arg_type ] ->. typ) @@ `Primitive Deref) [ arg ]
      | Cast { source } ->
          let source_type = c_ty source.ty in
          call
            (mk_global ([ source_type ] ->. typ) @@ `Primitive Deref)
            [ source ]
      | Use { source } ->
          let source = c_expr source in
          source.e
      | NeverToAny { source } ->
          let { e } = c_expr source in
          e
      (* TODO: this is incorrect *)
      | Pointer _ -> failwith "Pointer"
      | Loop { body } ->
          let body = c_expr body in
          Loop { body; label = None; witness = W.loop }
      | Match { scrutinee; arms } ->
          let scrutinee = c_expr scrutinee in
          let arms = List.map ~f:c_arm arms in
          Match { scrutinee; arms }
      | Let _ -> failwith "TODO: Let"
      | Block { safety_mode = BuiltinUnsafe | ExplicitUnsafe } ->
          raise UnsafeBlock
      | Block o ->
          let init =
            Option.map ~f:c_expr o.expr
            |> Option.value ~default:(unit_expr span)
          in
          let { e } =
            List.fold_right o.stmts ~init ~f:(fun { kind } body ->
                match kind with
                | Expr { expr = rhs } ->
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
                | Let { else_block = Some _ } -> raise LetElse
                | Let { initializer' = None } -> raise LetWithoutInit
                | Let { pattern = lhs; initializer' = Some rhs } ->
                    let lhs = c_pat lhs in
                    let rhs = c_expr rhs in
                    let e = Let { monadic = None; lhs; rhs; body } in
                    let span = union_span rhs.span body.span in
                    { e; typ; span })
          in
          e
      | Assign { lhs; rhs } ->
          let lhs = c_expr lhs in
          let e = c_expr rhs in
          let rec mk_lhs lhs =
            match lhs.e with
            | LocalVar var -> LhsLocalVar { var; typ = lhs.typ }
            | _ -> (
                match resugar_index_mut lhs with
                | Some (e, index) ->
                    LhsArrayAccessor { e = mk_lhs e; typ = lhs.typ; index }
                | None ->
                    LhsArbitraryExpr { e = lhs; witness = W.arbitrary_lhs })
          in
          Assign { lhs = mk_lhs lhs; e; witness = W.mutable_variable }
      | AssignOp _ -> failwith "AssignOp"
      | VarRef { id } -> LocalVar (local_ident id)
      | Field { lhs; field } ->
          let lhs = c_expr lhs in
          let projector =
            GlobalVar (`Projector (`Concrete (concrete_of_def_id field)))
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
      | GlobalName { id } -> GlobalVar (def_id id)
      | UpvarRef { var_hir_id = id } -> LocalVar (local_ident id)
      (* failwith ("upvar ref: " ^ Thir.show_decorated_for__expr_kind e) *)
      | Borrow { arg; borrow_kind = kind } ->
          let e = c_expr arg in
          let kind = c_borrow_kind kind in
          Borrow { kind; e; witness = W.reference }
      | AddressOf { arg; mutability = mut } ->
          let e = c_expr arg in
          AddressOf
            {
              e;
              mut = c_mutability W.mutable_pointer mut;
              witness = W.raw_pointer;
            }
      (* | Break { label; value = Some _ } -> *)
      (*     failwith "TODO: Break with labels are not supported" *)
      | Break { label; value } ->
          let e = Option.map ~f:c_expr value in
          let e = Option.value ~default:(unit_expr span) e in
          Break { e; label = None; witness = W.loop }
      | Continue _ -> Continue { label = None; witness = (W.continue, W.loop) }
      | Return { value } ->
          let e = Option.map ~f:c_expr value in
          let e = Option.value ~default:(unit_expr span) e in
          Return { e; witness = W.early_exit }
      | ConstBlock _ -> failwith "ConstBlock"
      | Repeat _ -> failwith "Repeat"
      | Tuple { fields } ->
          let fields = List.map ~f:c_expr fields in
          let len = List.length fields in
          Construct
            {
              constructor = `TupleCons len;
              constructs_record = false;
              fields =
                List.mapi
                  ~f:(fun i field -> (`TupleField (i, len), field))
                  fields;
              base = None;
            }
      | Array { fields } -> Array (List.map ~f:c_expr fields)
      | Adt { info; base; fields; user_ty } ->
          let constructor = def_id @@ variant_id_of_variant_informations info in
          let base = Option.map ~f:(fun base -> c_expr base.base) base in
          let fields =
            List.map
              ~f:(fun f ->
                let field =
                  def_id
                  @@ append_to_thir_def_id info.type_namespace
                       (List.last_exn f.field.path)
                in
                let value = c_expr f.value in
                (field, value))
              fields
          in
          Construct
            {
              constructs_record = info.constructs_record;
              constructor;
              fields;
              base;
            }
      | Literal { lit } -> Literal (c_lit lit @@ Some typ)
      | NamedConst { def_id = id } -> GlobalVar (def_id id)
      | Closure { movability; body; params; upvars } ->
          let params =
            List.filter_map ~f:(fun p -> Option.map ~f:c_pat p.pat) params
          in
          let body = c_expr body in
          let upvars = List.map ~f:c_expr upvars in
          Closure { body; params; captures = upvars }
      | e -> failwith ("todo expr: " ^ Thir.show_expr_kind e)
    in
    { e = v; span; typ }

  and c_pat (pat : Thir.decorated_for__pat_kind) : pat =
    let span = c_span pat.span in
    let typ = c_ty pat.ty in
    let v =
      match pat.contents with
      | Wild -> PWild
      | AscribeUserType { ascription = { annotation }; subpattern } ->
          let typ, typ_span = c_canonical_user_type_annotation annotation in
          let pat = c_pat subpattern in
          PAscription { typ; typ_span; pat }
      | Binding { mode; mutability; subpattern; ty; var } ->
          let mut = c_mutability W.mutable_variable mutability in
          let subpat =
            Option.map ~f:(c_pat &&& Fn.const W.as_pattern) subpattern
          in
          let typ = c_ty ty in
          let mode = c_binding_mode mode in
          let var = local_ident var in
          PBinding { mut; mode; var; typ; subpat }
      | Variant { info; substs; subpatterns } ->
          let name = def_id @@ variant_id_of_variant_informations info in
          let args = List.map ~f:(c_field_pat info) subpatterns in
          PConstruct { record = info.constructs_record; name; args }
      | Tuple { subpatterns } ->
          let len = List.length subpatterns in
          let args =
            List.mapi
              ~f:(fun i pat ->
                let pat = c_pat pat in
                { field = `TupleField (i, len); pat })
              subpatterns
          in
          PConstruct
            {
              name = `TupleCons (List.length subpatterns);
              args;
              record = false;
            }
      | Deref _ -> failwith "Deref"
      | Constant { value } ->
          let lit = c_constant_kind value in
          PConstant { lit }
      | Array { prefix; suffix; slice } -> failwith "Pat:Array"
      | Or _ -> failwith "Or"
      | Slice _ -> failwith "Slice"
      | Range _ -> failwith "Range"
    in
    { p = v; span; typ }

  and c_field_pat info (field_pat : Thir.field_pat) : field_pat =
    {
      field =
        def_id
        @@ append_to_thir_def_id info.type_namespace
             (List.last_exn field_pat.field.path);
      pat = c_pat field_pat.pattern;
    }

  and c_constant_kind (k : Thir.constant_kind) : literal =
    match k with
    | Ty _ -> raise GotTypeInLitPat
    | Lit lit -> c_lit' lit None
    (* | Val (ZeroSized, _) -> failwith "todo, ZeroSized" *)
    (* | Val (Slice _, _) -> failwith "todo, Slice" *)
    (* | Val ( _, _) -> failwith "todo" *)
    (* | Val (Todo s, _) -> failwith ("TODO node: " ^ s) *)
    | Todo s -> failwith ("TODO node: " ^ s)

  and c_canonical_user_type_annotation
      (annotation : Thir.canonical_user_type_annotation) : ty * span =
    (c_ty annotation.inferred_ty, c_span annotation.span)

  and c_ty (ty : Thir.ty) : ty =
    match ty with
    | Bool -> TBool
    | Char -> TChar
    | Int k -> TInt (c_int_ty k)
    | Uint k -> TInt (c_uint_ty k)
    | Float k -> TFloat
    | Arrow { params; ret } -> TArrow (List.map ~f:c_ty params, c_ty ret)
    | NamedType { def_id = id; generic_args } ->
        let ident = def_id id in
        let args = List.map ~f:c_generic_value generic_args in
        TApp { ident; args }
    | Foreign _ -> failwith "Foreign"
    | Str -> TStr
    | Array (ty, len) ->
        TArray
          {
            typ = c_ty ty;
            length =
              len
              (* TODO *)
              (* length = match len.kind with *)
              (*   | Value -> failwith "value" *)
              (*   | _ -> failwith "Import_thir:Array:len" *);
          }
    | Slice ty ->
        let ty = c_ty ty in
        TSlice { ty; witness = W.slice }
    | RawPtr _ -> TRawPointer { witness = W.raw_pointer }
    | Ref (region, ty, mut) ->
        let typ = c_ty ty in
        let mut = c_mutability W.mutable_reference mut in
        TRef { witness = W.reference; region = "todo"; typ; mut }
    | Never -> TFalse
    | Tuple types ->
        let types = List.map ~f:(fun ty -> GType (c_ty ty)) types in
        TApp { ident = `TupleType (List.length types); args = types }
    | Projection _ -> TProjectedAssociatedType (Thir.show_ty ty)
    | Param { index; name } ->
        (* TODO: [id] might not unique *)
        TParam { name; id = index }
    | _ -> failwith ("TODO typ " ^ Thir.show_ty ty)
  (* fun _ -> Ok Bool *)

  and c_generic_value (ty : Thir.generic_arg) : generic_value =
    match ty with
    | Type ty -> GType (c_ty ty)
    | Const e -> failwith "TODO" (* let* ty = c_ty ty in  *)
    | _ -> GLifetime { lt = "todo generics"; witness = W.lifetime }

  and c_arm (arm : Thir.arm) : arm =
    let pat = c_pat arm.pattern in
    let body = c_expr arm.body in
    let span = c_span arm.span in
    { arm = { pat; body }; span }

  and c_param (param : Thir.param) : param =
    {
      typ_span = Option.map ~f:c_span param.ty_span;
      typ = c_ty param.ty;
      pat = c_pat (Option.value_exn param.pat);
    }

  let c_generic_param (param : Thir.generic_param) : generic_param =
    let ident =
      match param.name with
      | Fresh ->
          (* failwith ("[Fresh] ident? " ^ Thir.show_generic_param param) *)
          (* TODO might be wrong to just have a wildcard here *)
          ({ name = "_"; id = 123456789 } : local_ident)
      | Error -> failwith ("[Error] ident? " ^ Thir.show_generic_param param)
      | Plain n -> local_ident n
    in
    match (param.kind : Thir.generic_param_kind) with
    | Lifetime { kind } -> GPLifetime { ident; witness = W.lifetime }
    | Type { default; synthetic } ->
        let default = Option.map ~f:c_ty default in
        GPType { ident; default }
    | Const { default; ty } -> failwith "TODO: Const"

  let c_predicate_kind (p : Thir.predicate_kind) : trait_ref option =
    match p with
    | Clause (Trait { is_positive = true; is_const = _; trait_ref }) ->
        let args = List.map ~f:c_generic_value trait_ref.substs in
        Some { trait = def_id trait_ref.def_id; args; bindings = [] }
    | _ -> None

  let c_constraint (c : Thir.where_predicate) : generic_constraint list =
    match c with
    | BoundPredicate
        { bound_generic_params; bounded_ty; bounds; hir_id; origin; span } ->
        let typ = c_ty bounded_ty in
        let traits = List.map ~f:c_predicate_kind bounds in
        let traits = List.filter_map ~f:Fn.id traits in
        List.map
          ~f:(fun trait : generic_constraint ->
            GCType { typ; implements = trait })
          traits
    | RegionPredicate _ -> failwith "region prediate"
    | EqPredicate _ -> failwith "EqPredicate"

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
        List.concat_map ~f:c_constraint generics.predicates
        |> list_dedup equal_generic_constraint;
    }

  let c_trait_item' (item : Thir.trait_item_kind) : trait_item' =
    match item with
    | Const (ty, _) ->
        failwith "TODO: traits: no support for defaults in traits for now"
    | Const (ty, None) -> TIFn (c_ty ty)
    | ProvidedFn _ ->
        failwith "TODO: traits: no support for defaults in funcitons for now"
    | RequiredFn (sg, _) ->
        let Thir.{ inputs; output; _ } = sg.decl in
        let output =
          match output with
          | DefaultReturn span -> unit_typ
          | Return ty -> c_ty ty
        in
        (* failwith @@ [%show: Thir.ty list] inputs; *)
        TIFn (TArrow (List.map ~f:c_ty inputs, output))
    | Type ([], None) -> TIType { params = []; constraints = [] }
    | Type (_, None) ->
        failwith "TODO: traits: no support for generics in type for now"
    | Type (_, Some _) ->
        failwith "TODO: traits: no support for defaults in type for now"

  let c_trait_item (item : Thir.trait_item) : trait_item =
    (* Raw_thir_ast.Param { index = 0; name = "Self" } *)
    let { params; constraints } = c_generics item.generics in
    {
      ti_span = c_span item.span;
      ti_generics = { params; constraints };
      ti_v = c_trait_item' item.kind;
      ti_name = fst item.ident;
    }

  let c_item (item : Thir.item) : item =
    let span = c_span item.span in
    let v =
      (* TODO: things might be unnamed (e.g. constants) *)
      match (item.kind : Thir.item_kind) with
      | Const (t, body) ->
          Fn
            {
              name = def_id (Option.value_exn item.def_id);
              generics = { params = []; constraints = [] };
              body = c_expr body;
              params = [];
            }
      | TyAlias (ty, generics) ->
          TyAlias
            {
              name = def_id (Option.value_exn item.def_id);
              generics = c_generics generics;
              ty = c_ty ty;
            }
      | Fn (generics, { body; header; params; ret; sig_span }) ->
          Fn
            {
              name = def_id (Option.value_exn item.def_id);
              generics = c_generics generics;
              body = c_expr body;
              params = List.map ~f:c_param params;
            }
      | Enum (variants, generics) ->
          let name = def_id (Option.value_exn item.def_id) in
          let generics = c_generics generics in
          let variants =
            List.map
              ~f:(fun { ident; data; def_id = variant_id } ->
                match data with
                | Tuple (fields, _, _) | Struct (fields, _) ->
                    let arguments =
                      List.map
                        ~f:(fun { def_id = id; ty } -> (def_id id, c_ty ty))
                        fields
                    in
                    { name = def_id variant_id; arguments }
                | Unit (_, name) -> { name = def_id name; arguments = [] })
              variants
          in
          Type { name; generics; variants; record = true }
      | Struct (v, generics) ->
          let name = def_id (Option.value_exn item.def_id) in
          let generics = c_generics generics in
          let v, record =
            let mk fields =
              let arguments =
                List.map
                  ~f:(fun Thir.{ def_id = id; ty } -> (def_id id, c_ty ty))
                  fields
              in
              { name; arguments }
            in
            match v with
            | Tuple (fields, _, _) -> (mk fields, false)
            | Struct (fields, _) -> (mk fields, true)
            | Unit (_, _) -> ({ name; arguments = [] }, false)
          in
          let variants = [ v ] in
          Type { name; generics; variants; record }
      | MacroInvokation { macro_ident; argument; span } ->
          IMacroInvokation
            {
              macro = def_id macro_ident;
              argument;
              span = c_span span;
              witness = W.macro;
            }
      | Trait (No, Normal, generics, _bounds, items) ->
          let name = def_id (Option.value_exn item.def_id) in
          let { params; constraints } = c_generics generics in
          let params =
            GPType { ident = { name = "Self"; id = 0 }; default = None }
            :: params
          in
          Trait
            {
              name;
              generics = { params; constraints };
              items = List.map ~f:c_trait_item items;
            }
      | Trait (Yes, _, _, _, _) -> failwith "Auto trait"
      | Trait (_, Unsafe, _, _, _) -> failwith "Unsafe trait"
      | _ -> NotImplementedYet
    in
    { span; v; parent_namespace = namespace_of_def_id item.owner_id }
end

let c_item (item : Thir.item) : (item, error) Result.t =
  try Exn.c_item item |> Result.return
  with Exn.ImportError error -> Error error
