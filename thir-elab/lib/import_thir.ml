module Thir = Raw_thir_ast
open Base
open Ast

let ( let* ) r f = Result.bind r ~f

type error =
  | UnsafeBlock
  | LetElse
  | LetWithoutInit
  | GotErrLiteral
  | BadSpanUnion
  | ShallowMutUnsupported
  | GotTypeInLitPat
[@@deriving show]

type 'a result = ('a, error) Result.t

let loc (loc : Thir.loc) : Ast.loc = { col = loc.col; line = loc.line }

module GlobalNames = struct
  let h v : full expr = { span = Dummy; typ = Ast.False; v = Ast.GlobalVar v }
  let box : full expr = `Primitive Box |> h
  let deref : full expr = `Primitive Box |> h
  let cast : full ty -> full ty -> full expr = fun _ _ -> `Primitive Cast |> h
  let binop : Thir.bin_op -> full expr = fun op -> `Primitive (BinOp op) |> h
  let unop : Thir.un_op -> full expr = fun op -> `Primitive (UnOp op) |> h

  let logicalop : Thir.logical_op -> full expr =
   fun op -> `Primitive (LogicalOp op) |> h

  let tuple_type : int -> full expr = fun len -> h (`Tuple len)
  (* let tuple_field: len:int -> Ast.expr = fun ~len -> h "tuple_field" *)
end

let sequence_result_option (x : 'a result option) : 'a option result =
  match x with
  | None -> Ok None
  | Some (Ok r) -> Ok (Some r)
  | Some (Error e) -> Error e

let string_of_def_path_item : Thir.def_path_item -> string option = function
  | TypeNs s | ValueNs s | MacroNs s | LifetimeNs s -> Some s
  | _ -> None

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

let union_span (x : span) (y : span) : span result =
  match (x, y) with
  | Dummy, _ | _, Dummy -> Ok Dummy
  | Span x, Span y when String.(x.file <> y.file) -> Error BadSpanUnion
  | Span { file; lo }, Span { hi } -> Ok (Span { file; lo; hi })

let c_borrow_kind : Thir.borrow_kind -> full borrow_kind result = function
  | Shared -> Ok Ast.Shared
  | Shallow -> Error ShallowMutUnsupported
  | Unique -> Ok Ast.Unique
  | Mut _ -> Ok (Ast.Mut ())

let c_span (span : Thir.span) : span result =
  Ok
    (Span
       {
         lo = loc span.lo;
         hi = loc span.hi;
         file =
           (match span.filename with Real (LocalPath path) -> path | _ -> "?");
       })

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

let c_mutability (witness : 'a) : bool -> 'a Ast.mutability = function
  | true -> Mutable witness
  | false -> Immutable

let c_binding_mode : Thir.binding_mode -> full binding_mode result = function
  | ByValue -> Ok Ast.ByValue
  | ByRef k ->
      let* k = c_borrow_kind k in
      Ok (Ast.ByRef k)

let unit_typ : 'a ty = App { ident = `Tuple 0; args = [] }

let unit_expr : full expr =
  {
    typ = unit_typ;
    span = Dummy;
    v =
      Ast.App
        {
          f =
            {
              v = Ast.GlobalVar (`Tuple 0);
              span = Dummy;
              typ = Ast.Arrow ([], unit_typ);
            };
          args = [];
        };
  }

let wild_pat : full ty -> full pat = fun typ -> { typ; span = Dummy; v = Wild }

let c_lit' (lit : Thir.lit_kind) : literal result =
  match lit with
  | Err -> Error GotErrLiteral
  | Str (str, _) -> Ok (String str)
  | ByteStr _ -> failwith "todo"
  | Byte _ -> failwith "todo"
  | Char s -> Ok (String s)
  | Int (i, t) ->
      Ok
        (Int
           {
             value = Bigint.of_int i;
             kind =
               { size = S8; signedness = Unsigned }
               (* kind = (match t with _ -> failwith "lit: int" (\* TODO *\)); *);
           })
  | Float _ -> failwith "todo float"
  | Bool b -> Ok (Bool b)

let c_lit (lit : Thir.spanned_for__lit_kind) : literal result = c_lit' lit.node

let rec c_expr (e : Thir.decorated_for__expr_kind) : full expr result =
  let call f args =
    Result.all (List.map ~f:c_expr args)
    |> Result.map ~f:(fun args -> App { f; args })
  in
  let* typ = c_ty e.ty in
  let* (v : full expr') =
    match e.contents with
    | Box { value } -> call GlobalNames.box [ value ]
    | MacroInvokation { argument; macro_ident } ->
        Ok
          (MacroInvokation
             { args = argument; macro = def_id macro_ident; witness = () })
    | If { cond; if_then_scope = _; else_opt; then' } ->
        let* cond = c_expr cond in
        let* then_ = c_expr then' in
        let* else_ = Option.map ~f:c_expr else_opt |> sequence_result_option in
        Ok (If { cond; else_; then_ })
    | Call { args; fn_span = _; from_hir_call = _; fun'; ty = _ } ->
        let* args = List.map ~f:c_expr args |> Result.all in
        let* f = c_expr fun' in
        Ok (App { f; args })
    | Deref { arg } -> call GlobalNames.box [ arg ]
    | Binary { lhs; rhs; op } -> call (GlobalNames.binop op) [ lhs; rhs ]
    | LogicalOp { lhs; rhs; op } -> call (GlobalNames.logicalop op) [ lhs; rhs ]
    | Unary { arg; op } -> call (GlobalNames.unop op) [ arg ]
    | Cast { source } ->
        let from_ty = typ in
        let* to_ty = c_ty source.ty in
        call (GlobalNames.cast from_ty to_ty) [ source ]
    | Use _ -> failwith "use"
    | NeverToAny _ -> failwith "NeverToAny"
    | Pointer _ -> failwith "Pointer"
    | Loop { body } ->
        let* body = c_expr body in
        Ok (Loop { body; label = None; witness = () })
    | Match { scrutinee; arms } ->
        let* scrutinee = c_expr scrutinee in
        let* arms = List.map ~f:c_arm arms |> Result.all in
        Ok (Match { scrutinee; arms })
    | Let _ -> failwith "TODO: Let"
    | Block { safety_mode = BuiltinUnsafe | ExplicitUnsafe } ->
        Error UnsafeBlock
    | Block o ->
        let init =
          Option.map ~f:c_expr o.expr |> Option.value ~default:(Ok unit_expr)
        in
        let* { v } =
          List.fold_right o.stmts ~init ~f:(fun { kind } body ->
              let* body = body in
              match kind with
              | Expr { expr = rhs } ->
                  let* rhs = c_expr rhs in
                  let v = Let { lhs = wild_pat rhs.typ; rhs; body } in
                  let* span = union_span rhs.span body.span in
                  Ok ({ v; typ; span } : _ expr)
              | Let { else_block = Some _ } -> Error LetElse
              | Let { initializer' = None } -> Error LetWithoutInit
              | Let { pattern = lhs; initializer' = Some rhs } ->
                  let* lhs = c_pat lhs in
                  let* rhs = c_expr rhs in
                  let v = Let { lhs; rhs; body } in
                  let* span = union_span rhs.span body.span in
                  Ok ({ v; typ; span } : _ expr))
        in
        Ok v
    | Assign { lhs; rhs } ->
        let* lhs = c_expr lhs in
        let* e = c_expr rhs in
        let lhs : _ lhs =
          match lhs.v with
          | LocalVar ident -> LhsLocalVar ident
          | _ -> failwith ("TODO:Expr:Assign" ^ "show_expr lhs")
        in
        Ok (Assign { lhs; e; witness = () })
    | AssignOp _ -> failwith "AssignOp"
    | VarRef { id } -> Ok (LocalVar (local_ident id))
    | Field { lhs; field } ->
        let* lhs = c_expr lhs in
        let projector =
          GlobalVar (`Projector (`Concrete (concrete_of_def_id field)))
        in
        let* span = c_span e.span in
        Ok
          (App
             {
               f = { v = projector; typ = Arrow ([ lhs.typ ], typ); span };
               args = [ lhs ];
             })
    | TupleField { lhs; field } ->
        (* TODO: refactor *)
        let* lhs = c_expr lhs in
        let projector = GlobalVar (`Projector (`TupleField field)) in
        let* span = c_span e.span in
        Ok
          (App
             {
               f = { v = projector; typ = Arrow ([ lhs.typ ], typ); span };
               args = [ lhs ];
             })
    | GlobalName { id } -> Ok (GlobalVar (def_id id))
    | UpvarRef _ -> failwith "upvar ref"
    | Borrow { arg; borrow_kind = kind } ->
        let* e = c_expr arg in
        let* kind = c_borrow_kind kind in
        Ok (Borrow { kind; e })
    | AddressOf { arg; mutability = mut } ->
        let* e = c_expr arg in
        Ok (AddressOf { e; mut = c_mutability () mut; witness = () })
    | Break { label; value = Some _ } ->
        failwith "TODO: Break with labels are not supported"
    | Break { label; value } ->
        let* e = Option.map ~f:c_expr value |> sequence_result_option in
        Ok (Break { e; label = None; witness = () })
    | Continue _ -> failwith "Continue"
    | Return { value } ->
        let* e = Option.map ~f:c_expr value |> sequence_result_option in
        Ok (Return { e; witness = () })
    | ConstBlock _ -> failwith "ConstBlock"
    | Repeat _ -> failwith "Repeat"
    | Tuple { fields } ->
        (* let* fields = List.map ~f:c_expr fields |> Result.all in *)
        call (GlobalNames.tuple_type (List.length fields)) fields
        (* Ok ( fields) *)
    | Array { fields } ->
        let* fields = List.map ~f:c_expr fields |> Result.all in
        Ok (Array fields)
    | Adt { base; fields; variant; user_ty } ->
        let* base =
          Option.map ~f:(fun base -> c_expr base.base) base
          |> sequence_result_option
        in
        let* fields =
          List.map
            ~f:(fun f ->
              let* value = c_expr f.value in
              Ok (def_id f.field, value))
            fields
          |> Result.all
        in
        Ok (Record { fields; base })
    | Literal { lit } ->
        let* lit = c_lit lit in
        Ok (Literal lit)
    | e -> failwith ("todo expr: " ^ Thir.show_expr_kind e)
  in
  let* span = c_span e.span in
  Ok ({ v; span; typ } : _ expr)

and c_pat (pat : Thir.decorated_for__pat_kind) : full pat result =
  let* span = c_span pat.span in
  let* typ = c_ty pat.ty in
  let* v =
    match pat.contents with
    | Wild -> Ok Wild
    | AscribeUserType { ascription = { annotation }; subpattern } ->
        let* typ = c_canonical_user_type_annotation annotation in
        let* pat = c_pat subpattern in
        Ok (PatAscription { typ; pat })
    | Binding { mode; mutability; subpattern; ty; var } ->
        let mut = c_mutability () mutability in
        let* subpat =
          Option.map
            ~f:(fun pat ->
              let* pat = c_pat pat in
              Ok (pat, ()))
            subpattern
          |> sequence_result_option
        in
        let* typ = c_ty ty in
        let* mode = c_binding_mode mode in
        let var = local_ident var in
        Ok (Binding { mut; mode; var; typ; subpat })
    | Variant { variant; substs; subpatterns } ->
        let name = def_id variant in
        let* args = List.map ~f:c_field_pat subpatterns |> Result.all in
        Ok (Variant { name; args })
    | Tuple { subpatterns } ->
        let* args =
          List.mapi
            ~f:(fun i pat ->
              let* pat = c_pat pat in
              Ok { field = `TupleField i; pat })
            subpatterns
          |> Result.all
        in
        Ok (Variant { name = `Tuple (List.length subpatterns); args })
    | Deref _ -> failwith "Deref"
    | Constant { value } ->
        let* lit = c_constant_kind value in
        Ok (Constant { lit })
    | Array { prefix; suffix; slice } -> failwith "Pat:Array"
    | Or _ -> failwith "Or"
    | Slice _ -> failwith "Slice"
    | Range _ -> failwith "Range"
  in
  Ok ({ v; span; typ } : _ pat)

and c_field_pat (field_pat : Thir.field_pat) : full field_pat result =
  let field = def_id field_pat.field in
  let* pat = c_pat field_pat.pattern in
  Ok { field; pat }

and c_constant_kind (k : Thir.constant_kind) : literal result =
  match k with
  | Ty _ -> Error GotTypeInLitPat
  | Lit lit -> c_lit' lit
  (* | Val (ZeroSized, _) -> failwith "todo, ZeroSized" *)
  (* | Val (Slice _, _) -> failwith "todo, Slice" *)
  (* | Val ( _, _) -> failwith "todo" *)
  (* | Val (Todo s, _) -> failwith ("TODO node: " ^ s) *)
  | Todo s -> failwith ("TODO node: " ^ s)

and c_canonical_user_type_annotation
    (annotation : Thir.canonical_user_type_annotation) : full ty spanned result
    =
  let* span = c_span annotation.span in
  let* v = c_ty annotation.inferred_ty in
  (* TODO: use user's type instead of inferred type? *)
  Ok ({ v; span } : _ spanned)

and c_ty (ty : Thir.ty) : full ty result =
  match ty with
  | Bool -> Ok Bool
  | Char -> Ok Char
  | Int k ->
      let k = c_int_ty k in
      Ok (Int k)
  | Uint k ->
      let k = c_uint_ty k in
      Ok (Int k)
  | Float k -> Ok Float
  | Arrow { params; ret } ->
      let* params = List.map ~f:c_ty params |> Result.all in
      let* ret = c_ty ret in
      Ok (Arrow (params, ret))
  | NamedType { def_id = id; generic_args } ->
      let ident = def_id id in
      let* args = List.map ~f:c_generic_arg generic_args |> Result.all in
      Ok (App { ident; args } : _ ty)
  | Foreign _ -> failwith "Foreign"
  | Str -> Ok Str
  | Array (ty, len) -> failwith "len array TODO"
  | Slice ty ->
      let* ty = c_ty ty in
      Ok (Slice { ty; witness = () })
  | RawPtr _ -> Ok (RawPointer { witness = () })
  | Ref (region, ty, mut) ->
      let* typ = c_ty ty in
      let mut = c_mutability () mut in
      Ok (Ref { witness = (); region = "todo"; typ; mut })
  | Never -> Ok False
  | Tuple types ->
      let* types = List.map ~f:c_ty types |> Result.all in
      let types = List.map ~f:(fun ty -> Type ty) types in
      Ok (App { ident = `Tuple (List.length types); args = types } : _ ty)
      (* Ok(TyTuple(types)) *)
  | Projection _ -> Ok (ProjectedAssociatedType (Thir.show_ty ty))
  | _ -> failwith ("TODO typ " ^ Thir.show_ty ty)
(* fun _ -> Ok Bool *)

and c_int_ty (ty : Thir.int_ty) : int_kind =
  { size = int_ty_to_size ty; signedness = Signed }

and c_uint_ty (ty : Thir.uint_ty) : int_kind =
  { size = uint_ty_to_size ty; signedness = Signed }

and c_generic_arg (ty : Thir.generic_arg) : full generic_arg result =
  match ty with
  | Type ty ->
      let* ty = c_ty ty in
      Ok (Type ty)
  | Const _ -> failwith "const generic: todo (those should just be expressions)"
  | _ -> Ok (Lifetime "todo generics")

and c_arm (arm : Thir.arm) : full arm result =
  let* pat = c_pat arm.pattern in
  let* body = c_expr arm.body in
  let* span = c_span arm.span in
  Ok ({ v = { pat; body }; span } : _ arm)

let c_param (param : Thir.param) : full param result =
  let* pat = c_pat (Option.value_exn param.pat) in
  let* typ = c_ty param.ty in
  let* typ_span =
    Option.map ~f:c_span param.ty_span |> sequence_result_option
  in
  Ok { typ_span; typ; pat }

let c_item (item : Thir.item) : full item result =
  let* span = c_span item.span in
  let* v =
    match item.kind with
    | Fn (generics, { body; header; params; ret; sig_span }) ->
        let generics = () (* TODO! *) in
        let* body = c_expr body in
        let* params = List.map ~f:c_param params |> Result.all in
        Ok
          (Fn
             {
               name = def_id (Option.value_exn item.def_id);
               generics;
               body;
               params;
             })
    | _ -> Ok NotImplementedYet
  in
  Ok ({ span; v } : _ item)
