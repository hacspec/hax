module Thir = Raw_thir_ast
open Base
module Ast = struct
  include Ast
  include Ast.Make(Features.Rust)
end
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

let c_borrow_kind : Thir.borrow_kind -> borrow_kind result = function
  | Shared -> Ok Ast.Shared
  | Shallow -> Error ShallowMutUnsupported
  | Unique -> Ok Ast.Unique
  | Mut _ -> Ok (Ast.Mut ())

let c_binding_mode : Thir.binding_mode -> binding_mode result = function
  | ByValue -> Ok Ast.ByValue
  | ByRef k ->
      let* k = c_borrow_kind k in
      Ok (Ast.ByRef (k, ()))

let unit_typ : ty = TApp { ident = `TupleType 0; args = [] }

let unit_expr : expr =
  {
    typ = unit_typ;
    span = Dummy;
    e =
      Ast.App
        {
          f =
            {
              e = Ast.GlobalVar (`TupleCons 0);
              span = Dummy;
              typ = unit_typ;
            };
          args = [];
        };
  }

let wild_pat : ty -> pat = fun typ -> { typ; span = Dummy; p = PWild }

module GlobalNames = struct
  let h v : expr = { span = Dummy; typ = Ast.TFalse; e = Ast.GlobalVar v }
  let box : expr = `Primitive Box |> h
  let deref : expr = `Primitive Box |> h
  let cast : ty -> ty -> expr = fun _ _ -> `Primitive Cast |> h
  let binop : ty -> ty -> ty -> Thir.bin_op -> expr
    = fun l r out op -> 
    { span = Dummy;
      typ = Ast.TArrow ([l; r], out);
      e = Ast.GlobalVar (`Primitive (BinOp op))
    }
  let unop : Thir.un_op -> expr = fun op -> `Primitive (UnOp op) |> h

  let logicalop : Thir.logical_op -> expr =
   fun op -> `Primitive (LogicalOp op) |> h

  let tuple_type : int -> expr = fun len -> h (`TupleType len)
  (* let tuple_field: len:int -> Ast.expr = fun ~len -> h "tuple_field" *)
end

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
             value = i;
             kind =
               { size = S8; signedness = Unsigned }
               (* kind = (match t with _ -> failwith "lit: int" (\* TODO *\)); *);
           })
  | Float _ -> failwith "todo float"
  | Bool b -> Ok (Bool b)

let c_lit (lit : Thir.spanned_for__lit_kind) : literal result = c_lit' lit.node

let append_to_thir_def_id (def_id: Thir.def_id) (item: Thir.def_path_item) =
  { def_id with path = def_id.path @ [item] }
    
let variant_id_of_variant_informations (info: Thir.variant_informations) =
  let is_def_id_prefix (x: Thir.def_id) (y: Thir.def_id): bool =
    String.(x.krate = y.krate) && List.is_prefix ~prefix:x.path ~equal:Thir.equal_def_path_item y.path
  in
  if not (is_def_id_prefix info.type_namespace info.variant)
  then failwith ("variant_id_of_variant_informations: ["
                 ^ Thir.show_def_id info.type_namespace ^
                   "] is not a prefix of ["
                 ^ Thir.show_def_id info.variant ^
                   "]");
  append_to_thir_def_id info.type_namespace (List.last_exn info.variant.path)

let rec c_expr (e : Thir.decorated_for__expr_kind) : expr result =
  let call f args =
    Result.all (List.map ~f:c_expr args)
    |> Result.map ~f:(fun args -> App { f; args })
  in
  let* typ = c_ty e.ty in
  let* (v : expr') =
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
    | Binary { lhs; rhs; op } ->
        let* lty = c_ty lhs.ty in
        let* rty = c_ty rhs.ty in
        call (GlobalNames.binop lty rty typ op) [ lhs; rhs ]
    | LogicalOp { lhs; rhs; op } -> call (GlobalNames.logicalop op) [ lhs; rhs ]
    | Unary { arg; op } -> call (GlobalNames.unop op) [ arg ]
    | Cast { source } ->
        let from_ty = typ in
        let* to_ty = c_ty source.ty in
        call (GlobalNames.cast from_ty to_ty) [ source ]
    | Use { source } ->
      let* source = c_expr source in
      Ok source.e
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
        let* { e } =
          List.fold_right o.stmts ~init ~f:(fun { kind } body ->
              let* body = body in
              match kind with
              | Expr { expr = rhs } ->
                  let* rhs = c_expr rhs in
                  let e = Let { lhs = wild_pat rhs.typ; rhs; body } in
                  let* span = union_span rhs.span body.span in
                  Ok ({ e; typ; span } : expr)
              | Let { else_block = Some _ } -> Error LetElse
              | Let { initializer' = None } -> Error LetWithoutInit
              | Let { pattern = lhs; initializer' = Some rhs } ->
                  let* lhs = c_pat lhs in
                  let* rhs = c_expr rhs in
                  let e = Let { lhs; rhs; body } in
                  let* span = union_span rhs.span body.span in
                  Ok ({ e; typ; span } : expr))
        in
        Ok e
    | Assign { lhs; rhs } ->
        let* lhs = c_expr lhs in
        let* e = c_expr rhs in
        let lhs =
          match lhs.e with
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
               f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
               args = [ lhs ];
             })
    | TupleField { lhs; field } ->
      (* TODO: refactor *)
        let tuple_len = 0 (* todo, lookup type *) in
        let* lhs = c_expr lhs in
        let projector = GlobalVar (`Projector (`TupleField (field, tuple_len))) in
        let* span = c_span e.span in
        Ok
          (App
             {
               f = { e = projector; typ = TArrow ([ lhs.typ ], typ); span };
               args = [ lhs ];
             })
    | GlobalName { id } -> Ok (GlobalVar (def_id id))
    | UpvarRef _ -> failwith "upvar ref"
    | Borrow { arg; borrow_kind = kind } ->
        let* e = c_expr arg in
        let* kind = c_borrow_kind kind in
        Ok (Borrow { kind; e; witness = () })
    | AddressOf { arg; mutability = mut } ->
        let* e = c_expr arg in
        Ok (AddressOf { e; mut = c_mutability () mut; witness = () })
    | Break { label; value = Some _ } ->
        failwith "TODO: Break with labels are not supported"
    | Break { label; value } ->
        let* e = Option.map ~f:c_expr value |> sequence_result_option in
        let e = Option.value ~default:unit_expr e in
        Ok (Break { e; label = None; witness = () })
    | Continue _ -> failwith "Continue"
    | Return { value } ->
       let* e = Option.map ~f:c_expr value |> sequence_result_option in
       let e = Option.value ~default:unit_expr e in
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
    | Adt { info; base; fields; user_ty } ->
        let constructor = def_id @@ variant_id_of_variant_informations info in
        let* base =
          Option.map ~f:(fun base -> c_expr base.base) base
          |> sequence_result_option
        in
        let* fields =
          List.map
            ~f:(fun f ->
              let field = def_id @@ append_to_thir_def_id info.type_namespace (List.last_exn f.field.path) in
              let* value = c_expr f.value in
              Ok (field, value))
            fields
          |> Result.all
        in
        Ok (Construct { constructs_record = info.constructs_record; constructor; fields; base })
    | Literal { lit } ->
        let* lit = c_lit lit in
        Ok (Literal lit)
    | e -> failwith ("todo expr: " ^ Thir.show_expr_kind e)
  in
  let* span = c_span e.span in
  Ok ({ e = v; span; typ } : expr)

and c_pat (pat : Thir.decorated_for__pat_kind) : pat result =
  let* span = c_span pat.span in
  let* typ = c_ty pat.ty in
  let* v =
    match pat.contents with
    | Wild -> Ok PWild
    | AscribeUserType { ascription = { annotation }; subpattern } ->
        let* (typ, typ_span) = c_canonical_user_type_annotation annotation in
        let* pat = c_pat subpattern in
        Ok (PAscription { typ; typ_span; pat })
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
        Ok (PBinding { mut; mode; var; typ; subpat })
    | Variant { info; substs; subpatterns } ->
        let name = def_id @@ variant_id_of_variant_informations info in
        let* args = List.map ~f:(c_field_pat info) subpatterns |> Result.all in
        Ok (PConstruct { record = info.constructs_record; name; args })
    | Tuple { subpatterns } ->
        let len = List.length subpatterns in
        let* args =
          List.mapi
            ~f:(fun i pat ->
              let* pat = c_pat pat in
              Ok { field = `TupleField (i, len); pat })
            subpatterns
          |> Result.all
        in
        Ok (PConstruct { name = `TupleCons (List.length subpatterns); args; record = false })
    | Deref _ -> failwith "Deref"
    | Constant { value } ->
        let* lit = c_constant_kind value in
        Ok (PConstant { lit })
    | Array { prefix; suffix; slice } -> failwith "Pat:Array"
    | Or _ -> failwith "Or"
    | Slice _ -> failwith "Slice"
    | Range _ -> failwith "Range"
  in
  Ok ({ p = v; span; typ } : pat)

and c_field_pat info (field_pat : Thir.field_pat) : field_pat result =
  let field = def_id @@ append_to_thir_def_id info.type_namespace (List.last_exn field_pat.field.path) in
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
    (annotation : Thir.canonical_user_type_annotation) : (ty * span) result
    =
  let* span = c_span annotation.span in
  let* typ = c_ty annotation.inferred_ty in
  (* TODO: use user's type instead of inferred type? *)
  Ok (typ, span)

and c_ty (ty : Thir.ty) : ty result =
  match ty with
  | Bool -> Ok TBool
  | Char -> Ok TChar
  | Int k ->
      let k = c_int_ty k in
      Ok (TInt k)
  | Uint k ->
      let k = c_uint_ty k in
      Ok (TInt k)
  | Float k -> Ok TFloat
  | Arrow { params; ret } ->
      let* params = List.map ~f:c_ty params |> Result.all in
      let* ret = c_ty ret in
      Ok (TArrow (params, ret))
  | NamedType { def_id = id; generic_args } ->
      let ident = def_id id in
      let* args = List.map ~f:c_generic_value generic_args |> Result.all in
      Ok (TApp { ident; args } : ty)
  | Foreign _ -> failwith "Foreign"
  | Str -> Ok TStr
  | Array (ty, len) -> failwith "len array TODO"
  | Slice ty ->
      let* ty = c_ty ty in
      Ok (TSlice { ty; witness = () })
  | RawPtr _ -> Ok (TRawPointer { witness = () })
  | Ref (region, ty, mut) ->
      let* typ = c_ty ty in
      let mut = c_mutability () mut in
      Ok (TRef { witness = (); region = "todo"; typ; mut })
  | Never -> Ok TFalse
  | Tuple types ->
      let* types = List.map ~f:c_ty types |> Result.all in
      let types = List.map ~f:(fun ty -> GType ty) types in
      Ok (TApp { ident = `TupleType (List.length types); args = types } : ty)
      (* Ok(TyTuple(types)) *)
  | Projection _ -> Ok (TProjectedAssociatedType (Thir.show_ty ty))
  | Param {index; name} ->
     (* TODO: [id] might not unique *)
     Ok (TParam { name; id = index })
  | _ -> failwith ("TODO typ " ^ Thir.show_ty ty)
(* fun _ -> Ok Bool *)

and c_int_ty (ty : Thir.int_ty) : int_kind =
  { size = int_ty_to_size ty; signedness = Signed }

and c_uint_ty (ty : Thir.uint_ty) : int_kind =
  { size = uint_ty_to_size ty; signedness = Signed }

and c_generic_value (ty : Thir.generic_arg) : generic_value result =
  match ty with
  | Type ty ->
      let* ty = c_ty ty in
      Ok (GType ty : generic_value)
  | Const e -> failwith "TODO"
      (* let* ty = c_ty ty in  *)
  | _ -> Ok (GLifetime {lt = "todo generics"; witness = ()})

and c_arm (arm : Thir.arm) : arm result =
  let* pat = c_pat arm.pattern in
  let* body = c_expr arm.body in
  let* span = c_span arm.span in
  Ok { arm = { pat; body }; span }

let c_param (param : Thir.param) : param result =
  let* pat = c_pat (Option.value_exn param.pat) in
  let* typ = c_ty param.ty in
  let* typ_span =
    Option.map ~f:c_span param.ty_span |> sequence_result_option
  in
  Ok { typ_span; typ; pat }

let c_generic_param (param: Thir.generic_param): generic_param result
  = let ident = match param.name with
      | Fresh -> (* failwith ("[Fresh] ident? " ^ Thir.show_generic_param param) *)
        (* TODO might be wrong to just have a wildcard here *)
        ({ name = "_"; id = 123456789 } : local_ident)
      | Error -> failwith ("[Error] ident? " ^ Thir.show_generic_param param)
      | Plain n -> local_ident n
  in
    match (param.kind : Thir.generic_param_kind) with
  | Lifetime {kind} -> Ok (Lifetime {ident; witness = ()})
  | Type {default; synthetic} ->
    let* default = sequence_result_option @@ Option.map ~f:c_ty default in
    Ok (Type {ident; default} : generic_param)
  | Const {default; ty} -> Obj.magic ()
    failwith "TODO: Const"

(* let c_generic_bound (c: Thir.generic_bound) *)
(*   : trait_ref result *)
(*   = match c with *)
(*   | _ -> failwith "TODO" *)

let c_predicate_kind (p: Thir.predicate_kind): trait_ref option result
  = match p with
  | Clause (Trait {is_positive = true; is_const = _; trait_ref }) ->

     let* args = List.map ~f:c_generic_value trait_ref.substs |> Result.all in
     Ok (Some {
            trait = def_id trait_ref.def_id;
            args;
            bindings = []
       })
  | _ -> Ok None

let c_constraint (c: Thir.where_predicate)
  : generic_constraint list result
  = match c with
  | BoundPredicate {
      bound_generic_params;
      bounded_ty;
      bounds;
      hir_id;
      origin;
      span
    } ->
     let* typ = c_ty bounded_ty in
     let* traits = List.map ~f:c_predicate_kind bounds |> Result.all in
     let traits = List.filter_map ~f:Fn.id traits in
     Ok (List.map ~f:(fun trait -> (Type {typ; implements = trait} : generic_constraint)) traits)
  | RegionPredicate _ -> failwith "region prediate"
  | EqPredicate _ -> failwith "EqPredicate"

let list_dedup (equal: 'a -> 'a -> bool): 'a list -> 'a list
  = let rec aux (seen: 'a list) (todo: 'a list): 'a list
    = match todo with
    | hd::tl ->
      if List.mem ~equal seen hd
      then     aux seen tl
      else hd::aux (hd::seen) tl
    | _ -> todo
  in aux []
                       
let c_generics (generics: Thir.generics): generics result =
  let* params = List.map ~f:c_generic_param generics.params
                |> Result.all in
  let* constraints = List.map ~f:c_constraint generics.predicates
                |> Result.all in
  Ok { params; constraints = List.concat constraints |> list_dedup equal_generic_constraint }

let c_item (item : Thir.item) : item result =
  let* span = c_span item.span in
  let* v =
    match item.kind with
    | Fn (generics, { body; header; params; ret; sig_span }) ->
        let* generics = c_generics generics in
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
    | Enum (variants, generics) ->
       let name = def_id (Option.value_exn item.def_id) in
       let* generics = c_generics generics in
       let* variants = List.map ~f:(fun {ident; data; def_id = variant_id} ->
              match data with
               | Tuple (fields, _, _)              
               | Struct (fields, _) ->
                  let* arguments = List.map ~f:(fun {def_id = id; ty} ->
                        let* ty = c_ty ty in
                        Ok (def_id id, ty)
                      ) fields |> Result.all in
                  Ok {name = def_id variant_id; arguments}
              | Unit (_, name) -> Ok ({name = def_id name; arguments = []})) variants
          |> Result.all in
        Ok (Type {
           name;
           generics; variants; record = true
         })
    | Struct (v, generics) ->
       let name = def_id (Option.value_exn item.def_id) in
       let* generics = c_generics generics in
       let* v = match v with
          | Tuple (fields, _, _) -> List.map ~f:Thir.show_hir_field_def fields |> String.concat ~sep:";" |> failwith
          | Struct (fields, _) ->
              let* arguments = List.map ~f:(fun {def_id = id; ty} ->
                    let* ty = c_ty ty in
                    Ok (def_id id, ty)
                  ) fields |> Result.all in
              Ok {name; arguments}
          (* | Tuple (_, _, _) -> Ok ({name; arguments = []}) *)
          | Unit (_, _) -> Ok ({name; arguments = []}) in
       let variants = [v] in
       Ok (Type {
               name;
               generics; variants; record = true
         })
    | _ -> Ok NotImplementedYet
  in
  Ok ({ span; v } : item)
