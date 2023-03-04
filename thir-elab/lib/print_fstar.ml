open Base
open Ast
open Ast.Make (Features.FStar)
open PPrint
open Utils

let map_first_letter (f : string -> string) (s : string) =
  let first, rest = String.(prefix s 1, drop_prefix s 1) in
  f first ^ rest

(* Helpers for constructing an F* surface AST *)
module F = struct
  module Util = FStar_Parser_Util
  module AST = FStar_Parser_AST
  module Const = FStar_Const
  module Range = FStar_Compiler_Range
  module Char = FStar_Char
  module Ident = FStar_Ident

  let dummyRange = Range.dummyRange
  let id ident = Ident.mk_ident (ident, dummyRange)

  let lid path =
    let init, last = List.(drop_last_exn path, last_exn path) in
    let init = List.map ~f:(map_first_letter String.uppercase) init in
    let path = init @ [ last ] in
    Ident.lid_of_path path dummyRange

  let lid_of_id id = Ident.lid_of_ids [ id ]
  let term (tm : AST.term') = AST.{ tm; range = dummyRange; level = Expr }

  let decl (d : AST.decl') =
    AST.{ d; drange = dummyRange; quals = []; attrs = [] }

  let pat (pat : AST.pattern') = AST.{ pat; prange = dummyRange }

  let pat_var_tcresolve (var : string option) =
    let tcresolve =
      Some (AST.Meta (term @@ AST.Var FStar_Parser_Const.tcresolve_lid))
    in
    pat
    @@
    match var with
    | Some var -> AST.PatVar (id var, tcresolve, [])
    | _ -> AST.PatWild (tcresolve, [])

  let pat_app name l = pat @@ AST.PatApp (name, l)
  let wild = pat @@ AST.PatWild (None, [])

  let mk_e_app base args =
    AST.mkApp base (List.map ~f:(fun arg -> (arg, AST.Nothing)) args) dummyRange

  let mk_e_binder b =
    AST.{ b; brange = dummyRange; blevel = Un; aqual = None; battributes = [] }

  let term_of_lid path = term @@ AST.Name (lid path)
  let binder_of_term (t : AST.term) : AST.binder = mk_e_binder @@ AST.NoName t
  let unit = term AST.(Const Const_unit)

  let mk_e_arrow inputs output =
    term @@ AST.Product (List.map ~f:binder_of_term inputs, output)

  let mk_e_arrow' types =
    let inputs, output = (List.drop_last_exn types, List.last_exn types) in
    mk_e_arrow inputs output

  let mk_refined (x : string) (typ : AST.term) (phi : x:AST.term -> AST.term) =
    let x = id x in
    let x_bd = mk_e_binder @@ AST.Annotated (x, typ) in
    term @@ AST.Refine (x_bd, phi (term @@ AST.Var (lid_of_id x)))
end

module Context = struct
  type t = int
end

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pprim_ident (id : primitive_ident) =
    match id with
    | Box -> failwith "Box"
    | Deref -> failwith "Box"
    | Cast -> failwith "Cast"
    | BinOp op -> (
        match op with
        | Add -> F.lid [ "Prims"; "op_Addition" ]
        | Sub -> F.lid [ "Prims"; "op_Subtraction" ]
        | Mul -> F.lid [ "FStar"; "Mul"; "op_Star" ]
        | Div -> F.lid [ "Prims"; "op_Division" ]
        | Eq -> F.lid [ "Prims"; "op_Equality" ]
        | Lt -> F.lid [ "Prims"; "op_LessThan" ]
        | Le -> F.lid [ "Prims"; "op_LessThanOrEqual" ]
        | Ge -> F.lid [ "Prims"; "op_GreaterThan" ]
        | Gt -> F.lid [ "Prims"; "op_GreaterThanOrEqual" ]
        | Ne -> F.lid [ "Prims"; "op_disEquality" ]
        | Rem -> failwith "TODO: Rem"
        | BitXor -> failwith "TODO: BitXor"
        | BitAnd -> failwith "TODO: BitAnd"
        | BitOr -> failwith "TODO: BitOr"
        | Shl -> failwith "TODO: Shl"
        | Shr -> failwith "TODO: Shr"
        | Offset -> failwith "TODO: Offset")
    | UnOp op -> (
        match op with
        | Not -> F.lid [ "Prims"; "l_Not" ]
        | Neg -> F.lid [ "Prims"; "op_Minus" ])
    | LogicalOp op -> (
        match op with
        | And -> F.lid [ "Prims"; "op_AmpAmp" ]
        | Or -> F.lid [ "Prims"; "op_BarBar" ])

  let rec pliteral (e : literal) =
    match e with
    | String s -> F.Const.Const_string (s, F.dummyRange)
    | Char c -> F.Const.Const_char (Char.to_int c)
    | Int { value } -> F.Const.Const_int (Bigint.to_string value, None)
    | Float _ -> failwith "Float: todo"
    | Bool b -> F.Const.Const_bool b

  let rec pglobal_ident (id : global_ident) =
    match id with
    | `Concrete cid -> F.lid (cid.crate :: Non_empty_list.to_list cid.path)
    | `Primitive prim_id -> pprim_ident prim_id
    | `TupleType 0 -> F.lid [ "prims"; "unit" ]
    | `TupleCons n when n <= 1 ->
        failwith ("Got a [TupleCons " ^ string_of_int n ^ "]")
    | `TupleType n when n <= 14 ->
        F.lid [ "FStar"; "Pervasives"; "tuple" ^ string_of_int n ]
    | `TupleCons n when n <= 14 ->
        F.lid [ "FStar"; "Pervasives"; "Mktuple" ^ string_of_int n ]
    | `TupleType _ | `TupleCons _ ->
        failwith "F* doesn't support tuple of size greater than 14"
    | `TupleField _ | `Projector _ ->
        failwith ("Cannot appear here: " ^ show_global_ident id)

  let rec plocal_ident (e : LocalIdent.t) = F.id e.name

  let pgeneric_param_name (name : string) : string =
    String.lowercase
      name (* TODO: this is not robust, might produce name clashes *)

  let rec map_last_non_empty_list (f : 'a -> 'a) (l : 'a Non_empty_list.t) :
      'a Non_empty_list.t =
    let open Non_empty_list in
    match l with
    | [ x ] -> [ f x ]
    | x :: y :: tl -> cons x @@ map_last_non_empty_list f (y :: tl)

  let map_last_concrete_ident (f : string -> string) (id : concrete_ident) =
    { id with path = map_last_non_empty_list f id.path }

  let map_last_global_ident (f : string -> string) (id : global_ident) =
    match id with
    | `Concrete concrete -> `Concrete (map_last_concrete_ident f concrete)
    | _ -> id

  let lowercase_global_ident : global_ident -> global_ident =
    map_last_global_ident @@ map_first_letter String.lowercase

  let uppercase_global_ident : global_ident -> global_ident =
    map_last_global_ident @@ map_first_letter String.uppercase

  let ptype_ident : global_ident -> F.Ident.lident =
    lowercase_global_ident >> pglobal_ident

  let pconstructor_ident : global_ident -> F.Ident.lident =
    uppercase_global_ident >> pglobal_ident

  let rec pty (t : ty) =
    match t with
    | TBool -> F.term_of_lid [ "Prims"; "bool" ]
    | TChar -> F.term_of_lid [ "FStar"; "Char"; "char" ]
    | TInt k -> F.term_of_lid [ "Prims"; "int" ] (* todo *)
    | TStr -> F.term_of_lid [ "Prims"; "string" ]
    | TFalse -> F.term_of_lid [ "Prims"; "l_False" ]
    | TApp { ident = `TupleType 0 as ident; args = [] } ->
        F.term @@ F.AST.Name (ptype_ident ident)
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty ty
    | TApp { ident = `TupleType n; args } when n >= 2 -> (
        let args =
          List.filter_map
            ~f:(function GType t -> Some (pty t) | _ -> None)
            args
        in
        let mk_star a b = F.term @@ F.AST.Op (F.id "*", [ a; b ]) in
        match args with
        | hd :: tl ->
            F.term @@ F.AST.Paren (List.fold_left ~init:hd ~f:mk_star tl)
        | _ -> failwith "Tuple type: bad arity")
    | TApp { ident; args } ->
        let base = F.term @@ F.AST.Name (ptype_ident ident) in
        let args = List.map ~f:pgeneric_value args in
        F.mk_e_app base args
    | TArrow (inputs, output) ->
        F.mk_e_arrow (List.map ~f:pty inputs) (pty output)
    | TFloat -> failwith "pty: Float"
    | TArray { typ; length } ->
        F.mk_refined "x"
          (F.mk_e_app (F.term_of_lid [ "Prims"; "list" ]) [ pty typ ])
          (fun ~x ->
            let len_of_x =
              F.mk_e_app
                (F.term_of_lid [ "FStar"; "List"; "Tot"; "Base"; "length" ])
                [ x ]
            in
            let lit =
              pliteral
                (Ast.Int
                   {
                     value = Bigint.of_int length;
                     kind = { size = SSize; signedness = Signed };
                   })
            in
            let length = F.term @@ F.AST.Const lit in
            let lt = F.term @@ F.AST.Name (pprim_ident @@ BinOp Lt) in
            F.mk_e_app lt [ len_of_x; length ])
    | TParam i ->
        F.term
        @@ F.AST.Var
             (F.lid_of_id
             @@ plocal_ident { i with name = pgeneric_param_name i.name })
    | TProjectedAssociatedType s ->
        (* F.term @@ F.AST.Const (F.Const.Const_string (show_ty t, F.dummyRange)) *)
        F.term
        @@ F.AST.Const
             (F.Const.Const_string ("TODO:ProjectedType", F.dummyRange))
    (* print_endline @@ show_ty t; *)
    (* failwith ("TODO: print_fstar cannot handle yet: " ^ show_ty t) *)
    | _ -> .

  and pgeneric_value (g : generic_value) =
    match g with
    | GType ty -> pty ty
    | GConst todo -> failwith "pgeneric_arg: Const"
    | GLifetime _ -> .

  let index_of_field = function
    | `Concrete { path } -> (
        try Some (Int.of_string @@ Non_empty_list.last path) with _ -> None)
    | `TupleField (nth, _) -> Some nth
    | _ -> None

  let is_field_an_index = index_of_field >> Option.is_some

  (* let rec pborrow_kind (e : borrow_kind) = failwith "TODO" *)
  let rec ppat (p : pat) =
    match p.p with
    | PWild -> F.wild
    | PAscription { typ; pat } ->
        F.pat @@ F.AST.PatAscribed (ppat pat, (pty typ, None))
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat = None;
          var;
          typ = _ (* we skip type annot here *);
        } ->
        F.pat @@ F.AST.PatVar (plocal_ident var, None, [])
    | PArray { args } -> F.pat @@ F.AST.PatList (List.map ~f:ppat args)
    | PConstruct { name = `TupleCons 0; args = [] } ->
        F.pat @@ F.AST.PatConst F.Const.Const_unit
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } -> ppat pat
    | PConstruct { name = `TupleCons n; args } ->
        F.pat
        @@ F.AST.PatTuple (List.map ~f:(fun { pat } -> ppat pat) args, false)
    | PConstruct { name; args; record } ->
        let pat_rec () =
          F.pat @@ F.AST.PatRecord (List.map ~f:pfield_pat args)
        in
        if record then pat_rec ()
        else
          let pat_name = F.pat @@ F.AST.PatName (pconstructor_ident name) in
          let is_payload_record =
            List.for_all ~f:(fun { field } -> is_field_an_index field) args
            |> not
          in
          F.pat_app pat_name
          @@
          if is_payload_record then [ pat_rec () ]
          else List.map ~f:(fun { field; pat } -> ppat pat) args
    | PConstant { lit } -> F.pat @@ F.AST.PatConst (pliteral lit)
    | PDeref { subpat } -> ppat subpat
    | _ -> .

  and pfield_pat ({ field; pat } : field_pat) = (pglobal_ident field, ppat pat)

  let rec pexpr (e : expr) =
    match e.e with
    | Literal e -> F.term @@ F.AST.Const (pliteral e)
    | LocalVar local_ident ->
        F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident local_ident)
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        F.AST.unit_const F.dummyRange
    | GlobalVar global_ident -> F.term @@ F.AST.Var (pglobal_ident global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        F.term
        @@ F.AST.Project (pexpr arg, F.lid [ "_" ^ string_of_int (n + 1) ])
    | App { f; args } -> F.mk_e_app (pexpr f) @@ List.map ~f:pexpr args
    | If { cond; then_; else_ } ->
        F.term
        @@ F.AST.If
             ( pexpr cond,
               None,
               None,
               pexpr then_,
               Option.value_map else_ ~default:F.unit ~f:pexpr )
    | Array l -> F.AST.mkConsList F.dummyRange (List.map ~f:pexpr l)
    | Let { lhs; rhs; body; monadic = Some monad } ->
        let p = F.pat @@ F.AST.PatAscribed (ppat lhs, (pty lhs.typ, None)) in
        let op = "let" ^ match monad with _ -> "*" in
        F.term @@ F.AST.LetOperator ([ (F.id op, p, pexpr rhs) ], pexpr body)
    | Let { lhs; rhs; body; monadic = None } ->
        let p = F.pat @@ F.AST.PatAscribed (ppat lhs, (pty lhs.typ, None)) in
        F.term
        @@ F.AST.Let (NoLetQualifier, [ (None, (p, pexpr rhs)) ], pexpr body)
    | MonadicAction _ -> .
    | Match { scrutinee; arms } ->
        F.term
        @@ F.AST.Match (pexpr scrutinee, None, None, List.map ~f:parm arms)
    | Ascription { e; typ } ->
        F.term @@ F.AST.Ascribed (pexpr e, pty typ, None, false)
    | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
        pexpr e
    | Construct { constructor = `TupleCons n; fields; base } ->
        F.AST.mkTuple (List.map ~f:(snd >> pexpr) fields) F.dummyRange
    | Construct { constructs_record = true; constructor; fields; base } ->
        F.term
        @@ F.AST.Record
             ( Option.map ~f:pexpr base,
               List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields )
    | Construct { constructs_record = false; constructor; fields; base }
      when List.for_all ~f:(fst >> is_field_an_index) fields ->
        assert (Option.is_none base);
        F.mk_e_app (F.term @@ F.AST.Name (pglobal_ident constructor))
        @@ List.map ~f:(snd >> pexpr) fields
    | Construct { constructs_record = false; constructor; fields; base } ->
        let r =
          F.term
          @@ F.AST.Record
               ( Option.map ~f:pexpr base,
                 List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields
               )
        in
        F.mk_e_app (F.term @@ F.AST.Name (pglobal_ident constructor)) [ r ]
    | Closure { params; body } ->
        F.term
        @@ F.AST.Abs
             ( List.map
                 ~f:(fun p ->
                   F.pat @@ F.AST.PatAscribed (ppat p, (pty p.typ, None)))
                 params,
               pexpr body )
    | Return { e } ->
        F.term @@ F.AST.App (F.term_of_lid [ "RETURN_STMT" ], pexpr e, Nothing)
    | _ -> .

  and parm { arm = { pat; body } } = (ppat pat, None, pexpr body)

  let doc_to_string : document -> string =
    FStar_Pprint.pretty_string 1.0 (Z.of_int 100)

  let term_to_string : F.AST.term -> string =
    FStar_Parser_ToDocument.term_to_document >> doc_to_string

  let decl_to_string : F.AST.decl -> string =
    FStar_Parser_ToDocument.decl_to_document >> doc_to_string

  (* let item_to_string: F.AST.item -> string = *)
  (*   FStar_Parser_ToDocument.decl_to_document >> doc_to_string *)

  (* todo eliminate me *)
  let last_of_global_ident (g : global_ident) =
    match g with
    | `Concrete { path; crate = _ } -> Non_empty_list.last path
    | _ -> failwith "last_of_global_ident"

  (* let rec pgeneric_param' (p : generic_param) *)
  (*   = match p with *)
  (*   | Lifetime {ident} -> failwith "pgeneric_param:LIFETIME" *)
  (*   | Type {ident; default = None} -> *)
  (*     let t = F.term @@ F.AST.Name (F.lid ["Type"]) in *)
  (*     F.mk_e_binder (F.AST.Annotated (plocal_ident ident, t)) *)
  (*   | Type {ident; default = _} -> failwith "pgeneric_param:Type with default" *)
  (*   | Const {ident; typ} -> failwith "todo" *)

  let rec pgeneric_param_bd (p : generic_param) =
    match p with
    | GPLifetime { ident } -> failwith "pgeneric_param:LIFETIME"
    | GPType { ident; default = None } ->
        let t = F.term @@ F.AST.Name (F.lid [ "Type" ]) in
        F.mk_e_binder (F.AST.Annotated (plocal_ident ident, t))
    | GPType { ident; default = _ } ->
        failwith "pgeneric_param:Type with default"
    | GPConst { ident; typ } -> failwith "todo"

  let rec pgeneric_param (p : generic_param) =
    match p with
    | GPLifetime { ident } -> failwith "pgeneric_param:LIFETIME"
    | GPType { ident; default = None } ->
        let v =
          F.pat
          @@ F.AST.PatVar
               ( plocal_ident
                   { ident with name = pgeneric_param_name ident.name },
                 Some F.AST.Implicit,
                 [] )
        in
        let t = F.term @@ F.AST.Name (F.lid [ "Type" ]) in
        F.pat @@ F.AST.PatAscribed (v, (t, None))
    | GPType { ident; default = _ } ->
        failwith "pgeneric_param:Type with default"
    | GPConst { ident; typ } -> failwith "todo"

  let rec pgeneric_constraint (nth : int) (c : generic_constraint) =
    match c with
    | GCLifetime _ -> failwith "pgeneric_constraint lifetime"
    | GCType { typ; implements } ->
        let implements : trait_ref = implements in
        let trait = F.term @@ F.AST.Name (ptype_ident implements.trait) in
        let args = List.map ~f:pgeneric_value implements.args in
        let tc = F.mk_e_app trait (*pty typ::*) args in
        F.pat
        @@ F.AST.PatAscribed
             (F.pat_var_tcresolve @@ Some ("__" ^ string_of_int nth), (tc, None))

  let rec pitem (e : item) =
    match e.v with
    | Fn { name; generics; body; params } ->
        let last_of_global_ident (g : global_ident) =
          match g with
          | `Concrete { path; crate } ->
              String.concat ~sep:"_" @@ (crate :: Non_empty_list.to_list path)
          | _ -> failwith "last_of_global_ident"
        in
        let pat =
          F.pat @@ F.AST.PatVar (F.id @@ last_of_global_ident name, None, [])
        in
        let pat =
          F.pat
          @@ F.AST.PatApp
               ( pat,
                 List.map ~f:pgeneric_param generics.params
                 @ List.mapi ~f:pgeneric_constraint generics.constraints
                 @ List.map
                     ~f:(fun { pat; typ_span; typ } ->
                       F.pat @@ F.AST.PatAscribed (ppat pat, (pty typ, None)))
                     params )
        in
        let pat = F.pat @@ F.AST.PatAscribed (pat, (pty body.typ, None)) in
        F.decl @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, pexpr body) ])
    | TyAlias { name; generics; ty } ->
        let pat =
          F.pat
          @@ F.AST.PatVar
               ( F.id @@ last_of_global_ident @@ lowercase_global_ident name,
                 None,
                 [] )
        in
        F.decl
        @@ F.AST.TopLevelLet
             ( NoLetQualifier,
               [
                 ( F.pat
                   @@ F.AST.PatApp
                        ( pat,
                          List.map ~f:pgeneric_param generics.params
                          @ List.mapi ~f:pgeneric_constraint
                              generics.constraints ),
                   pty ty );
               ] )
    | Type { name; generics; variants = [ variant ]; record = true } ->
        (* let constructors = F.id (last_of_global_ident name), None, [] in *)
        F.decl
        @@ F.AST.Tycon
             ( false,
               false,
               [
                 F.AST.TyconRecord
                   ( F.id @@ last_of_global_ident @@ lowercase_global_ident name,
                     [],
                     (* todo type parameters & constraints *)
                     None,
                     [],
                     List.map
                       ~f:(fun (field, ty) ->
                         (F.id @@ last_of_global_ident field, None, [], pty ty))
                       variant.arguments );
               ] )
    | Type { name; generics; variants } ->
        let self =
          F.term_of_lid [ last_of_global_ident @@ lowercase_global_ident name ]
        in
        let constructors =
          List.map
            ~f:(fun { name; arguments } ->
              ( F.id (last_of_global_ident name),
                Some
                  (let field_indexes =
                     List.map ~f:(fst >> index_of_field) arguments
                   in
                   let is_record_payload =
                     List.exists ~f:Option.is_none field_indexes
                   in
                   if is_record_payload then
                     F.AST.VpRecord
                       ( (* F.id @@ last_of_global_ident @@ lowercase_global_ident name, *)
                         (* [], (\* todo type parameters & constraints *\) *)
                         (* None, *)
                         (* [], *)
                         List.map
                           ~f:(fun (field, ty) ->
                             ( F.id @@ last_of_global_ident field,
                               None,
                               [],
                               pty ty ))
                           arguments,
                         Some self )
                   else
                     F.AST.VpArbitrary
                       (F.term
                       @@ F.AST.Product
                            ( List.map
                                ~f:(fun (_, ty) ->
                                  F.mk_e_binder @@ F.AST.NoName (pty ty))
                                arguments,
                              self ))
                   (* let arguments = *)
                   (*   List.zip arguments () *)
                   (* in *)
                   (* F.AST.VpArbitrary ( *)
                   (*     F.term @@ *)
                   (*       F.AST.Product ( *)
                   (*           List.mapi ~f:(fun nth (field, ty) -> *)
                   (*               let field = last_of_global_ident field in *)
                   (*               let ty = pty ty in *)
                   (*               try let nth' = Int.of_string field in *)
                   (*                   if Int.(nth' <> nth) *)
                   (*                   then failwith "While outputing F*, fields of a struct variant were given in a bad order" *)
                   (*                   else F.AST.NoName ty *)
                   (*               with | _ -> F.AST.Annotated (F.id field, ty) *)
                   (*             ) arguments |> List.map ~f:F.mk_e_binder, *)
                   (*           self *)
                   (*         ) *)
                   (*   ) *)),
                [] ))
            variants
        in
        F.decl
        @@ F.AST.Tycon
             ( false,
               false,
               [
                 F.AST.TyconVariant
                   ( F.id @@ last_of_global_ident @@ lowercase_global_ident name,
                     [],
                     (* todo type parameters & constraints *)
                     None,
                     constructors );
               ] )
    | _ ->
        F.decl
        @@ F.AST.TopLevelLet
             (NoLetQualifier, [ (F.pat @@ F.AST.PatWild (None, []), F.unit) ])
end
