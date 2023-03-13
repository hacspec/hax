open Utils
open Base

module FStarBackend = struct
  let name = "fstar"

  module InputLanguage = struct
    open Features
    include Off
    include On.Monadic_binding
    include On.Macro
  end

  module RejectNotFStar (FA : Features.T) = struct
    module FB = InputLanguage

    include
      Feature_gate.Make (FA) (FB)
        (struct
          module A = FA
          module B = FB
          include Feature_gate.DefaultSubtype

          let mutable_variable = reject
          let loop = reject
          let continue = reject
          let mutable_reference = reject
          let mutable_pointer = reject
          let mutable_borrow = reject
          let reference = reject
          let slice = reject
          let raw_pointer = reject
          let early_exit _ = Obj.magic ()
          let macro _ = Features.On.macro
          let as_pattern = reject
          let lifetime = reject
          let monadic_action = reject
          let arbitrary_lhs = reject
          let monadic_binding _ = Features.On.monadic_binding
          let for_loop = reject
          let metadata = Desugar_utils.Metadata.make "RejectNotFStar"
        end)
  end

  module AST = Ast.Make (InputLanguage)

  module BackendOptions = struct
    open Cmdliner

    type t = ()

    let parse = Term.(const ())
  end

  open Ast
  module U = Ast_utils.Make (InputLanguage)
  open AST

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
      let last = if String.(last = "new") then "new_" else last in
      let init = List.map ~f:(map_first_letter String.uppercase) init in
      let path = init @ [ last ] in
      Ident.lid_of_path path dummyRange

    let lid_of_id id = Ident.lid_of_ids [ id ]
    let term (tm : AST.term') = AST.{ tm; range = dummyRange; level = Expr }

    let decl ?(quals = []) (d : AST.decl') =
      AST.{ d; drange = dummyRange; quals = []; attrs = [] }

    let decls ?(quals = []) x = [ decl ~quals x ]
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
      AST.mkApp base
        (List.map ~f:(fun arg -> (arg, AST.Nothing)) args)
        dummyRange

    let mk_e_binder b =
      AST.
        { b; brange = dummyRange; blevel = Un; aqual = None; battributes = [] }

    let term_of_lid path = term @@ AST.Name (lid path)
    let binder_of_term (t : AST.term) : AST.binder = mk_e_binder @@ AST.NoName t
    let unit = term AST.(Const Const_unit)

    let mk_e_arrow inputs output =
      term @@ AST.Product (List.map ~f:binder_of_term inputs, output)

    let mk_e_arrow' types =
      let inputs, output = (List.drop_last_exn types, List.last_exn types) in
      mk_e_arrow inputs output

    let mk_refined (x : string) (typ : AST.term) (phi : x:AST.term -> AST.term)
        =
      let x = id x in
      let x_bd = mk_e_binder @@ AST.Annotated (x, typ) in
      term @@ AST.Refine (x_bd, phi (term @@ AST.Var (lid_of_id x)))

    let parse_string f s =
      let open FStar_Parser_ParseIt in
      let frag_of_text s =
        {
          frag_fname = "<string_of_term>";
          frag_line = Z.of_int 1;
          frag_col = Z.of_int 0;
          frag_text = s;
        }
      in
      match parse (f (frag_of_text s)) with
      | ParseError (_, err, _) -> failwith ("string_of_term: got error " ^ err)
      | x -> x

    let term_of_string s =
      match parse_string (fun x -> Fragment x) s with
      | Term t -> t
      | _ -> failwith "parse failed"

    let decls_of_string s =
      match parse_string (fun x -> Toplevel x) s with
      | ASTFragment (Inr l, _) -> l
      | _ -> failwith "parse failed"

    let decl_of_string s =
      match decls_of_string s with [ d ] -> d | _ -> failwith "decl_of_string"
  end

  let doc_to_string : PPrint.document -> string =
    FStar_Pprint.pretty_string 1.0 (Z.of_int 100)

  let term_to_string : F.AST.term -> string =
    FStar_Parser_ToDocument.term_to_document >> doc_to_string

  let decl_to_string : F.AST.decl -> string =
    FStar_Parser_ToDocument.decl_to_document >> doc_to_string

  (* let _ = failwith @@ term_to_string @@ F.term_of_string "a + 3" *)

  module Context = struct
    type t = { current_namespace : string * string list }
  end

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
      | Int { value; kind = { size; signedness } } ->
          F.Const.Const_int
            ( Bigint.to_string value,
              let open F.Const in
              Option.map
                (match size with
                | S8 -> Some Int8
                | S16 -> Some Int16
                | S32 -> Some Int32
                | S64 -> Some Int64
                | S128 -> failwith "Cannot handle S128"
                | SSize -> None)
                ~f:(fun w ->
                  ( (match signedness with
                    | Signed -> Signed
                    | Unsigned -> Unsigned),
                    w )) )
      | Float _ -> failwith "Float: todo"
      | Bool b -> F.Const.Const_bool b

    let pliteral_as_expr (e : literal) =
      let h e = F.term @@ F.AST.Const (pliteral e) in
      match e with
      | Int { value; kind = { size = S128; signedness } as s } ->
          let lit = h (Int { value; kind = { s with size = SSize } }) in
          let prefix =
            match signedness with Signed -> "i" | Unsigned -> "u"
          in
          F.mk_e_app (F.term_of_lid [ "pub_" ^ prefix ^ "128" ]) [ lit ]
      | _ -> h e

    (* let is_concrete_ident_in_namespace (crate, path) (id : concrete_ident) = *)
    (*   crate = id.crate && List.is_prefix ~prefix:path @@ Non_empty_list. id.path *)

    let pconcrete_ident (id : concrete_ident) =
      let id_path = Non_empty_list.to_list id.path in
      let crate, path = ctx.current_namespace in
      if
        String.(crate = id.crate)
        && [%eq: string list] (List.drop_last_exn id_path) path
      then F.lid [ List.last_exn id_path ]
      else F.lid (id.crate :: id_path)

    let rec pglobal_ident (id : global_ident) =
      match id with
      | `Concrete cid -> pconcrete_ident cid
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

    let ptype_ident : global_ident -> F.Ident.lident =
      lowercase_global_ident
      >> map_last_global_ident (fun s -> s ^ "_t")
      >> pglobal_ident

    let pconstructor_ident : global_ident -> F.Ident.lident =
      uppercase_global_ident >> pglobal_ident

    let rec pty (t : ty) =
      match t with
      | TBool -> F.term_of_lid [ "Prims"; "bool" ]
      | TChar -> F.term_of_lid [ "FStar"; "Char"; "char" ]
      | TInt k ->
          let prefix = function Signed -> "Int" | Unsigned -> "UInt" in
          let path x s = [ prefix x ^ s; "t" ] in
          F.term_of_lid
            (match k with
            | { size = SSize; signedness = Signed } -> [ "int_size" ]
            | { size = SSize; signedness = Unsigned } -> [ "uint_size" ]
            (* | { size = SSize; signedness = Signed } -> [ "Prims"; "int" ] *)
            (* | { size = SSize; signedness = Unsigned } -> [ "Prims"; "nat" ] *)
            | { size = S8; signedness } -> path signedness "8"
            | { size = S16; signedness } -> path signedness "16"
            | { size = S32; signedness } -> path signedness "32"
            | { size = S64; signedness } -> path signedness "64"
            | { size = S128; signedness } -> path signedness "128")
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
          let mk_star a b = F.term @@ F.AST.Op (F.id "&", [ a; b ]) in
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
              let length =
                pliteral_as_expr
                  (Ast.Int
                     {
                       value = Bigint.of_int length;
                       kind = { size = SSize; signedness = Signed };
                     })
              in
              let lt = F.term @@ F.AST.Name (pprim_ident @@ BinOp Lt) in
              F.mk_e_app lt [ len_of_x; length ])
      | TParam i ->
          F.term
          @@ F.AST.Var
               (F.lid_of_id
               @@ plocal_ident { i with name = pgeneric_param_name i.name })
      | TProjectedAssociatedType s ->
          print_endline @@ s;
          (* failwith "xx"; *)
          (* F.term @@ F.AST.Const (F.Const.Const_string (show_ty t, F.dummyRange)) *)
          F.term
          @@ F.AST.Const
               (F.Const.Const_string ("TODO:ProjectedType", F.dummyRange))
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
      | _ -> .

    and pfield_pat ({ field; pat } : field_pat) = (pglobal_ident field, ppat pat)

    let debug_expr (label : string) (e : F.AST.term) =
      F.term @@ F.AST.App (F.term_of_lid [ "__debug__" ^ label ], e, Nothing)

    let operators =
      let c = GlobalIdent.of_string_exn in
      [
        (c "std::core::array::update_array_at", (3, ".[]<-"));
        (c "core::ops::index::Index::index", (2, ".[]"));
        (c "core::ops::bit::BitXor::bitxor", (2, "^."));
        (c "core::ops::bit::BitAnd::bitand", (2, "&."));
        (c "core::ops::bit::BitOr::bitor", (2, "|."));
        (c "core::ops::arith::Add::add", (2, "+."));
        (c "core::ops::arith::Mul::mul", (2, "*."));
        (`Primitive (BinOp Add), (2, "+"));
        (`Primitive (BinOp Sub), (2, "-"));
        (`Primitive (BinOp Mul), (2, "*"));
        (`Primitive (BinOp Eq), (2, "="));
        (`Primitive (BinOp Ne), (2, "<>"))
        (* | BinOp  -> ( *)
        (*    match op with *)
        (*    | Add -> F.lid [ "Prims"; "op_Addition" ] *)
        (*    | Sub -> F.lid [ "Prims"; "op_Subtraction" ] *)
        (*    | Mul -> F.lid [ "FStar"; "Mul"; "op_Star" ] *)
        (*    | Div -> F.lid [ "Prims"; "op_Division" ] *)
        (*    | Eq -> F.lid [ "Prims"; "op_Equality" ] *)
        (*    | Lt -> F.lid [ "Prims"; "op_LessThan" ] *)
        (*    | Le -> F.lid [ "Prims"; "op_LessThanOrEqual" ] *)
        (*    | Ge -> F.lid [ "Prims"; "op_GreaterThan" ] *)
        (*    | Gt -> F.lid [ "Prims"; "op_GreaterThanOrEqual" ] *)
        (*    | Ne -> F.lid [ "Prims"; "op_disEquality" ] *)
        (*    | Rem -> failwith "TODO: Rem" *)
        (*    | BitXor -> failwith "TODO: BitXor" *)
        (*    | BitAnd -> failwith "TODO: BitAnd" *)
        (*    | BitOr -> failwith "TODO: BitOr" *)
        (*    | Shl -> failwith "TODO: Shl" *)
        (*    | Shr -> failwith "TODO: Shr" *)
        (*    | Offset -> failwith "TODO: Offset") *);
      ]
      |> Map.of_alist_exn (module GlobalIdent)

    let rec pexpr (e : expr) =
      match e.e with
      | Literal e -> pliteral_as_expr e
      | LocalVar local_ident ->
          F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident local_ident)
      | GlobalVar (`TupleCons 0)
      | Construct { constructor = `TupleCons 0; fields = [] } ->
          F.AST.unit_const F.dummyRange
      | GlobalVar global_ident ->
          F.term
          @@ F.AST.Var (pglobal_ident @@ lowercase_global_ident global_ident)
      | App
          {
            f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
            args = [ arg ];
          } ->
          F.term
          @@ F.AST.Project (pexpr arg, F.lid [ "_" ^ string_of_int (n + 1) ])
      | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
          let arity, op = Map.find_exn operators x in
          if List.length args <> arity then failwith "Bad arity";
          F.term @@ F.AST.Op (F.Ident.id_of_text op, List.map ~f:pexpr args)
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
          let p =
            (* TODO: temp patch that remove annotation when we see an associated type *)
            if [%matches? TProjectedAssociatedType _] @@ U.remove_tuple1 lhs.typ
            then ppat lhs
            else F.pat @@ F.AST.PatAscribed (ppat lhs, (pty lhs.typ, None))
          in
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
                 List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields
               )
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
                     (* F.pat @@ F.AST.PatAscribed (ppat p, (pty p.typ, None))) *)
                     ppat p)
                   params,
                 pexpr body )
      | Return { e } ->
          F.term @@ F.AST.App (F.term_of_lid [ "RETURN_STMT" ], pexpr e, Nothing)
      | MacroInvokation _ -> failwith "expr:MacroInvokation"
      | _ -> .

    and parm { arm = { pat; body } } = (ppat pat, None, pexpr body)

    (* let item_to_string: F.AST.item -> string = *)
    (*   FStar_Parser_ToDocument.decl_to_document >> doc_to_string *)

    (* todo eliminate me *)
    let last_of_global_ident (g : global_ident) =
      match g with
      | `Concrete { path; crate = _ } -> Non_empty_list.last path
      | _ -> failwith "last_of_global_ident"

    let str_of_type_ident : global_ident -> string =
      lowercase_global_ident
      >> map_last_global_ident (fun s -> s ^ "_t")
      >> last_of_global_ident

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
               ( F.pat_var_tcresolve @@ Some ("__" ^ string_of_int nth),
                 (tc, None) )

    let hacspec_lib_item s =
      `Concrete { crate = "hacspec"; path = Non_empty_list.[ "lib"; s ] }

    let rec pitem (e : item) =
      match e.v with
      | Fn { name; generics; body; params } ->
          (* let last_of_global_ident (g : global_ident) = *)
          (*   match g with *)
          (*   | `Concrete { path; crate } -> *)
          (*       String.concat ~sep:"_" @@ (crate :: Non_empty_list.to_list path) *)
          (*   | _ -> failwith "last_of_global_ident" *)
          (* in *)
          let pat =
            F.pat
            @@ F.AST.PatVar
                 ( F.id @@ last_of_global_ident @@ lowercase_global_ident name,
                   None,
                   [] )
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
          F.decls @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, pexpr body) ])
      | TyAlias { name; generics; ty } ->
          let pat =
            F.pat
            @@ F.AST.PatVar
                 ( F.id @@ last_of_global_ident @@ lowercase_global_ident name,
                   None,
                   [] )
          in
          F.decls ~quals:[ F.AST.Unfold_for_unification_and_vcgen ]
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
          F.decls
          @@ F.AST.Tycon
               ( false,
                 false,
                 [
                   F.AST.TyconRecord
                     ( F.id @@ str_of_type_ident name,
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
            F.term_of_lid
              [ last_of_global_ident @@ lowercase_global_ident name ]
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
          F.decls
          @@ F.AST.Tycon
               ( false,
                 false,
                 [
                   F.AST.TyconVariant
                     ( F.id @@ last_of_global_ident
                       @@ lowercase_global_ident name,
                       [],
                       (* todo type parameters & constraints *)
                       None,
                       constructors );
                 ] )
      | IMacroInvokation
          {
            macro =
              `Concrete
                Non_empty_list.
                  { crate = "hacspec_lib_tc"; path = [ "public_nat_mod" ] };
            argument;
            span;
          } ->
          let open Hacspeclib_macro_parser in
          (* failwith argument; *)
          let o : PublicNatMod.t =
            PublicNatMod.parse argument |> Result.ok_or_failwith
          in
          (F.decls_of_string @@ "unfold type "
          ^ str_of_type_ident (hacspec_lib_item @@ o.type_name)
          ^ "  = nat_mod 0x" ^ o.modulo_value)
          @ F.decls_of_string @@ "unfold type "
          ^ str_of_type_ident (hacspec_lib_item @@ o.type_of_canvas)
          ^ "  = lseq pub_uint8 "
          ^ string_of_int o.bit_size_of_field
          (* type field_canvas_t = lseq (pub_uint8) (17) *)
          (* type field_element_t = nat_mod 0x03fffffffffffffffffffffffffffffffb *)
      | IMacroInvokation
          {
            macro =
              `Concrete
                Non_empty_list.{ crate = "hacspec_lib_tc"; path = [ "bytes" ] };
            argument;
            span;
          } ->
          let open Hacspeclib_macro_parser in
          let o : Bytes.t = Bytes.parse argument |> Result.ok_or_failwith in
          F.decls_of_string @@ "unfold type "
          ^ str_of_type_ident (hacspec_lib_item @@ o.bytes_name)
          ^ "  = lseq uint8 " ^ o.size
      | IMacroInvokation
          {
            macro =
              `Concrete
                Non_empty_list.{ crate = "hacspec_lib_tc"; path = [ "array" ] };
            argument;
            span;
          } ->
          let open Hacspeclib_macro_parser in
          let o : Array.t = Array.parse argument |> Result.ok_or_failwith in
          let typ =
            match o.typ with
            | "U32" -> "uint32"
            | "U16" -> "uint16"
            | "U8" -> "uint8"
            | usize -> usize
          in
          let size = o.size in
          let array_def =
            F.decls_of_string @@ "unfold type "
            ^ str_of_type_ident (hacspec_lib_item o.array_name)
            ^ "  = lseq " ^ typ ^ " " ^ size
          in
          let index_def =
            match o.index_typ with
            | Some index ->
                F.decls_of_string @@ "unfold type "
                ^ str_of_type_ident (hacspec_lib_item @@ o.array_name ^ "_idx")
                ^ " = nat_mod " ^ size
            | None -> []
          in
          array_def @ index_def
      | IMacroInvokation
          { macro = `Concrete Non_empty_list.{ crate; path = _ } as x } ->
          F.decls_of_string @@ "let _ = \"could not handle macro "
          ^ [%show: global_ident] x
          ^ "\""
      | IMacroInvokation _ -> failwith "x"
      | _ -> []
  end

  module type S = sig
    val pitem : item -> F.AST.decl list
  end

  let make ctx =
    (module Make (struct
      let ctx = ctx
    end) : S)

  let string_of_item (item : item) : string =
    let (module Print) = make { current_namespace = item.parent_namespace } in
    List.map ~f:decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

  let string_of_items =
    List.map ~f:string_of_item >> List.map ~f:String.strip
    >> List.filter ~f:(String.is_empty >> not)
    >> String.concat ~sep:"\n\n"

  let hardcoded_fstar_headers =
    "\n\
     #set-options \"--fuel 0 --ifuel 1 --z3rlimit 15\"\n\
     open FStar.Mul\n\
     open Hacspec.Lib\n\
     open Hacspec_lib_tc"

  (* module AST : Ast.T *)

  let modules_to_string (o : Backend.Options.t) modules =
    let out_dir = "out/" in
    (try Caml.Sys.mkdir out_dir 0o777 with Sys_error _ -> ());
    List.iter
      ~f:(fun (relative_path, data) ->
        if not (String.equal relative_path "Hacspec_lib.fst") then (
          let file = out_dir ^ relative_path in
          Core.Out_channel.write_all file ~data;
          print_endline @@ "Wrote " ^ file))
      modules

  let translate (o : Backend.Options.t) (bo : BackendOptions.t)
      (items : AST.item list) : unit =
    U.group_items_by_namespace items
    |> Map.to_alist
    |> List.map ~f:(fun (ns, items) ->
           let mod_name =
             String.concat ~sep:"."
               (List.map
                  ~f:(map_first_letter String.uppercase)
                  (fst ns :: snd ns))
           in
           ( mod_name ^ ".fst",
             "module " ^ mod_name ^ hardcoded_fstar_headers ^ "\n\n"
             ^ string_of_items items ))
    |> modules_to_string o

  open Desugar_utils

  module DesugarToInputLanguage =
    [%functor_application
       Reject.RawOrMutPointer(Features.Rust)
    |> Reject.Arbitrary_lhs
    |> Resugar_for_loop.Make
    |> Desugar_direct_and_mut.Make
    |> Reject.Continue
    |> Desugar_drop_references.Make
    |> (fun X ->
        (Desugar_mutable_variable.Make(module X))
          (module struct
            let early_exit = fun _ -> Features.On.early_exit
          end))
    |> RejectNotFStar
    |> Identity
    ]
    [@ocamlformat "disable"]

  let desugar (o : Backend.Options.t) (bo : BackendOptions.t)
      (i : Ast.Rust.item) : AST.item list =
    DesugarToInputLanguage.ditem i
end

let register = Backend.Registration.register (module FStarBackend)
