open Hax_engine
open Utils
open Base
open Coq_ast

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Slice
      include On.Monadic_binding
      include On.Macro
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.Coq
    end)

module SubtypeToInputLanguage
    (FA : Features.T
            with type mutable_reference = Features.Off.mutable_reference
             and type continue = Features.Off.continue
             and type mutable_pointer = Features.Off.mutable_pointer
             and type mutable_variable = Features.Off.mutable_variable
             and type reference = Features.Off.reference
             and type raw_pointer = Features.Off.raw_pointer
             and type early_exit = Features.Off.early_exit
             and type question_mark = Features.Off.question_mark
             and type as_pattern = Features.Off.as_pattern
             and type lifetime = Features.Off.lifetime
             and type monadic_action = Features.Off.monadic_action
             and type arbitrary_lhs = Features.Off.arbitrary_lhs
             and type nontrivial_lhs = Features.Off.nontrivial_lhs
             and type loop = Features.Off.loop
             and type for_loop = Features.Off.for_loop
             and type for_index_loop = Features.Off.for_index_loop
             and type state_passing_loop = Features.Off.state_passing_loop) =
struct
  module FB = InputLanguage

  include
    Subtype.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Features.SUBTYPE.Id
        include Features.SUBTYPE.On.Monadic_binding
        include Features.SUBTYPE.On.Construct_base
        include Features.SUBTYPE.On.Slice
        include Features.SUBTYPE.On.Macro
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module U = Ast_utils.Make (InputLanguage)
open AST

module CoqLibrary : Library = struct
  module Notation = struct
    let int_repr (x : string) (i : string) : string =
      "(@repr" ^ " " ^ "WORDSIZE" ^ x ^ " " ^ i ^ ")"

    let let_stmt (var : string) (expr : string) (typ : string) (body : string)
        (depth : int) : string =
      "let" ^ " " ^ var ^ " " ^ ":=" ^ " (" ^ expr ^ ") " ^ ":" ^ " " ^ typ
      ^ " " ^ "in" ^ newline_indent depth ^ body

    let let_mut_stmt = let_stmt
    let tuple_prefix : string = ""
  end
end

module C = Coq (CoqLibrary)

module Context = struct
  type t = { current_namespace : string * string list }
end

let primitive_to_string (id : primitive_ident) : string =
  match id with
  | Box -> "(TODO: BOX)" (* failwith "Box" *)
  | Deref -> "(TODO: Deref)" (* failwith "Deref" *)
  | Cast -> "cast" (* failwith "Cast" *)
  | BinOp op -> (
      match op with
      | Add -> "MachineIntegers.add"
      | Sub -> "MachineIntegers.sub"
      | Mul -> "MachineIntegers.mul"
      | Div -> "MachineIntegers.divs"
      | Eq -> "eq_op"
      | Lt -> "lt_op"
      | Le -> "le_op"
      | Ge -> "ge_op"
      | Gt -> "gt_op"
      | Ne -> "ne_op"
      | Rem -> "MachineIntegers.mods" (* .% *)
      | BitXor -> "MachineIntegers.xor" (* .^ *)
      | BitAnd -> "MachineIntegers.and" (* .& *)
      | BitOr -> "MachineIntegers.or" (* .| *)
      | Shl -> "shift_left_" (* shift_left *)
      | Shr -> "shift_right_" (* shift_right *)
      | Offset -> "(TODO: Offset)" (* failwith "TODO: Offset" *))
  | UnOp op -> "(TODO: UnOp)"
  | LogicalOp op -> ( match op with And -> "andb" | Or -> "orb")

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pconcrete_ident (id : concrete_ident) : string =
    let id_path = Non_empty_list.to_list id.path in
    let crate, path = ctx.current_namespace in
    if
      String.(crate = id.crate)
      && [%eq: string list] (List.drop_last_exn id_path) path
    then List.last_exn id_path
    else
      (* id.crate ^ "_" ^ *)
      (* List.fold_left ~init:"" ~f:(fun x y -> x ^ "_" ^ y) *)
      List.last_exn id_path

  let pglobal_ident (id : global_ident) : string =
    match id with
    | `Projector (`Concrete cid) | `Concrete cid -> pconcrete_ident cid
    | `Primitive p_id -> primitive_to_string p_id
    | `TupleType i -> "TODO (global ident) tuple type"
    | `TupleCons i -> "TODO (global ident) tuple cons"
    | `Projector (`TupleField (i, j)) | `TupleField (i, j) ->
        "TODO (global ident) tuple field"
    | _ -> .

  let pglobal_ident_last (id : global_ident) : string =
    match id with
    | `Concrete { crate; path } -> Non_empty_list.last path
    | `Primitive p_id -> "TODO (global ident last) primitive"
    | `TupleType i -> "TODO (global ident last) tuple type"
    | `TupleCons i -> "TODO (global ident last) tuple cons"
    | `TupleField i -> "TODO (global ident last) tuple field"
    | `Projector (`Concrete cid) -> "TODO (global ident last) projector cid"
    | `Projector (`TupleField (i, j)) ->
        "TODO (global ident last) projector tuplefield"
    | _ -> .

  module TODOs_debug = struct
    let __TODO_pat__ _ s = C.AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ _ s : C.AST.ty = C.AST.Name (s ^ " todo(ty)")
    let __TODO_item__ _ s = C.AST.Unimplemented (s ^ " todo(item)")
    let __TODO_term__ _ s = C.AST.Const (C.AST.Const_string (s ^ " todo(term)"))
  end

  module TODOs = struct
    let __TODO_ty__ span s : C.AST.ty =
      Error.unimplemented ~details:("[ty] node " ^ s) span

    let __TODO_pat__ span s =
      Error.unimplemented ~details:("[pat] node " ^ s) span

    let __TODO_term__ span s =
      Error.unimplemented ~details:("[expr] node " ^ s) span

    let __TODO_item__ span s = C.AST.Unimplemented (s ^ " todo(item)")
  end

  open TODOs

  let pint_kind (k : int_kind) : C.AST.int_type =
    {
      size =
        (match k.size with
        | S8 -> U8
        | S16 -> U16
        | S32 -> U32
        | S64 -> U64
        | S128 -> U128
        | SSize -> USize);
      signed = k.signedness == Signed;
    }

  let rec pliteral span (e : literal) =
    match e with
    | String s -> C.AST.Const_string s
    | Char c -> C.AST.Const_char (Char.to_int c)
    | Int { value; kind } -> C.AST.Const_int (value, pint_kind kind)
    | Float _ -> Error.unimplemented ~details:"pliteral: Float" span
    | Bool b -> C.AST.Const_bool b

  let rec pty span (t : ty) : C.AST.ty =
    match t with
    | TBool -> C.AST.Bool
    | TChar -> __TODO_ty__ span "char"
    | TInt k -> C.AST.Int (pint_kind k)
    | TStr -> __TODO_ty__ span "str"
    | TFalse -> __TODO_ty__ span "false"
    | TApp { ident = `TupleType 0 as ident; args = [] } -> C.AST.Unit
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty span ty
    | TApp { ident = `TupleType n; args } when n >= 2 ->
        C.AST.Product (args_ty span args)
    | TApp { ident; args } ->
        C.AST.AppTy (pglobal_ident ident ^ "_t", args_ty span args)
    | TArrow (inputs, output) ->
        List.fold_right ~init:(pty span output)
          ~f:(fun x y -> C.AST.Arrow (x, y))
          (List.map ~f:(pty span) inputs)
    | TFloat -> __TODO_ty__ span "pty: Float"
    | TArray { typ; length } ->
        C.AST.ArrayTy (pty span typ, "TODO: Int.to_string length")
    | TSlice { ty; _ } -> C.AST.SliceTy (pty span ty)
    | TParam i -> C.AST.Name i.name
    | TProjectedAssociatedType s ->
        C.AST.Wild
        (* __TODO_ty__ span ("proj:assoc:type" ^ s) *)
        (* failwith "proj:assoc:type" *)
    | _ -> .

  and args_ty span (args : generic_value list) : C.AST.ty list =
    (* List.map ~f:pty *)
    match args with
    | arg :: xs ->
        (match arg with
        | GLifetime { lt; witness } -> __TODO_ty__ span "lifetime"
        | GType x -> pty span x
        | GConst _ -> __TODO_ty__ span "const")
        :: args_ty span xs
    | [] -> []

  let rec ppat (p : pat) : C.AST.pat =
    match p.p with
    | PWild -> C.AST.Wild
    | PAscription { typ; pat } -> C.AST.AscriptionPat (ppat pat, pty p.span typ)
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat = None;
          var;
          typ = _ (* we skip type annot here *);
        } ->
        C.AST.Ident var.name
    | PArray { args } -> __TODO_pat__ p.span "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> C.AST.UnitPat
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        __TODO_pat__ p.span "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        C.AST.TuplePat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; record } ->
        C.AST.RecordPat (pglobal_ident_last name, pfield_pats args)
    | PConstant { lit } -> C.AST.Lit (pliteral p.span lit)
    | PDeref { subpat } -> __TODO_pat__ p.span "deref"
    | _ -> .

  and pfield_pats (args : field_pat list) : (string * C.AST.pat) list =
    match args with
    | { field; pat } :: xs ->
        (pglobal_ident_last field, ppat pat) :: pfield_pats xs
    | _ -> []

  let operators =
    let c = GlobalIdent.of_string_exn in
    [
      (c "std::core::array::update_array_at", (3, [ ""; ".["; "]<-"; "" ]));
      (c "core::ops::index::Index::index", (2, [ ""; ".["; "]" ]));
      (c "core::ops::bit::BitXor::bitxor", (2, [ ""; ".^"; "" ]));
      (c "core::ops::bit::BitAnd::bitand", (2, [ ""; ".&"; "" ]));
      (c "core::ops::bit::BitOr::bitor", (2, [ ""; ".|"; "" ]));
      (c "core::ops::arith::Add::add", (2, [ ""; ".+"; "" ]));
      (c "core::ops::arith::Sub::sub", (2, [ ""; ".-"; "" ]));
      (c "core::ops::arith::Mul::mul", (2, [ ""; ".*"; "" ]));
      (`Primitive (BinOp Add), (2, [ ""; ".+"; "" ]));
      (`Primitive (BinOp Sub), (2, [ ""; ".-"; "" ]));
      (`Primitive (BinOp Mul), (2, [ ""; ".*"; "" ]));
      (`Primitive (BinOp Div), (2, [ ""; "./"; "" ]));
      (`Primitive (BinOp Eq), (2, [ ""; "=.?"; "" ]));
      (`Primitive (BinOp Lt), (2, [ ""; "<.?"; "" ]));
      (`Primitive (BinOp Le), (2, [ ""; "<=.?"; "" ]));
      (`Primitive (BinOp Ge), (2, [ ""; ">=.?"; "" ]));
      (`Primitive (BinOp Gt), (2, [ ""; ">.?"; "" ]));
      (`Primitive (BinOp Ne), (2, [ ""; "<>"; "" ]));
      (`Primitive (BinOp Rem), (2, [ ""; ".%"; "" ]));
      (`Primitive (BinOp BitXor), (2, [ ""; ".^"; "" ]));
      (`Primitive (BinOp BitAnd), (2, [ ""; ".&"; "" ]));
      (`Primitive (BinOp BitOr), (2, [ ""; ".|"; "" ]));
      (`Primitive (BinOp Shl), (2, [ ""; " shift_left "; "" ]));
      (`Primitive (BinOp Shr), (2, [ ""; " shift_right "; "" ]));
      (c "secret_integers::rotate_left", (2, [ "rol "; " "; "" ]));
      (c "hacspec::lib::foldi", (4, [ "foldi "; " "; " "; " "; "" ]));
      (* (c "secret_integers::u8", (0, ["U8"])); *)
      (* (c "secret_integers::u16", (0, ["U16"])); *)
      (* (c "secret_integers::u32", (0, ["U32"])); *)
      (* (c "secret_integers::u64", (0, ["U64"])); *)
      (* (c "secret_integers::u128", (0, ["U128"])); *)
    ]
    |> Map.of_alist_exn (module GlobalIdent)

  let index_of_field = function
    | `Concrete { path } -> (
        try Some (Int.of_string @@ Non_empty_list.last path) with _ -> None)
    | `TupleField (nth, _) -> Some nth
    | _ -> None

  (* let is_field_an_index = index_of_field >> Option.is_some *)

  let rec pexpr (e : expr) =
    try pexpr_unwrapped e
    with Diagnostics.SpanFreeError kind ->
      TODOs_debug.__TODO_term__ e.span "failure"

  and pexpr_unwrapped (e : expr) : C.AST.term =
    let span = e.span in
    match e.e with
    | Literal l -> C.AST.Const (pliteral e.span l)
    | LocalVar local_ident -> C.AST.Name local_ident.name
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        C.AST.UnitTerm
    | GlobalVar global_ident -> C.AST.Var (pglobal_ident global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        __TODO_term__ span "app global vcar projector tuple"
    | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
        let arity, op = Map.find_exn operators x in
        if List.length args <> arity then
          Error.assertion_failure span "expr: function application: bad arity";
        let args = List.map ~f:pexpr args in
        C.AST.AppFormat (op, args)
    (* | App { f = { e = GlobalVar x }; args } -> *)
    (*    __TODO_term__ span "GLOBAL APP?" *)
    | App { f; args } ->
        let base = pexpr f in
        let args = List.map ~f:pexpr args in
        C.AST.App (base, args)
    | If { cond; then_; else_ } ->
        C.AST.If
          ( pexpr cond,
            pexpr then_,
            Option.value_map else_ ~default:(C.AST.Literal "()") ~f:pexpr )
    | Array l -> C.AST.Array (List.map ~f:pexpr l)
    | Let { lhs; rhs; body; monadic } ->
        C.AST.Let
          {
            pattern = ppat lhs;
            mut =
              (match lhs.p with
              | PBinding { mut = Mutable _ } -> true
              | _ -> false);
            value = pexpr rhs;
            body = pexpr body;
            value_typ = pty span lhs.typ;
          }
    | EffectAction _ -> __TODO_term__ span "monadic action"
    | Match { scrutinee; arms } ->
        C.AST.Match
          ( pexpr scrutinee,
            List.map
              ~f:(fun { arm = { arm_pat; body } } -> (ppat arm_pat, pexpr body))
              arms )
    | Ascription { e; typ } -> __TODO_term__ span "asciption"
    | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
        pexpr e
    | Construct { constructor = `TupleCons n; fields; base } ->
        C.AST.Tuple (List.map ~f:(snd >> pexpr) fields)
    | Construct { constructs_record = true; constructor; fields; base } ->
        C.AST.RecordConstructor
          ( C.AST.Var (pglobal_ident constructor ^ "_t"),
            List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields )
    | Construct { constructor; fields = [ (f, e) ]; base } ->
        C.AST.App (C.AST.Var (pglobal_ident constructor), [ pexpr e ])
    | Construct { constructor; fields; base } ->
        C.AST.Var
          (pglobal_ident constructor ^ snd (C.ty_to_string (pty span e.typ)))
    | Closure { params; body } ->
        C.AST.Lambda (List.map ~f:ppat params, pexpr body)
    | MacroInvokation { macro; args; witness } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | _ -> .

  let rec pitem (e : item) : C.AST.decl list =
    try pitem_unwrapped e
    with Diagnostics.SpanFreeError _kind ->
      [ C.AST.Unimplemented "item error backend" ]

  and pitem_unwrapped (e : item) : C.AST.decl list =
    let span = e.span in
    match e.v with
    | Fn { name; generics; body; params } ->
        [
          C.AST.Definition
            ( pglobal_ident name,
              List.map
                ~f:(fun { pat; typ; typ_span } -> (ppat pat, pty span typ))
                params,
              pexpr body,
              pty span body.typ );
        ]
    | TyAlias { name; generics; ty } ->
        [ C.AST.Notation (pglobal_ident name ^ "_t", pty span ty) ]
    (* record *)
    | Type
        {
          name;
          generics;
          variants = [ { name = record_name; arguments } ];
          record = true;
        }
      when GlobalIdent.equal name record_name ->
        [
          C.AST.Record
            ( pglobal_ident_last name ^ "_t" ^ pglobal_ident record_name,
              p_record_record span arguments );
        ]
    (* enum *)
    | Type { name; generics; variants; record = true } ->
        [
          C.AST.Inductive
            ( pglobal_ident_last name ^ "_t",
              List.fold_left ~init:[]
                ~f:(fun a b ->
                  a
                  @ [
                      (match b with
                      | GPType { ident; default } -> ident.name
                      | _ ->
                          Error.unimplemented
                            ~details:"Coq: TODO: generic_params" span);
                    ])
                generics.params,
              p_inductive span variants name );
        ]
    | Type { name; generics; variants } ->
        [
          C.AST.Notation
            ( pglobal_ident_last name ^ "_t",
              C.AST.Product (List.map ~f:snd (p_record span variants name)) );
          C.AST.Definition
            ( pglobal_ident_last name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (pglobal_ident_last name ^ "_t"),
                  C.AST.Name (pglobal_ident_last name ^ "_t") ) );
        ]
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
        let o : PublicNatMod.t =
          PublicNatMod.parse argument |> Result.ok_or_failwith
        in
        [
          C.AST.Notation
            ( o.type_name ^ "_t",
              C.AST.NatMod
                (o.type_of_canvas, o.bit_size_of_field, o.modulo_value) );
          C.AST.Definition
            ( o.type_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.type_name ^ "_t"),
                  C.AST.Name (o.type_name ^ "_t") ) );
        ]
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
        [
          C.AST.Notation
            ( o.bytes_name ^ "_t",
              C.AST.ArrayTy
                ( C.AST.Int { size = C.AST.U8; signed = false },
                  (* int_of_string *) o.size ) );
          C.AST.Definition
            ( o.bytes_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.bytes_name ^ "_t"),
                  C.AST.Name (o.bytes_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.
                {
                  crate = "hacspec_lib_tc";
                  path = [ "unsigned_public_integer" ];
                };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o = UnsignedPublicInteger.parse argument |> Result.ok_or_failwith in
        [
          C.AST.Notation
            ( o.integer_name ^ "_t",
              C.AST.ArrayTy
                ( C.AST.Int { size = C.AST.U8; signed = false },
                  Int.to_string ((o.bits + 7) / 8) ) );
          C.AST.Definition
            ( o.integer_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.integer_name ^ "_t"),
                  C.AST.Name (o.integer_name ^ "_t") ) );
        ]
    | IMacroInvokation
        {
          macro =
            `Concrete
              Non_empty_list.
                { crate = "hacspec_lib_tc"; path = [ "public_bytes" ] };
          argument;
          span;
        } ->
        let open Hacspeclib_macro_parser in
        let o : Bytes.t = Bytes.parse argument |> Result.ok_or_failwith in
        let typ =
          C.AST.ArrayTy
            ( C.AST.Int { size = C.AST.U8; signed = false },
              (* int_of_string *) o.size )
        in
        [
          C.AST.Notation (o.bytes_name ^ "_t", typ);
          C.AST.Definition
            ( o.bytes_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.bytes_name ^ "_t"),
                  C.AST.Name (o.bytes_name ^ "_t") ) );
        ]
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
          (* Some *)
          | "U128" -> C.AST.U128
          (* Some *)
          | "U64" -> C.AST.U64
          (* Some *)
          | "U32" -> C.AST.U32
          (* Some *)
          | "U16" -> C.AST.U16
          (* Some *)
          | "U8" -> C.AST.U8
          | usize -> C.AST.U32 (* TODO: usize? *)
        in
        [
          C.AST.Notation
            ( o.array_name ^ "_t",
              C.AST.ArrayTy
                ( C.AST.Int { size = typ; signed = false },
                  (* int_of_string *) o.size ) );
          C.AST.Definition
            ( o.array_name,
              [],
              C.AST.Var "id",
              C.AST.Arrow
                ( C.AST.Name (o.array_name ^ "_t"),
                  C.AST.Name (o.array_name ^ "_t") ) );
        ]
    | IMacroInvokation { macro; _ } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | Use { path; is_external; rename } ->
        if is_external then [] else [ C.AST.Require (path, rename) ]
    | HaxError s -> [ __TODO_item__ span s ]
    | NotImplementedYet -> [ __TODO_item__ span "Not implemented yet?" ]
    | Trait { name; generics; items } ->
        [
          C.AST.Class
            ( pglobal_ident name,
              List.map
                ~f:(fun x ->
                  ( x.ti_name,
                    match x.ti_v with
                    | TIFn fn_ty -> pty span fn_ty
                    | _ -> __TODO_ty__ span "field_ty" ))
                items,
              List.fold_left ~init:[]
                ~f:(fun a b ->
                  a
                  @ [
                      (match b with
                      | GPType { ident; default } -> ident.name
                      | _ ->
                          Error.unimplemented
                            ~details:"Coq: TODO: generic_params" span);
                    ])
                generics.params );
        ]
    | Impl { generics; self_ty; of_trait = Some (name, gen_vals); items } ->
        [
          C.AST.Instance
            ( pglobal_ident name,
              pty span self_ty,
              args_ty span gen_vals,
              List.map
                ~f:(fun x ->
                  match x.ii_v with
                  | IIFn { body; params } ->
                      ( x.ii_name,
                        List.map
                          ~f:(fun { pat; typ; typ_span } ->
                            (ppat pat, pty span typ))
                          params,
                        pexpr body,
                        pty span body.typ )
                  | _ ->
                      ( "todo_name",
                        [],
                        __TODO_term__ span "body",
                        __TODO_ty__ span "typ" ))
                items );
        ]
    | Impl _ -> [ __TODO_item__ span "trait self" ]

  (* self_ty : ty; *)
  (* of_trait : (global_ident * generic_value list) option; *)
  (* items : impl_item list; *)

  and p_inductive span variants parrent_name : C.AST.inductive_case list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        if (index_of_field >> Option.is_some) arg_name then
          C.AST.InductiveCase (pglobal_ident_last name, pty span arg_ty)
          :: p_inductive span xs parrent_name
        else
          C.AST.InductiveCase (pglobal_ident_last arg_name, pty span arg_ty)
          :: p_inductive span xs parrent_name
    | { name; arguments = [] } :: xs ->
        C.AST.BaseCase (pglobal_ident_last name)
        :: p_inductive span xs parrent_name
    | { name; arguments } :: xs ->
        C.AST.InductiveCase
          ( pglobal_ident_last name,
            C.AST.RecordTy (pglobal_ident name, p_record_record span arguments)
          )
        :: p_inductive span xs parrent_name
    | _ -> []

  and p_record span variants parrent_name : (string * C.AST.ty) list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        (pglobal_ident_last arg_name, pty span arg_ty)
        :: p_record span xs parrent_name
    | { name; arguments = [] } :: xs ->
        ("TODO FIELD?", __TODO_ty__ span "TODO")
        :: p_record span xs parrent_name
    | { name; arguments } :: xs ->
        ( pglobal_ident_last name,
          C.AST.RecordTy (pglobal_ident name, p_record_record span arguments) )
        :: p_record span xs parrent_name
    | _ -> []

  and p_record_record span arguments : (string * C.AST.ty) list =
    List.map
      ~f:(function
        | arg_name, arg_ty -> (pglobal_ident_last arg_name, pty span arg_ty))
      arguments
end

module type S = sig
  val pitem : item -> C.AST.decl list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item (item : item) : string =
  let (module Print) = make { current_namespace = item.parent_namespace } in
  List.map ~f:C.decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

let string_of_items =
  List.map ~f:string_of_item >> List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   From Hacspec Require Import Hacspec_Lib MachineIntegers.\n\
   From Coq Require Import ZArith.\n\
   Import List.ListNotations.\n\
   Open Scope Z_scope.\n\
   Open Scope bool_scope.\n"

let translate (bo : BackendOptions.t) (items : AST.item list) : Types.file list
    =
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"."
             (List.map
                ~f:(map_first_letter String.uppercase)
                (fst ns :: snd ns))
         in

         Types.
           {
             path = mod_name ^ ".v";
             contents =
               hardcoded_coq_headers ^ "\n" ^ string_of_items items ^ "\n";
           })

open Phase_utils

module TransformToInputLanguage =
  CatchErrors
    ([%functor_application
    Phases.Reject.RawOrMutPointer(Features.Rust)
    |> Phases.Reject.Arbitrary_lhs
    |> Phases.Reconstruct_for_loops
    |> Phases.Direct_and_mut
    |> Phases.Drop_references
    |> Phases.Trivialize_assign_lhs
    |> Phases.Reconstruct_question_marks
    |> Side_effect_utils.Hoist
    |> Phases.Local_mutation
    |> Phases.Reject.Continue
    |> Phases.Cf_into_monads
    |> Phases.Reject.EarlyExit
    |> Phases.Functionalize_loops
    |> Phases.Reject.As_pattern
    |> SubtypeToInputLanguage
    |> Identity
    ]
    [@ocamlformat "disable"])

let apply_phases (bo : BackendOptions.t) (i : Ast.Rust.item list) :
    AST.item list =
  List.concat_map ~f:TransformToInputLanguage.ditem i
