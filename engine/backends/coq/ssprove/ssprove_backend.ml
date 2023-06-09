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
      let backend = Diagnostics.Backend.SSProve
    end)

module RejectNotSSProve (FA : Features.T) = struct
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
        let slice _ = Features.On.slice
        let raw_pointer = reject
        let early_exit _ = Obj.magic ()
        let question_mark = reject
        let macro _ = Features.On.macro
        let as_pattern = reject
        let lifetime = reject
        let monadic_action = reject
        let arbitrary_lhs = reject
        let nontrivial_lhs = reject
        let monadic_binding _ = Features.On.monadic_binding
        let construct_base _ = Features.On.construct_base
        let state_passing_loop = reject
        let for_loop = reject

        let metadata =
          Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
      end)
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module U = Ast_utils.Make (InputLanguage)
open AST

module SSProveLibrary : Library = struct
  module Notation = struct
    let int_repr (x : string) (i : string) : string =
      "(" ^ "lift_to_both0" ^ " " ^ "(" ^ i ^ " " ^ ":" ^ " " ^ "int" ^ x ^ ")"
      ^ ")"

    let let_stmt (var : string) (expr : string) (typ : string) (body : string)
        (depth : int) : string =
      "letb" ^ " " ^ var ^ " " ^ ":=" ^ " (" ^ expr ^ ") " ^ ":" ^ " " ^ "both0"
      ^ "(" ^ typ ^ ")" ^ " " ^ "in" ^ newline_indent depth ^ body

    let let_mut_stmt = let_stmt
    let tuple_prefix : string = "prod_b0"
  end
end

module SSP = Coq (SSProveLibrary)

module Context = struct
  type t = { current_namespace : string * string list }
end

let primitive_to_string (id : primitive_ident) : string =
  match id with
  | Box -> "(TODO: BOX)" (* failwith "Box" *)
  | Deref -> "(TODO: Deref)" (* failwith "Deref" *)
  | Cast -> "cast_int"
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
    let __TODO_pat__ _ s = SSP.AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ _ s : SSP.AST.ty = SSP.AST.Name (s ^ " todo(ty)")
    let __TODO_item__ _ s = SSP.AST.Unimplemented (s ^ " todo(item)")

    let __TODO_term__ _ s =
      SSP.AST.Const (SSP.AST.Const_string (s ^ " todo(term)"))
  end

  module TODOs = struct
    let __TODO_ty__ span s : SSP.AST.ty =
      Error.unimplemented ~details:("[ty] node " ^ s) span

    let __TODO_pat__ span s =
      Error.unimplemented ~details:("[pat] node " ^ s) span

    let __TODO_term__ span s =
      Error.unimplemented ~details:("[expr] node " ^ s) span

    let __TODO_item__ span s = SSP.AST.Unimplemented (s ^ " todo(item)")
  end

  open TODOs

  let pint_kind (k : int_kind) : SSP.AST.int_type =
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

  let rec pliteral (e : literal) =
    match e with
    | String s -> SSP.AST.Const_string s
    | Char c -> SSP.AST.Const_char (Char.to_int c)
    | Int { value; kind } -> SSP.AST.Const_int (value, pint_kind kind)
    | Float _ -> failwith "Float: todo"
    | Bool b -> SSP.AST.Const_bool b

  let rec pty span (t : ty) : SSP.AST.ty =
    match t with
    | TBool -> SSP.AST.Bool
    | TChar -> __TODO_ty__ span "char"
    | TInt k -> SSP.AST.Int (pint_kind k)
    | TStr -> __TODO_ty__ span "str"
    | TFalse -> __TODO_ty__ span "false"
    | TApp { ident = `TupleType 0 as ident; args = [] } -> SSP.AST.Unit
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty span ty
    | TApp { ident = `TupleType n; args } when n >= 2 ->
        SSP.AST.Product (args_ty span args)
    | TApp { ident; args } ->
        SSP.AST.AppTy (pglobal_ident ident ^ "_t", args_ty span args)
    | TArrow (inputs, output) ->
        List.fold_right ~init:(pty span output)
          ~f:(fun x y -> SSP.AST.Arrow (x, y))
          (List.map ~f:(pty span) inputs)
    | TFloat -> failwith "pty: Float"
    | TArray { typ; length } ->
        SSP.AST.ArrayTy (pty span typ, "TODO: Int.to_string length")
    | TSlice { ty; _ } -> SSP.AST.SliceTy (pty span ty)
    | TParam i -> SSP.AST.Name i.name
    | TProjectedAssociatedType s ->
        SSP.AST.Wild
        (* __TODO_ty__ span ("proj:assoc:type" ^ s) *)
        (* failwith "proj:assoc:type" *)
    | _ -> .

  and args_ty span (args : generic_value list) : SSP.AST.ty list =
    (* List.map ~f:pty *)
    match args with
    | arg :: xs ->
        (match arg with
        | GLifetime { lt; witness } -> __TODO_ty__ span "lifetime"
        | GType x -> pty span x
        | GConst _ -> __TODO_ty__ span "const")
        :: args_ty span xs
    | [] -> []

  let rec ppat (p : pat) : SSP.AST.pat =
    match p.p with
    | PWild -> SSP.AST.Wild
    | PAscription { typ; pat } ->
        SSP.AST.AscriptionPat (ppat pat, pty p.span typ)
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat = None;
          var;
          typ = _ (* we skip type annot here *);
        } ->
        SSP.AST.Ident var.name
    | PArray { args } -> __TODO_pat__ p.span "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> SSP.AST.UnitPat
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        __TODO_pat__ p.span "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        SSP.AST.TuplePat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; record } ->
        SSP.AST.RecordPat (pglobal_ident_last name, pfield_pats args)
    | PConstant { lit } -> SSP.AST.Lit (pliteral lit)
    | PDeref { subpat } -> __TODO_pat__ p.span "deref"
    | _ -> .

  and pfield_pats (args : field_pat list) : (string * SSP.AST.pat) list =
    match args with
    | { field; pat } :: xs ->
        (pglobal_ident_last field, ppat pat) :: pfield_pats xs
    | _ -> []

  let operators =
    let c = GlobalIdent.of_string_exn in
    [
      ( c "std::core::array::update_array_at",
        (3, [ "nseq_array_or_seq "; ".["; "]<-"; "" ]) );
      ( c "core::ops::index::Index::index",
        (2, [ "nseq_array_or_seq "; ".["; "]" ]) );
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
      (c "hacspec::lib::foldi", (4, [ "foldi_both' "; " "; " (ssp"; ") "; "" ]));
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

  let rec pexpr (e : expr) : SSP.AST.term =
    let span = e.span in
    match e.e with
    | Literal e -> SSP.AST.Const (pliteral e)
    | LocalVar local_ident -> SSP.AST.Name local_ident.name
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        SSP.AST.UnitTerm
    | GlobalVar global_ident -> SSP.AST.Var (pglobal_ident global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        __TODO_term__ span "app global vcar projector tuple"
    | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
        let arity, op = Map.find_exn operators x in
        if List.length args <> arity then failwith "Bad arity";
        let args = List.map ~f:pexpr args in
        SSP.AST.AppFormat (op, args)
    (* | App { f = { e = GlobalVar x }; args } -> *)
    (*    __TODO_term__ span "GLOBAL APP?" *)
    | App { f; args } ->
        let base = pexpr f in
        let args = List.map ~f:pexpr args in
        SSP.AST.App (base, args)
    | If { cond; then_; else_ } ->
        SSP.AST.If
          ( pexpr cond,
            pexpr then_,
            Option.value_map else_ ~default:(SSP.AST.Literal "()") ~f:pexpr )
    | Array l -> SSP.AST.Array (List.map ~f:pexpr l)
    | Let { lhs; rhs; body; monadic = Some monad } ->
        SSP.AST.Let
          {
            pattern = ppat lhs;
            value = pexpr rhs;
            body = pexpr body;
            value_typ = pty span lhs.typ;
          }
    | Let { lhs; rhs; body; monadic = None } ->
        SSP.AST.Let
          {
            pattern = ppat lhs;
            value = pexpr rhs;
            body = pexpr body;
            value_typ = pty span lhs.typ;
          }
    | EffectAction _ -> __TODO_term__ span "monadic action"
    | Match { scrutinee; arms } ->
        SSP.AST.Match
          ( pexpr scrutinee,
            List.map
              ~f:(fun { arm = { arm_pat; body } } -> (ppat arm_pat, pexpr body))
              arms )
    | Ascription { e; typ } -> __TODO_term__ span "asciption"
    | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
        pexpr e
    | Construct { constructor = `TupleCons n; fields; base } ->
        SSP.AST.Tuple (List.map ~f:(snd >> pexpr) fields)
    | Construct { constructs_record = true; constructor; fields; base } ->
        SSP.AST.RecordConstructor
          ( SSP.AST.Var (pglobal_ident constructor ^ "_t"),
            List.map ~f:(fun (f, e) -> (pglobal_ident f, pexpr e)) fields )
    | Construct { constructor; fields = [ (f, e) ]; base } ->
        SSP.AST.App (SSP.AST.Var (pglobal_ident constructor), [ pexpr e ])
    | Construct { constructor; fields; base } ->
        SSP.AST.Var
          (pglobal_ident constructor ^ snd (SSP.ty_to_string (pty span e.typ)))
    | Closure { params; body } ->
        SSP.AST.Lambda (List.map ~f:ppat params, pexpr body)
    | MacroInvokation { macro; args; witness } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | _ -> .

  let rec pitem (e : item) : SSP.AST.decl list =
    let span = e.span in
    match e.v with
    | Fn { name; generics; body; params } ->
        [
          SSP.AST.ProgramDefinition
            ( pglobal_ident name,
              List.map
                ~f:(fun { pat; typ; typ_span } ->
                  (ppat pat, SSP.AST.AppTy ("both0", [ pty span typ ])))
                params,
              pexpr body,
              SSP.AST.AppTy ("both0", [ pty span body.typ ]) );
        ]
    | TyAlias { name; generics; ty } ->
        [ SSP.AST.Notation (pglobal_ident name ^ "_t", pty span ty) ]
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
          SSP.AST.Record
            ( pglobal_ident_last name ^ "_t" ^ pglobal_ident record_name,
              p_record_record span arguments );
        ]
    (* enum *)
    | Type { name; generics; variants; record = true } ->
        [
          SSP.AST.Inductive
            ( pglobal_ident_last name ^ "_t",
              List.fold_left ~init:[]
                ~f:(fun a b ->
                  a
                  @ [
                      (match b with
                      | GPType { ident; default } -> ident.name
                      | _ -> failwith "SSProve: TODO: generic_params");
                    ])
                generics.params,
              p_inductive span variants name );
        ]
    | Type { name; generics; variants } ->
        [
          SSP.AST.Notation
            ( pglobal_ident_last name ^ "_t",
              SSP.AST.Product (List.map ~f:snd (p_record span variants name)) );
          SSP.AST.Definition
            ( pglobal_ident_last name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy
                    ("both0", [ SSP.AST.Name (pglobal_ident_last name ^ "_t") ]),
                  SSP.AST.AppTy
                    ("both0", [ SSP.AST.Name (pglobal_ident_last name ^ "_t") ])
                ) );
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
          SSP.AST.Notation
            ( o.type_name ^ "_t",
              SSP.AST.NatMod
                (o.type_of_canvas, o.bit_size_of_field, o.modulo_value) );
          SSP.AST.Definition
            ( o.type_name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.type_name ^ "_t") ]),
                  SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.type_name ^ "_t") ])
                ) );
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
          SSP.AST.Notation
            ( o.bytes_name ^ "_t",
              SSP.AST.ArrayTy
                ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                  (* int_of_string *) o.size ) );
          SSP.AST.Definition
            ( o.bytes_name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.bytes_name ^ "_t") ]),
                  SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.bytes_name ^ "_t") ])
                ) );
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
          SSP.AST.Notation
            ( o.integer_name ^ "_t",
              SSP.AST.ArrayTy
                ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
                  Int.to_string ((o.bits + 7) / 8) ) );
          SSP.AST.Definition
            ( o.integer_name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy
                    ("both0", [ SSP.AST.Name (o.integer_name ^ "_t") ]),
                  SSP.AST.AppTy
                    ("both0", [ SSP.AST.Name (o.integer_name ^ "_t") ]) ) );
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
          SSP.AST.ArrayTy
            ( SSP.AST.Int { size = SSP.AST.U8; signed = false },
              (* int_of_string *) o.size )
        in
        [
          SSP.AST.Notation (o.bytes_name ^ "_t", typ);
          SSP.AST.Definition
            ( o.bytes_name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.bytes_name ^ "_t") ]),
                  SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.bytes_name ^ "_t") ])
                ) );
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
          | "U128" -> SSP.AST.U128
          (* Some *)
          | "U64" -> SSP.AST.U64
          (* Some *)
          | "U32" -> SSP.AST.U32
          (* Some *)
          | "U16" -> SSP.AST.U16
          (* Some *)
          | "U8" -> SSP.AST.U8
          | usize -> SSP.AST.U32 (* TODO: usize? *)
        in
        [
          SSP.AST.Notation
            ( o.array_name ^ "_t",
              SSP.AST.ArrayTy
                ( SSP.AST.Int { size = typ; signed = false },
                  (* int_of_string *) o.size ) );
          SSP.AST.Definition
            ( o.array_name,
              [],
              SSP.AST.Var "id",
              SSP.AST.Arrow
                ( SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.array_name ^ "_t") ]),
                  SSP.AST.AppTy ("both0", [ SSP.AST.Name (o.array_name ^ "_t") ])
                ) );
        ]
    | IMacroInvokation { macro; _ } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | Use { path; is_external; rename } ->
        if is_external then [] else [ SSP.AST.Require (path, rename) ]
    | HaxError s -> [ __TODO_item__ span s ]
    | NotImplementedYet -> [ __TODO_item__ span "Not implemented yet?" ]
    | Trait { name; generics; items } ->
        [
          SSP.AST.Class
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
                      | _ -> failwith "SSProve: TODO: generic_params");
                    ])
                generics.params );
        ]
    | Impl { generics; self_ty; of_trait = Some (name, gen_vals); items } ->
        [
          SSP.AST.Instance
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

  and p_inductive span variants parrent_name : SSP.AST.inductive_case list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        if (index_of_field >> Option.is_some) arg_name then
          SSP.AST.InductiveCase (pglobal_ident_last name, pty span arg_ty)
          :: p_inductive span xs parrent_name
        else
          SSP.AST.InductiveCase (pglobal_ident_last arg_name, pty span arg_ty)
          :: p_inductive span xs parrent_name
    | { name; arguments = [] } :: xs ->
        SSP.AST.BaseCase (pglobal_ident_last name)
        :: p_inductive span xs parrent_name
    | { name; arguments } :: xs ->
        SSP.AST.InductiveCase
          ( pglobal_ident_last name,
            SSP.AST.RecordTy (pglobal_ident name, p_record_record span arguments)
          )
        :: p_inductive span xs parrent_name
    | _ -> []

  and p_record span variants parrent_name : (string * SSP.AST.ty) list =
    match variants with
    | { name; arguments = [ (arg_name, arg_ty) ] } :: xs ->
        (pglobal_ident_last arg_name, pty span arg_ty)
        :: p_record span xs parrent_name
    | { name; arguments = [] } :: xs ->
        ("TODO FIELD?", __TODO_ty__ span "TODO")
        :: p_record span xs parrent_name
    | { name; arguments } :: xs ->
        ( pglobal_ident_last name,
          SSP.AST.RecordTy (pglobal_ident name, p_record_record span arguments)
        )
        :: p_record span xs parrent_name
    | _ -> []

  and p_record_record span arguments : (string * SSP.AST.ty) list =
    List.map
      ~f:(function
        | arg_name, arg_ty -> (pglobal_ident_last arg_name, pty span arg_ty))
      arguments
end

module type S = sig
  val pitem : item -> SSP.AST.decl list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item (item : item) : string =
  let (module Print) = make { current_namespace = item.parent_namespace } in
  List.map ~f:SSP.decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

let string_of_items =
  List.map ~f:string_of_item >> List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

let hardcoded_coq_headers =
  "(* File automatically generated by Hacspec *)\n\
   Set Warnings \"-notation-overridden,-ambiguous-paths\".\n\
   From Crypt Require Import choice_type Package Prelude.\n\
   Import PackageNotation.\n\
   From extructures Require Import ord fset.\n\
   From mathcomp Require Import ssrZ word.\n\
   From Jasmin Require Import word.\n\n\
   From Coq Require Import ZArith.\n\
   Import List.ListNotations.\n\
   Open Scope list_scope.\n\
   Open Scope Z_scope.\n\
   Open Scope bool_scope.\n\n\
   From Hacspec Require Import ChoiceEquality.\n\
   From Hacspec Require Import LocationUtility.\n\
   From Hacspec Require Import Hacspec_Lib_Comparable.\n\
   From Hacspec Require Import Hacspec_Lib_Pre.\n\
   From Hacspec Require Import Hacspec_Lib.\n\n\
   Open Scope hacspec_scope.\n\
   Import choice.Choice.Exports.\n\n\
   Obligation Tactic := try timeout 8 solve_ssprove_obligations.\n"

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
    |> Phases.Reject.Continue
    |> Phases.Drop_references
    |> Phases.Trivialize_assign_lhs
    |> Phases.Reconstruct_question_marks
    |> Side_effect_utils.Hoist
    |> Phases.Local_mutation
    |> Phases.Reject.Continue
    |> Phases.Cf_into_monads
    |> Phases.Reject.EarlyExit
    |> Phases.Functionalize_loops
    |> RejectNotSSProve
    |> Identity
    ]
    [@ocamlformat "disable"])

let apply_phases (bo : BackendOptions.t) (i : Ast.Rust.item) : AST.item list =
  TransformToInputLanguage.ditem i
