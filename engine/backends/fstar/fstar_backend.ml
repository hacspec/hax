open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Monadic_binding
      include On.Slice
      include On.Macro
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.FStar
    end)

module SubtypeToInputLanguage
    (FA : Features.T
            with type mutable_reference = Features.Off.mutable_reference
             and type continue = Features.Off.continue
             and type break = Features.Off.break
             and type mutable_reference = Features.Off.mutable_reference
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
             and type block = Features.Off.block
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

module FStarNamePolicy = struct
  include Concrete_ident.DefaultNamePolicy

  [@@@ocamlformat "disable"]

  let index_field_transform index = "_" ^ index

  let reserved_words = Hash_set.of_list (module String) ["attributes";"noeq";"unopteq";"and";"assert";"assume";"begin";"by";"calc";"class";"default";"decreases";"effect";"eliminate";"else";"end";"ensures";"exception";"exists";"false";"friend";"forall";"fun";"λ";"function";"if";"in";"include";"inline";"inline_for_extraction";"instance";"introduce";"irreducible";"let";"logic";"match";"returns";"as";"module";"new";"new_effect";"layered_effect";"polymonadic_bind";"polymonadic_subcomp";"noextract";"of";"open";"opaque";"private";"quote";"range_of";"rec";"reifiable";"reify";"reflectable";"requires";"set_range_of";"sub_effect";"synth";"then";"total";"true";"try";"type";"unfold";"unfoldable";"val";"when";"with";"_";"__SOURCE_FILE__";"__LINE__";"match";"if";"let";"and"]
end

module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (FStarNamePolicy)
open AST
module F = Fstar_ast

let doc_to_string : PPrint.document -> string =
  FStar_Pprint.pretty_string 1.0 (Z.of_int 100)

let term_to_string : F.AST.term -> string =
  FStar_Parser_ToDocument.term_to_document >> doc_to_string

let decl_to_string : F.AST.decl -> string =
  FStar_Parser_ToDocument.decl_to_document >> doc_to_string

module Context = struct
  type t = { current_namespace : string * string list; items : item list }
end

let magic_id_raw_local_ident = LocalIdent.var_id_of_int (-765142)

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pprim_ident (span : span) (id : primitive_ident) =
    match id with
    | Deref -> Error.assertion_failure span "pprim_ident Deref"
    | Cast -> F.lid [ "cast" ]
    | LogicalOp op -> (
        match op with
        | And -> F.lid [ "Prims"; "op_AmpAmp" ]
        | Or -> F.lid [ "Prims"; "op_BarBar" ])

  let rec pliteral span (e : literal) =
    match e with
    | String s -> F.Const.Const_string (s, F.dummyRange)
    | Char c -> F.Const.Const_char (Char.to_int c)
    | Int { value; kind = { size; signedness } } ->
        let open F.Const in
        let size =
          match size with
          | S8 -> Int8
          | S16 -> Int16
          | S32 -> Int32
          | S64 -> Int64
          | S128 ->
              Error.unimplemented
                ~details:
                  "128 literals (fail if pattern maching, otherwise TODO)" span
          | SSize -> Sizet
        in
        F.Const.Const_int
          ( value,
            Some
              ( (match signedness with Signed -> Signed | Unsigned -> Unsigned),
                size ) )
    | Float _ -> Error.unimplemented ~details:"pliteral: Float" span
    | Bool b -> F.Const.Const_bool b

  let pliteral_as_expr span (e : literal) =
    let h e = F.term @@ F.AST.Const (pliteral span e) in
    match e with
    | Int { value; kind = { size = S128; signedness } as s } ->
        let lit = h (Int { value; kind = { s with size = SSize } }) in
        let prefix = match signedness with Signed -> "i" | Unsigned -> "u" in
        F.mk_e_app (F.term_of_lid [ "pub_" ^ prefix ^ "128" ]) [ lit ]
    | _ -> h e

  let pconcrete_ident (id : concrete_ident) =
    let id = U.Concrete_ident_view.to_view id in
    let ns_crate, ns_path = ctx.current_namespace in
    if String.(ns_crate = id.crate) && [%eq: string list] ns_path id.path then
      F.lid [ id.definition ]
    else F.lid (id.crate :: (id.path @ [ id.definition ]))

  let rec pglobal_ident (span : span) (id : global_ident) =
    match id with
    | `Concrete cid -> pconcrete_ident cid
    | `Primitive prim_id -> pprim_ident span prim_id
    | `TupleType 0 -> F.lid [ "prims"; "unit" ]
    | `TupleCons n when n <= 1 ->
        Error.assertion_failure span
          ("Got a [TupleCons " ^ string_of_int n ^ "]")
    | `TupleType n when n <= 14 ->
        F.lid [ "FStar"; "Pervasives"; "tuple" ^ string_of_int n ]
    | `TupleCons n when n <= 14 ->
        F.lid [ "FStar"; "Pervasives"; "Mktuple" ^ string_of_int n ]
    | `TupleType n | `TupleCons n ->
        let reason = "F* doesn't support tuple of size greater than 14" in
        Error.raise
          {
            kind = UnsupportedTupleSize { tuple_size = Int64.of_int n; reason };
            span;
          }
    | `TupleField _ | `Projector _ ->
        Error.assertion_failure span
          ("pglobal_ident: expected to be handled somewhere else: "
         ^ show_global_ident id)

  let rec plocal_ident (e : LocalIdent.t) =
    F.id
    @@
    if [%eq: LocalIdent.id] e.id magic_id_raw_local_ident then e.name
    else
      U.Concrete_ident_view.local_name
        (match String.chop_prefix ~prefix:"impl " e.name with
        | Some name -> "impl_" ^ Int.to_string ([%hash: string] name)
        | _ -> e.name)

  let pfield_ident span (f : global_ident) : F.Ident.lident =
    match f with
    | `Concrete cid -> pconcrete_ident cid
    | `Projector (`TupleField (n, len)) | `TupleField (n, len) ->
        F.lid [ "_" ^ Int.to_string (n + 1) ]
    | `Projector (`Concrete cid) -> pconcrete_ident cid
    | _ ->
        Error.assertion_failure span
          ("pfield_ident: not a valid field name in F* backend: "
         ^ show_global_ident f)

  let index_of_field_concrete id =
    try Some (Int.of_string @@ U.Concrete_ident_view.to_definition_name id)
    with _ -> None

  let index_of_field = function
    | `Concrete id -> index_of_field_concrete id
    | `TupleField (nth, _) -> Some nth
    | _ -> None

  let is_field_an_index = index_of_field >> Option.is_some

  let operators =
    let c = Global_ident.of_name Value in
    [
      (c Rust_primitives__hax__array_of_list, (3, ".[]<-"));
      (c Core__ops__index__Index__index, (2, ".[]"));
      (c Core__ops__bit__BitXor__bitxor, (2, "^."));
      (c Core__ops__bit__BitAnd__bitand, (2, "&."));
      (c Core__ops__bit__BitOr__bitor, (2, "|."));
      (c Core__ops__bit__Not__not, (1, "~."));
      (c Core__ops__arith__Add__add, (2, "+."));
      (c Core__ops__arith__Sub__sub, (2, "-."));
      (c Core__ops__arith__Mul__mul, (2, "*."));
      (c Core__ops__arith__Div__div, (2, "/."));
      (c Core__ops__arith__Rem__rem, (2, "%."));
      (c Core__ops__bit__Shl__shl, (2, ">>."));
      (c Core__ops__bit__Shr__shr, (2, "<<."));
      (c Core__cmp__PartialEq__eq, (2, "=."));
      (c Core__cmp__PartialOrd__lt, (2, "<."));
      (c Core__cmp__PartialOrd__le, (2, "<=."));
      (c Core__cmp__PartialEq__ne, (2, "<>."));
      (c Core__cmp__PartialOrd__ge, (2, ">=."));
      (c Core__cmp__PartialOrd__gt, (2, ">."));
    ]
    |> Map.of_alist_exn (module Global_ident)

  let rec pty span (t : ty) =
    match t with
    | TBool -> F.term_of_lid [ "bool" ]
    | TChar -> F.term_of_lid [ "char" ]
    | TInt k -> F.term_of_lid [ show_int_kind k ]
    | TStr -> F.term_of_lid [ "string" ]
    | TSlice { ty; _ } -> F.mk_e_app (F.term_of_lid [ "slice" ]) [ pty span ty ]
    | TApp { ident = `TupleType 0 as ident; args = [] } ->
        F.term @@ F.AST.Name (pglobal_ident span ident)
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty span ty
    | TApp { ident = `TupleType n; args } when n >= 2 -> (
        let args =
          List.filter_map
            ~f:(function GType t -> Some (pty span t) | _ -> None)
            args
        in
        let mk_star a b = F.term @@ F.AST.Op (F.id "&", [ a; b ]) in
        match args with
        | hd :: tl ->
            F.term @@ F.AST.Paren (List.fold_left ~init:hd ~f:mk_star tl)
        | _ -> Error.assertion_failure span "Tuple type: bad arity")
    | TApp { ident; args } ->
        let base = F.term @@ F.AST.Name (pglobal_ident span ident) in
        let args = List.map ~f:(pgeneric_value span) args in
        F.mk_e_app base args
    | TArrow (inputs, output) ->
        F.mk_e_arrow (List.map ~f:(pty span) inputs) (pty span output)
    | TFloat _ -> Error.unimplemented ~details:"pty: Float" span
    | TArray { typ; length } ->
        F.mk_e_app (F.term_of_lid [ "array" ]) [ pty span typ; pexpr length ]
    | TParam i -> F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident i)
    | TAssociatedType s -> F.term @@ F.AST.Wild
    | TOpaque s -> F.term @@ F.AST.Wild
    | _ -> .

  and pgeneric_value span (g : generic_value) =
    match g with
    | GType ty -> pty span ty
    | GConst e -> pexpr e
    | GLifetime _ -> .

  and ppat (p : pat) =
    match p.p with
    | PWild -> F.wild
    | PAscription { typ; pat } ->
        F.pat @@ F.AST.PatAscribed (ppat pat, (pty p.span typ, None))
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
    | PConstruct { name; args; is_record; is_struct } ->
        let pat_rec () =
          F.pat @@ F.AST.PatRecord (List.map ~f:pfield_pat args)
        in
        if is_struct && is_record then pat_rec ()
        else
          let pat_name = F.pat @@ F.AST.PatName (pglobal_ident p.span name) in
          let is_payload_record =
            List.for_all ~f:(fun { field } -> is_field_an_index field) args
            |> not
          in
          F.pat_app pat_name
          @@
          if is_payload_record then [ pat_rec () ]
          else List.map ~f:(fun { field; pat } -> ppat pat) args
    | PConstant { lit } -> F.pat @@ F.AST.PatConst (pliteral p.span lit)
    | _ -> .

  and pfield_pat ({ field; pat } : field_pat) =
    (pglobal_ident pat.span field, ppat pat)

  and pexpr (e : expr) =
    try pexpr_unwrapped e
    with Diagnostics.SpanFreeError.Exn _ ->
      (* let typ = *)
      (* try pty e.span e.typ *)
      (* with Diagnostics.SpanFreeError _ -> U.hax_failure_typ *)
      (* in *)
      F.term @@ F.AST.Const (F.Const.Const_string ("failure", F.dummyRange))

  and pexpr_unwrapped (e : expr) =
    match e.e with
    | Literal l -> pliteral_as_expr e.span l
    | LocalVar local_ident ->
        F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident local_ident)
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        F.AST.unit_const F.dummyRange
    | GlobalVar global_ident ->
        F.term @@ F.AST.Var (pglobal_ident e.span @@ global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        F.term
        @@ F.AST.Project (pexpr arg, F.lid [ "_" ^ string_of_int (n + 1) ])
    | App { f = { e = GlobalVar (`Projector (`Concrete cid)) }; args = [ arg ] }
      ->
        F.term @@ F.AST.Project (pexpr arg, pconcrete_ident cid)
    | App { f = { e = GlobalVar x }; args } when Map.mem operators x ->
        let arity, op = Map.find_exn operators x in
        if List.length args <> arity then
          Error.assertion_failure e.span
            "pexpr: bad arity for operator application";
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
    | Array l ->
        let len = List.length l in
        let body = F.AST.mkConsList F.dummyRange (List.map ~f:pexpr l) in
        let array_of_list =
          let id =
            Concrete_ident.of_name Value Rust_primitives__hax__array_of_list
          in
          F.term @@ F.AST.Name (pconcrete_ident id)
        in
        let list_ident = F.id "list" in
        let list = F.term_of_lid [ "list" ] in
        let array = F.mk_e_app array_of_list [ list ] in
        let assert_norm =
          F.term_of_lid [ "FStar"; "Pervasives"; "assert_norm" ]
        in
        let equality = F.term_of_lid [ "Prims"; "eq2" ] in
        let length = F.term_of_lid [ "List"; "Tot"; "length" ] in
        let length = F.mk_e_app length [ list ] in
        let len =
          F.term @@ F.AST.Const (F.Const.Const_int (Int.to_string len, None))
        in
        let formula = F.mk_e_app equality [ length; len ] in
        let assertion = F.mk_e_app assert_norm [ formula ] in
        let pat = F.AST.PatVar (list_ident, None, []) |> F.pat in
        F.term
        @@ F.AST.Let
             ( NoLetQualifier,
               [ (None, (pat, body)) ],
               F.term @@ F.AST.Seq (assertion, array) )
    | Let { lhs; rhs; body; monadic = Some monad } ->
        let p =
          F.pat @@ F.AST.PatAscribed (ppat lhs, (pty lhs.span lhs.typ, None))
        in
        let op = "let" ^ match monad with _ -> "*" in
        F.term @@ F.AST.LetOperator ([ (F.id op, p, pexpr rhs) ], pexpr body)
    | Let { lhs; rhs; body; monadic = None } ->
        let p =
          (* TODO: temp patch that remove annotation when we see an associated type *)
          if [%matches? TAssociatedType _] @@ U.remove_tuple1 lhs.typ then
            ppat lhs
          else
            F.pat @@ F.AST.PatAscribed (ppat lhs, (pty lhs.span lhs.typ, None))
        in
        F.term
        @@ F.AST.Let (NoLetQualifier, [ (None, (p, pexpr rhs)) ], pexpr body)
    | EffectAction _ -> .
    | Match { scrutinee; arms } ->
        F.term
        @@ F.AST.Match (pexpr scrutinee, None, None, List.map ~f:parm arms)
    | Ascription { e; typ } ->
        F.term @@ F.AST.Ascribed (pexpr e, pty e.span typ, None, false)
    | Construct { constructor = `TupleCons 1; fields = [ (_, e') ]; base } ->
        pexpr e'
    | Construct { constructor = `TupleCons n; fields; base = None } ->
        F.AST.mkTuple (List.map ~f:(snd >> pexpr) fields) F.dummyRange
    | Construct
        { is_record = true; is_struct = true; constructor; fields; base } ->
        F.term
        @@ F.AST.Record
             ( Option.map ~f:(fst >> pexpr) base,
               List.map
                 ~f:(fun (f, e) -> (pfield_ident e.span f, pexpr e))
                 fields )
    | Construct { is_record = false; constructor; fields; base } ->
        if [%matches? Some _] base then
          Diagnostics.failure ~context:(Backend FStar) ~span:e.span
            (AssertionFailure { details = "non-record type with base present" });
        F.mk_e_app (F.term @@ F.AST.Name (pglobal_ident e.span constructor))
        @@ List.map ~f:(snd >> pexpr) fields
    | Construct { is_record = true; constructor; fields; base } ->
        let r =
          F.term
          @@ F.AST.Record
               ( Option.map ~f:(fst >> pexpr) base,
                 List.map
                   ~f:(fun (f, e') -> (pglobal_ident e.span f, pexpr e'))
                   fields )
        in
        F.mk_e_app
          (F.term @@ F.AST.Name (pglobal_ident e.span constructor))
          [ r ]
    | Closure { params; body } ->
        F.mk_e_abs (List.map ~f:ppat params) (pexpr body)
    | Return { e } ->
        F.term @@ F.AST.App (F.term_of_lid [ "RETURN_STMT" ], pexpr e, Nothing)
    | MacroInvokation { macro; args; witness } ->
        Error.raise
        @@ {
             kind = UnsupportedMacro { id = [%show: global_ident] macro };
             span = e.span;
           }
    | _ -> .

  and parm { arm = { arm_pat; body } } = (ppat arm_pat, None, pexpr body)

  let rec pgeneric_param span (p : generic_param) : F.AST.pattern =
    let mk_implicit (ident : local_ident) ty =
      let v =
        F.pat @@ F.AST.PatVar (plocal_ident ident, Some F.AST.Implicit, [])
      in
      F.pat @@ F.AST.PatAscribed (v, (ty, None))
    in
    let ident = p.ident in
    match p.kind with
    | GPLifetime _ -> Error.assertion_failure span "pgeneric_param:LIFETIME"
    | GPType { default = None } ->
        mk_implicit ident (F.term @@ F.AST.Name (F.lid [ "Type" ]))
    | GPType _ ->
        Error.unimplemented span ~details:"pgeneric_param:Type with default"
    | GPConst { typ } -> mk_implicit ident (pty span typ)

  let rec pgeneric_constraint span (nth : int) (c : generic_constraint) =
    match c with
    | GCLifetime _ -> .
    | GCType { typ; implements; id } ->
        let implements : trait_ref = implements in
        let trait = F.term @@ F.AST.Name (pconcrete_ident implements.trait) in
        let args = List.map ~f:(pgeneric_value span) implements.args in
        let tc = F.mk_e_app trait (*pty typ::*) args in
        F.pat
        @@ F.AST.PatAscribed (F.pat_var_tcresolve @@ Some ("i" ^ id), (tc, None))

  let rec pgeneric_param_bd span (p : generic_param) =
    let ident = p.ident in
    match p.kind with
    | GPLifetime _ -> .
    | GPType { default = _ } ->
        let t = F.term @@ F.AST.Name (F.lid [ "Type" ]) in
        F.mk_e_binder (F.AST.Annotated (plocal_ident ident, t))
    | GPType _ ->
        Error.unimplemented span ~details:"pgeneric_param_bd:Type with default"
    | GPConst { typ } ->
        F.mk_e_binder (F.AST.Annotated (plocal_ident ident, pty span typ))

  let pgeneric_param_ident span (p : generic_param) =
    match (pgeneric_param_bd span p).b with
    | Annotated (ident, _) -> ident
    | _ -> failwith "pgeneric_param_ident"

  (* let rec ptrait_ref span (typ : F.AST.term) (trait_ref : trait_ref) = *)
  (*   let trait = F.term @@ F.AST.Name (pconcrete_ident implements.trait) in *)
  (*   let args = List.map ~f:(pgeneric_value span) implements.args in *)
  (*   F.mk_e_app trait args *)

  let rec pgeneric_constraint_type span (c : generic_constraint) =
    match c with
    | GCLifetime _ ->
        Error.assertion_failure span "pgeneric_constraint_bd:LIFETIME"
    | GCType { typ; implements } ->
        let implements : trait_ref = implements in
        let trait = F.term @@ F.AST.Name (pconcrete_ident implements.trait) in
        let args = List.map ~f:(pgeneric_value span) implements.args in
        F.mk_e_app trait args

  let rec pgeneric_constraint_bd span (c : generic_constraint) =
    let tc = pgeneric_constraint_type span c in
    F.AST.
      {
        b = F.AST.Annotated (F.generate_fresh_ident (), tc);
        brange = F.dummyRange;
        blevel = Un;
        aqual = None;
        battributes = [];
      }

  let pgenerics span generics =
    List.map ~f:(pgeneric_param_bd span) generics.params
    @ List.map ~f:(pgeneric_constraint_bd span) generics.constraints

  let get_attr (type a) (name : string) (map : string -> a) (attrs : attrs) :
      a option =
    List.find_map
      ~f:(fun attr ->
        match attr.kind with
        | Tool { path; tokens } when [%eq: string] path name ->
            Some (map tokens)
        | _ -> None)
      attrs

  module UUID : sig
    type t

    val of_attrs : attrs -> t option
    val associated_items : ?kind:string -> t option -> item list
    val associated_item : ?kind:string -> t option -> item option
  end = struct
    (* TODO: parse_quoted_string is incorrect *)
    let parse_quoted_string = String.strip ~drop:([%eq: char] '"')

    let parse_associated_with s =
      let uuid, kind = String.lsplit2 ~on:',' s |> Option.value_exn in
      let uuid = parse_quoted_string uuid in
      let kind = String.strip ~drop:([%eq: char] ' ') kind in
      (uuid, kind)

    type t = string

    let of_attrs : attrs -> t option = get_attr "_hax::uuid" parse_quoted_string

    let associated_items ?kind (uuid : t option) : item list =
      let ( let* ) x f = Option.bind ~f x in
      Option.value ~default:[]
        (let* uuid = uuid in
         List.filter
           ~f:(fun item ->
             Option.value ~default:false
               (let* uuid', kind' =
                  get_attr "_hax::associated_with" parse_associated_with
                    item.attrs
                in
                let kind_eq =
                  match kind with
                  | Some kind -> String.equal kind' kind
                  | None -> true
                in
                Some (kind_eq && String.equal uuid' uuid)))
           ctx.items
         |> Option.some)

    let associated_item ?kind (uuid : t option) : item option =
      match associated_items ?kind uuid with
      | [ i ] -> Some i
      | [] -> None
      | _ -> failwith "expected 0-1 items"
  end

  (* TODO: incorrect *)
  let fvar_of_params = function
    | { pat = { p = PBinding { var; _ }; _ }; _ } -> var
    | _ -> failwith "?? todo"

  let associated_refinement (free_variables : string list) (attrs : attrs) :
      expr option =
    UUID.associated_item ~kind:"refinement" (UUID.of_attrs attrs)
    |> Option.map ~f:(function
         | { v = Fn { params; body; _ }; _ } ->
             let substs =
               List.zip_exn
                 (List.map ~f:fvar_of_params params)
                 (List.map
                    ~f:(fun name ->
                      LocalIdent.{ id = magic_id_raw_local_ident; name })
                    free_variables)
             in
             let v =
               U.Mappers.rename_local_idents (fun i ->
                   match List.find ~f:(fst >> [%eq: local_ident] i) substs with
                   | None -> i
                   | Some (_, i) -> i)
             in
             v#visit_expr () body
         | _ -> failwith "expected associated_refinement")

  let pmaybe_refined_ty span (free_variables : string list) (attrs : attrs)
      (binder_name : string) (ty : ty) : F.AST.term =
    match associated_refinement free_variables attrs with
    | Some refinement ->
        F.mk_refined binder_name (pty span ty) (fun ~x -> pexpr refinement)
    | None -> pty span ty
  (* let prefined_ty span (binder : string) (ty : ty) (refinement : expr) : *)
  (*     F.AST.term = *)
  (*   F.mk_refined binder (pty span ty) (pexpr refinement) *)

  let rec pitem (e : item) : [> `Item of F.AST.decl | `Comment of string ] list
      =
    try pitem_unwrapped e
    with Diagnostics.SpanFreeError.Exn error ->
      let error = Diagnostics.SpanFreeError.payload error in
      let error = [%show: Diagnostics.Context.t * Diagnostics.kind] error in
      [
        `Comment
          ("item error backend: " ^ error ^ "\n\nLast AST:\n"
          ^ (U.LiftToFullAst.item e |> Print_rust.pitem_str));
      ]

  and pitem_unwrapped (e : item) :
      [> `Item of F.AST.decl | `Comment of string ] list =
    match e.v with
    | Alias { name; item } ->
        let pat =
          F.pat
          @@ F.AST.PatVar
               (F.id @@ U.Concrete_ident_view.to_definition_name name, None, [])
        in
        F.decls ~quals:[ F.AST.Unfold_for_unification_and_vcgen ]
        @@ F.AST.TopLevelLet
             ( NoLetQualifier,
               [ (pat, F.term @@ F.AST.Name (pconcrete_ident item)) ] )
    | Fn { name; generics; body; params } ->
        let pat =
          F.pat
          @@ F.AST.PatVar
               (F.id @@ U.Concrete_ident_view.to_definition_name name, None, [])
        in
        let pat =
          F.pat
          @@ F.AST.PatApp
               ( pat,
                 List.map ~f:(pgeneric_param e.span) generics.params
                 @ List.mapi
                     ~f:(pgeneric_constraint e.span)
                     generics.constraints
                 @ List.map
                     ~f:(fun { pat; typ_span; typ } ->
                       let span = Option.value ~default:e.span typ_span in
                       F.pat
                       @@ F.AST.PatAscribed (ppat pat, (pty span typ, None)))
                     params )
        in
        let pat =
          F.pat @@ F.AST.PatAscribed (pat, (pty body.span body.typ, None))
        in
        F.decls @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, pexpr body) ])
    | TyAlias { name; generics; ty } ->
        let pat =
          F.pat
          @@ F.AST.PatVar
               (F.id @@ U.Concrete_ident_view.to_definition_name name, None, [])
        in
        F.decls ~quals:[ F.AST.Unfold_for_unification_and_vcgen ]
        @@ F.AST.TopLevelLet
             ( NoLetQualifier,
               [
                 ( F.pat
                   @@ F.AST.PatApp
                        ( pat,
                          List.map ~f:(pgeneric_param e.span) generics.params
                          @ List.mapi
                              ~f:(pgeneric_constraint e.span)
                              generics.constraints ),
                   pty e.span ty );
               ] )
    | Type
        {
          name;
          generics;
          variants = [ { arguments; is_record = true; _ } ];
          is_struct = true;
        } ->
        F.decls
        @@ F.AST.Tycon
             ( false,
               false,
               [
                 F.AST.TyconRecord
                   ( F.id @@ U.Concrete_ident_view.to_definition_name name,
                     pgenerics e.span generics,
                     None,
                     [],
                     List.map
                       ~f:(fun (prev, (field, ty, attrs)) ->
                         let fname : string =
                           U.Concrete_ident_view.to_definition_name field
                         in
                         let fvars =
                           List.map prev ~f:(fun (field, _, _) ->
                               U.Concrete_ident_view.to_definition_name field)
                         in
                         ( F.id fname,
                           None,
                           [],
                           pmaybe_refined_ty e.span fvars attrs fname ty ))
                       (inits arguments) );
               ] )
    | Type { name; generics; variants; _ } ->
        let self =
          F.mk_e_app
            (F.term_of_lid [ U.Concrete_ident_view.to_definition_name name ])
            (List.map ~f:(pgeneric_param_ident e.span) generics.params
            |> List.map ~f:(fun id -> F.term @@ F.AST.Name (F.lid_of_id id)))
        in

        let constructors =
          List.map
            ~f:(fun { name; arguments; is_record; _ } ->
              ( F.id (U.Concrete_ident_view.to_definition_name name),
                Some
                  (let field_indexes =
                     List.map ~f:(fst3 >> index_of_field_concrete) arguments
                   in
                   if is_record then
                     F.AST.VpRecord
                       ( List.map
                           ~f:(fun (field, ty, attrs) ->
                             let fname : string =
                               U.Concrete_ident_view.to_definition_name field
                             in
                             (F.id fname, None, [], pty e.span ty))
                           arguments,
                         Some self )
                   else
                     F.AST.VpArbitrary
                       (F.term
                       @@ F.AST.Product
                            ( List.map
                                ~f:(fun (_, ty, _) ->
                                  F.mk_e_binder @@ F.AST.NoName (pty e.span ty))
                                arguments,
                              self ))),
                [] ))
            variants
        in
        F.decls
        @@ F.AST.Tycon
             ( false,
               false,
               [
                 F.AST.TyconVariant
                   ( F.id @@ U.Concrete_ident_view.to_definition_name name,
                     pgenerics e.span generics,
                     None,
                     constructors );
               ] )
    | IMacroInvokation { macro; argument; span } -> (
        let open Hacspeclib_macro_parser in
        let unsupported_macro () =
          Error.raise
          @@ {
               kind = UnsupportedMacro { id = [%show: concrete_ident] macro };
               span = e.span;
             }
        in
        match U.Concrete_ident_view.to_view macro with
        | { crate = "hacspec_lib"; path = _; definition = name } -> (
            let unwrap r =
              match r with
              | Ok r -> r
              | Error details ->
                  let macro_id = [%show: concrete_ident] macro in
                  Error.raise
                    {
                      kind = ErrorParsingMacroInvocation { macro_id; details };
                      span = e.span;
                    }
            in
            let mk_typ_name name = "t_" ^ String.lowercase name in
            match name with
            | "public_nat_mod" ->
                let o = PublicNatMod.parse argument |> unwrap in
                (F.decls_of_string @@ "unfold type " ^ mk_typ_name o.type_name
               ^ "  = nat_mod 0x" ^ o.modulo_value)
                @ F.decls_of_string @@ "unfold type "
                ^ mk_typ_name o.type_of_canvas
                ^ "  = lseq pub_uint8 "
                ^ string_of_int o.bit_size_of_field
            | "bytes" ->
                let o = Bytes.parse argument |> unwrap in
                F.decls_of_string @@ "unfold type " ^ mk_typ_name o.bytes_name
                ^ "  = lseq uint8 " ^ o.size
            | "public_bytes" ->
                let o = Bytes.parse argument |> unwrap in
                F.decls_of_string @@ "unfold type " ^ mk_typ_name o.bytes_name
                ^ "  = lseq uint8 " ^ o.size
            | "array" ->
                let o = Array.parse argument |> unwrap in
                let typ =
                  match o.typ with
                  | "U32" -> "uint32"
                  | "U16" -> "uint16"
                  | "U8" -> "uint8"
                  | usize -> "uint_size"
                in
                let size = o.size in
                let array_def =
                  F.decls_of_string @@ "unfold type " ^ mk_typ_name o.array_name
                  ^ "  = lseq " ^ typ ^ " " ^ size
                in
                let index_def =
                  match o.index_typ with
                  | Some index ->
                      F.decls_of_string @@ "unfold type "
                      ^ mk_typ_name (o.array_name ^ "_idx")
                      ^ " = nat_mod " ^ size
                  | None -> []
                in
                array_def @ index_def
            | "unsigned_public_integer" ->
                let o = UnsignedPublicInteger.parse argument |> unwrap in
                F.decls_of_string @@ "unfold type " ^ mk_typ_name o.integer_name
                ^ "  = lseq uint8 ("
                ^ (Int.to_string @@ ((o.bits + 7) / 8))
                ^ ")"
            | _ -> unsupported_macro ())
        | _ -> unsupported_macro ())
    | Trait { name; generics; items } ->
        let bds = List.map ~f:(pgeneric_param_bd e.span) generics.params in
        let name_str = U.Concrete_ident_view.to_definition_name name in
        let name = F.id @@ name_str in
        let fields =
          List.concat_map
            ~f:(fun i ->
              let name = U.Concrete_ident_view.to_definition_name i.ti_ident in
              let bds = pgenerics i.ti_span i.ti_generics in
              let fields =
                match i.ti_v with
                | TIType bounds ->
                    let t = F.term @@ F.AST.Name (F.lid [ "Type" ]) in
                    (* let constraints = *)
                    (*   List.map *)
                    (*     ~f:(fun implements -> *)
                    (*       { typ = TApp { ident = i.ti_ident } }) *)
                    (*     bounds *)
                    (* in *)
                    (F.id name, None, [], t)
                    :: List.map
                         ~f:(fun { trait; args } ->
                           let base =
                             F.term @@ F.AST.Name (pconcrete_ident trait)
                           in
                           let args =
                             List.map ~f:(pgeneric_value e.span) args
                           in
                           (F.id name, None, [], F.mk_e_app base args))
                         bounds
                | TIFn ty -> [ (F.id name, None, [], pty e.span ty) ]
              in
              List.map ~f:Fn.id
                (* ~f:(fun (n, q, a, ty) -> (n, q, a, F.mk_e_app bds ty)) *)
                fields)
            items
        in
        let constraints_fields =
          generics.constraints
          |> List.map ~f:(fun c ->
                 let hash = Int.to_string ([%hash: generic_constraint] c) in
                 let name = "__constraint_" ^ hash ^ "_" ^ name_str in
                 let typ = pgeneric_constraint_type e.span c in
                 (F.id name, None, [], typ))
        in
        let fields = constraints_fields @ fields in
        let fields =
          if List.is_empty fields then
            let marker_field = "__marker_trait_" ^ name_str in
            [ (F.id marker_field, None, [], pty e.span U.unit_typ) ]
          else fields
        in
        let tcdef = F.AST.TyconRecord (name, bds, None, [], fields) in
        let d = F.AST.Tycon (false, true, [ tcdef ]) in
        [ `Item { d; drange = F.dummyRange; quals = []; attrs = [] } ]
    | Impl { generics; self_ty = _; of_trait = trait, generic_args; items } ->
        (* this unique name is stupid, we have disambiguators... And things will be refered differently! very stupid, TODO *)
        let unique_name_todo = "impl_" ^ Int.to_string ([%hash: item] e) in
        let pat = F.pat @@ F.AST.PatVar (F.id unique_name_todo, None, []) in
        let pat =
          F.pat
          @@ F.AST.PatApp
               ( pat,
                 List.map ~f:(pgeneric_param e.span) generics.params
                 @ List.mapi
                     ~f:(pgeneric_constraint e.span)
                     generics.constraints )
        in
        let typ =
          F.mk_e_app
            (F.term @@ F.AST.Name (pglobal_ident e.span trait))
            (List.map ~f:(pgeneric_value e.span) generic_args)
        in
        let pat = F.pat @@ F.AST.PatAscribed (pat, (typ, None)) in
        let fields =
          List.map
            ~f:(fun { ii_span; ii_generics; ii_v; ii_ident } ->
              let name = U.Concrete_ident_view.to_definition_name ii_ident in
              ( F.lid [ name ],
                match ii_v with
                | IIFn { body; params } ->
                    let pats =
                      List.map ~f:(pgeneric_param ii_span) generics.params
                      @ List.mapi
                          ~f:(pgeneric_constraint ii_span)
                          generics.constraints
                      @ List.map
                          ~f:(fun { pat; typ_span; typ } ->
                            let span = Option.value ~default:ii_span typ_span in
                            F.pat
                            @@ F.AST.PatAscribed (ppat pat, (pty span typ, None)))
                          params
                    in
                    F.mk_e_abs pats (pexpr body)
                | IIType ty -> pty ii_span ty ))
            items
        in
        let fields =
          if List.is_empty fields then
            [ (F.lid [ "__marker_trait" ], pexpr (U.unit_expr e.span)) ]
          else fields
        in
        let body = F.term @@ F.AST.Record (None, fields) in
        F.decls @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, body) ])
    | HaxError details ->
        [
          `Comment
            ("item error backend: " ^ details ^ "\n\nLast AST:\n"
            ^ (U.LiftToFullAst.item e |> Print_rust.pitem_str));
        ]
    | Use _ (* TODO: Not Yet Implemented *) | NotImplementedYet -> []
    | _ -> .
end

module type S = sig
  val pitem : item -> [> `Item of F.AST.decl | `Comment of string ] list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item items (item : item) : string =
  let (module Print) =
    make
      {
        current_namespace = U.Concrete_ident_view.to_namespace item.ident;
        items;
      }
  in
  List.map ~f:(function
    | `Item i -> decl_to_string i
    | `Comment s -> "(* " ^ s ^ " *)")
  @@ Print.pitem item
  |> String.concat ~sep:"\n"

let string_of_items items =
  List.map ~f:(string_of_item items) items
  |> List.map ~f:String.strip
  |> List.filter ~f:(String.is_empty >> not)
  |> String.concat ~sep:"\n\n"

let hardcoded_fstar_headers =
  "\n#set-options \"--fuel 0 --ifuel 1 --z3rlimit 15\"\nopen Core"

let translate (bo : BackendOptions.t) (items : AST.item list) : Types.file list
    =
  let show_view Concrete_ident.{ crate; path; definition } =
    crate :: (path @ [ definition ]) |> String.concat ~sep:"::"
  in
  Stdlib.prerr_endline @@ "[translate]"
  ^ [%show: string list]
      (List.map
         ~f:(fun i -> U.Concrete_ident_view.to_view i.ident |> show_view)
         items);
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
             path = mod_name ^ ".fst";
             contents =
               "module " ^ mod_name ^ hardcoded_fstar_headers ^ "\n\n"
               ^ string_of_items items;
           })

open Phase_utils
module DepGraph = Dependencies.Make (InputLanguage)
module DepGraphR = Dependencies.Make (Features.Rust)

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.RawOrMutPointer(Features.Rust)
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_for_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
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
  [@ocamlformat "disable"]

let apply_phases (bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  let items =
    (* let hax_core_extraction = *)
    (*   Sys.getenv "HAX_CORE_EXTRACTION_MODE" *)
    (*   |> [%equal: string option] (Some "on") *)
    (* in *)
    (* if hax_core_extraction then *)
    (*   let names = *)
    (*     Core_names.names |> List.map ~f:(Concrete_ident.of_def_id Value) *)
    (*   in *)
    (*   DepGraphR.ItemGraph.transitive_dependencies_of_items names items *)
    (* else *)
    items
  in
  let items =
    TransformToInputLanguage.ditems items
    |> List.map ~f:U.Mappers.add_typ_ascription
    (* |> DepGraph.name_me *)
  in
  items
