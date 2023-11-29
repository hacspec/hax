open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Monadic_binding

      (* include On.Mutable_reference *)
      (* include On.Reference *)
      include On.Slice
      include On.Macro

      (* include On.Lifetime *)
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.FStar
    end)

module SubtypeToInputLanguage
    (FA : Features.T
            with type continue = Features.Off.continue
             and type break = Features.Off.break
             and type mutable_pointer = Features.Off.mutable_pointer
             and type mutable_variable = Features.Off.mutable_variable
             and type reference = Features.Off.reference
             and type mutable_reference = Features.Off.mutable_reference
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

        (* include Features.SUBTYPE.On.Mutable_reference *)
        (* include Features.SUBTYPE.On.Reference *)
        (* include Features.SUBTYPE.On.Lifetime *)
        include Features.SUBTYPE.On.Construct_base
        include Features.SUBTYPE.On.Slice
        include Features.SUBTYPE.On.Macro
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)

module BackendOptions = struct
  type t = Hax_engine.Types.f_star_options
end

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

module Make
    (Attrs : Attrs.WITH_ITEMS) (Ctx : sig
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

  let pnegative = function true -> "-" | false -> ""

  let is_never_to_any : expr -> bool =
    U.Expect.concrete_app1 Rust_primitives__hax__never_to_any >> Option.is_some

  let rec pliteral span (e : literal) =
    match e with
    | String s -> F.Const.Const_string (s, F.dummyRange)
    | Char c -> F.Const.Const_char (Char.to_int c)
    | Int { value; kind = { size; signedness }; negative } ->
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
          | SSize ->
              Error.unimplemented
                ~details:
                  "usize literals (fail if pattern maching, otherwise TODO)"
                span
        in
        F.Const.Const_int
          ( pnegative negative ^ value,
            Some
              ( (match signedness with Signed -> Signed | Unsigned -> Unsigned),
                size ) )
    | Float _ -> Error.unimplemented ~details:"pliteral: Float" span
    | Bool b -> F.Const.Const_bool b

  let pliteral_as_expr span (e : literal) =
    let mk_const c = F.AST.Const c |> F.term in
    let mk_nat value negative =
      mk_const (F.Const.Const_int (pnegative negative ^ value, None))
    in
    let wrap_app fn x n = F.mk_e_app (F.term_of_lid [ fn ]) [ mk_nat x n ] in
    match e with
    | Int { value; kind = { size = SSize; signedness = sn }; negative = n } ->
        wrap_app (match sn with Signed -> "isz" | Unsigned -> "sz") value n
    | Int { value; kind = { size = S128; signedness = sn }; negative } ->
        let prefix = match sn with Signed -> "i" | Unsigned -> "u" in
        wrap_app ("pub_" ^ prefix ^ "128") value negative
    | _ -> mk_const @@ pliteral span e

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

  let plocal_ident (e : Local_ident.t) =
    (* let name = U.Concrete_ident_view.local_ident e.name in *)
    F.id
    @@ U.Concrete_ident_view.local_ident
         (match String.chop_prefix ~prefix:"impl " e.name with
         | Some name ->
             let name = "impl_" ^ Int.to_string ([%hash: string] name) in
             { e with name }
         | _ -> e)

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
      (c Core__ops__arith__Add__add, (2, "+!"));
      (c Core__ops__arith__Sub__sub, (2, "-!"));
      (c Core__ops__arith__Mul__mul, (2, "*!"));
      (c Core__ops__arith__Div__div, (2, "/!"));
      (c Core__ops__arith__Rem__rem, (2, "%!"));
      (c Core__ops__bit__Shl__shl, (2, "<<!"));
      (c Core__ops__bit__Shr__shr, (2, ">>!"));
      (c Core__cmp__PartialEq__eq, (2, "=."));
      (c Core__cmp__PartialOrd__lt, (2, "<."));
      (c Core__cmp__PartialOrd__le, (2, "<=."));
      (c Core__cmp__PartialEq__ne, (2, "<>."));
      (c Core__cmp__PartialOrd__ge, (2, ">=."));
      (c Core__cmp__PartialOrd__gt, (2, ">."));
      (`Primitive (LogicalOp And), (2, "&&"));
      (`Primitive (LogicalOp Or), (2, "||"));
    ]
    |> Map.of_alist_exn (module Global_ident)

  let rec pty span (t : ty) =
    match t with
    | TBool -> F.term_of_lid [ "bool" ]
    | TChar -> F.term_of_lid [ "char" ]
    | TInt k -> F.term_of_lid [ show_int_kind k ]
    | TStr -> F.term_of_lid [ "string" ]
    | TSlice { ty; _ } ->
        F.mk_e_app (F.term_of_lid [ "t_Slice" ]) [ pty span ty ]
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
        F.mk_e_app (F.term_of_lid [ "t_Array" ]) [ pty span typ; pexpr length ]
    | TParam i -> F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident i)
    | TAssociatedType { impl; item } -> (
        match pimpl_expr span impl with
        | Some impl ->
            F.term
            @@ F.AST.Project
                 (impl, F.lid [ U.Concrete_ident_view.to_definition_name item ])
        | None -> F.term @@ F.AST.Wild)
    | TOpaque s -> F.term @@ F.AST.Wild
    | _ -> .

  and pimpl_expr span (ie : impl_expr) =
    let some = Option.some in
    let hax_unstable_impl_exprs = false in
    match ie with
    | Concrete tr -> c_trait_ref span tr |> some
    | LocalBound { id } ->
        let local_ident =
          Local_ident.{ name = id; id = Local_ident.mk_id Expr 0 }
        in
        F.term @@ F.AST.Var (F.lid_of_id @@ plocal_ident local_ident) |> some
    | ImplApp { impl; _ } when not hax_unstable_impl_exprs ->
        pimpl_expr span impl
    | Parent { impl; trait } when hax_unstable_impl_exprs ->
        let* impl = pimpl_expr span impl in
        let trait = "_super_" ^ name_of_trait_ref span trait in
        F.term @@ F.AST.Project (impl, F.lid [ trait ]) |> some
    | ImplApp { impl; args = [] } when hax_unstable_impl_exprs ->
        pimpl_expr span impl
    | ImplApp { impl; args } when hax_unstable_impl_exprs ->
        let* impl = pimpl_expr span impl in
        let* args = List.map ~f:(pimpl_expr span) args |> Option.all in
        F.mk_e_app impl args |> some
    | Projection _ when hax_unstable_impl_exprs ->
        F.term_of_lid [ "_Projection" ] |> some
    | Dyn _ when hax_unstable_impl_exprs -> F.term_of_lid [ "_Dyn" ] |> some
    | Builtin _ when hax_unstable_impl_exprs ->
        F.term_of_lid [ "_Builtin" ] |> some
    | _ -> None

  and name_of_trait_ref _span : trait_ref -> string =
    [%hash: trait_ref] >> Int.to_string

  and c_trait_ref span trait_ref =
    let trait = F.term @@ F.AST.Name (pconcrete_ident trait_ref.trait) in
    List.map ~f:(pgeneric_value span) trait_ref.args |> F.mk_e_app trait

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
    | POr { subpats } ->
        Error.unimplemented p.span ~details:"ppat:Disjuntive patterns"
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
          F.pat_app pat_name
          @@
          if is_record then [ pat_rec () ]
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
    | App { f; args; generic_args } ->
        let const_generics =
          List.filter_map
            ~f:(function GConst e -> Some e | _ -> None)
            generic_args
        in
        let args = const_generics @ args in
        F.mk_e_app (pexpr f) @@ List.map ~f:pexpr args
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
               [
                 ( Some
                     [ F.term @@ F.AST.Var FStar_Parser_Const.inline_let_attr ],
                   (pat, body) );
               ],
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
        let arms =
          List.filter ~f:(fun arm -> is_never_to_any arm.arm.body |> not) arms
        in
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
        let params =
          List.mapi
            ~f:(fun i p ->
              match p.p with
              | PBinding { var; subpat = None; _ } -> (var, p)
              | _ ->
                  ( Local_ident.
                      { name = "temp_" ^ Int.to_string i; id = mk_id Expr (-1) },
                    p ))
            params
        in
        let body =
          let f (lid, (pat : pat)) =
            let rhs = { e = LocalVar lid; span = pat.span; typ = pat.typ } in
            U.make_let pat rhs
          in
          List.fold_right ~init:body ~f params
        in
        let mk_pat ((lid, pat) : local_ident * pat) =
          ppat (U.make_var_pat lid pat.typ pat.span)
        in
        F.mk_e_abs (List.map ~f:mk_pat params) (pexpr body)
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
    let mk ~aqual (ident : local_ident) ty =
      let v = F.pat @@ F.AST.PatVar (plocal_ident ident, aqual, []) in
      F.pat @@ F.AST.PatAscribed (v, (ty, None))
    in
    let ident = p.ident in
    match p.kind with
    | GPLifetime _ -> Error.assertion_failure span "pgeneric_param:LIFETIME"
    | GPType { default = None } ->
        mk ~aqual:(Some F.AST.Implicit) ident
          (F.term @@ F.AST.Name (F.lid [ "Type" ]))
    | GPType _ ->
        Error.unimplemented span ~details:"pgeneric_param:Type with default"
    | GPConst { typ } -> mk ~aqual:None ident (pty span typ)

  let rec pgeneric_constraint span (nth : int) (c : generic_constraint) =
    match c with
    | GCLifetime _ -> .
    | GCType { bound; id; _ } ->
        let tc = c_trait_ref span bound in
        F.pat
        @@ F.AST.PatAscribed (F.pat_var_tcresolve @@ Some ("i" ^ id), (tc, None))

  let rec pgeneric_param_bd
      ?(aqual : F.AST.arg_qualifier option = Some FStar_Parser_AST.Implicit)
      span (p : generic_param) =
    let ident = p.ident in
    match p.kind with
    | GPLifetime _ -> .
    | GPType { default = _ } ->
        let t = F.term @@ F.AST.Name (F.lid [ "Type" ]) in
        F.mk_binder ~aqual (F.AST.Annotated (plocal_ident ident, t))
    | GPType _ ->
        Error.unimplemented span ~details:"pgeneric_param_bd:Type with default"
    | GPConst { typ } ->
        F.mk_binder ~aqual:None
          (F.AST.Annotated (plocal_ident ident, pty span typ))

  let pgeneric_param_ident
      ?(aqual : F.AST.arg_qualifier option = Some FStar_Parser_AST.Implicit)
      span (p : generic_param) =
    match (pgeneric_param_bd ~aqual span p).b with
    | Annotated (ident, _) -> ident
    | _ -> failwith "pgeneric_param_ident"

  let rec pgeneric_constraint_type span (c : generic_constraint) =
    match c with
    | GCLifetime _ ->
        Error.assertion_failure span "pgeneric_constraint_bd:LIFETIME"
    | GCType { bound; _ } -> c_trait_ref span bound

  let rec pgeneric_constraint_bd span (c : generic_constraint) =
    let tc = pgeneric_constraint_type span c in
    F.AST.
      {
        b = F.AST.Annotated (F.generate_fresh_ident (), tc);
        brange = F.dummyRange;
        blevel = Un;
        aqual = Some TypeClassArg;
        battributes = [];
      }

  let pgenerics
      ?(aqual : F.AST.arg_qualifier option = Some FStar_Parser_AST.Implicit)
      span generics =
    List.map ~f:(pgeneric_param_bd ~aqual span) generics.params
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
                 (List.map ~f:Local_ident.make_final free_variables)
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
    match Attrs.associated_refinement_in_type free_variables attrs with
    | Some refinement ->
        F.mk_refined binder_name (pty span ty) (fun ~x -> pexpr refinement)
    | None -> pty span ty

  (* let prefined_ty span (binder : string) (ty : ty) (refinement : expr) : *)
  (*     F.AST.term = *)
  (*   F.mk_refined binder (pty span ty) (pexpr refinement) *)

  let is_scalar (ty : ty) =
    match ty with TBool | TChar | TInt _ | TFloat _ -> true | _ -> false

  let add_clauses_effect_type (scalar_inputs : bool) scalar_output
      (attrs : attrs) typ : F.AST.typ * bool =
    let attr_term ?keep_last_args kind f =
      Attrs.associated_expr ?keep_last_args kind attrs
      |> Option.map ~f:(pexpr >> f >> F.term)
    in
    let decreases = attr_term Decreases (fun t -> F.AST.Decreases (t, None)) in
    let is_lemma = Attrs.lemma attrs in
    let prepost_bundle =
      let trivial_pre = F.term_of_lid [ "Prims"; "l_True" ] in
      let trivial_post =
        if is_lemma then trivial_pre
        else
          let wild = F.pat @@ F.AST.PatWild (None, []) in
          F.mk_e_abs [ wild; wild; wild ] trivial_pre
      in
      let pre = attr_term Requires (fun t -> F.AST.Requires (t, None)) in
      let post =
        let keep_last_args = if is_lemma then 0 else 1 in
        attr_term ~keep_last_args Ensures (fun t -> F.AST.Ensures (t, None))
      in
      if is_lemma || Option.is_some pre || Option.is_some post then
        Some
          ( Option.value ~default:trivial_pre pre,
            Option.value ~default:trivial_post post )
      else None
    in
    let args =
      (Option.map ~f:(fun (req, ens) -> [ req; ens ]) prepost_bundle
      |> Option.value ~default:[])
      @ Option.to_list decreases
    in
    let mk namespace effect = F.term_of_lid (namespace @ [ effect ]) in
    let prims = mk [ "Prims" ] in
    let st = mk [ "FStar"; "HyperStack"; "ST" ] "St" in
    let stack_inline = mk [ "FStar"; "HyperStack"; "ST" ] "StackInline" in
    if is_lemma then
      (F.mk_e_app (prims "Tot") (if is_lemma then args else [ typ ]), false)
    else
      match (scalar_inputs, scalar_output) with
      | true, true -> (typ, false)
      | _, true -> (F.mk_e_app st [ typ ], false)
      | _, _ ->
          ( F.mk_e_app stack_inline
              [
                typ;
                F.term_of_string "(fun _ -> True)";
                F.term_of_string "(fun _ _ _ -> True)";
              ],
            true )
  (* if scalar_output && scalar_inputs then typ *)
  (* else *)
  (*   match args with *)
  (*   (\* | _ -> typ *\) *)
  (*   | _ -> *)
  (*       F.mk_e_app effect (if is_lemma then args else [ typ ]) *)

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
        let pat_args =
          List.map ~f:(pgeneric_param e.span) generics.params
          @ List.mapi ~f:(pgeneric_constraint e.span) generics.constraints
          @ List.map
              ~f:(fun { pat; typ_span; typ } ->
                let span = Option.value ~default:e.span typ_span in
                F.pat @@ F.AST.PatAscribed (ppat pat, (pty span typ, None)))
              params
        in
        let pat = F.pat @@ F.AST.PatApp (pat, pat_args) in
        let scalar_inputs =
          List.for_all ~f:(fun { typ; _ } -> is_scalar typ) params
        in
        let scalar_output = is_scalar body.typ in
        let ty, inline_for_extraction =
          match params with
          | [] -> (pty body.span body.typ, false)
          | _ ->
              add_clauses_effect_type scalar_inputs scalar_output e.attrs
                (pty body.span body.typ)
        in
        let inline_for_extraction =
          inline_for_extraction
          || List.exists
               ~f:
                 [%matches?
                   { kind = Tool { path = "inline"; tokens = "always" } }]
               e.attrs
        in
        let quals =
          if inline_for_extraction then [ F.AST.Inline_for_extraction ] else []
        in
        let pat = F.pat @@ F.AST.PatAscribed (pat, (ty, None)) in
        let body = pexpr body in
        let body =
          if List.is_empty params then
            let normalize_term =
              F.term_of_lid [ "FStar"; "Pervasives"; "normalize_term" ]
            in

            F.mk_e_app normalize_term [ body ]
          else body
        in
        F.decls ~quals @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, body) ])
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
                     pgenerics ~aqual:None e.span generics,
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
        F.decls ~quals:[ Noeq ]
        @@ F.AST.Tycon
             ( false,
               false,
               [
                 F.AST.TyconVariant
                   ( F.id @@ U.Concrete_ident_view.to_definition_name name,
                     pgenerics ~aqual:None e.span generics,
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
        let bds =
          List.map ~f:(pgeneric_param_bd ~aqual:None e.span) generics.params
        in
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
                | TIFn ty ->
                    let ty = pty e.span ty in
                    let ty =
                      F.term
                      @@ F.AST.Product (pgenerics i.ti_span i.ti_generics, ty)
                    in
                    [ (F.id name, None, [], ty) ]
              in
              List.map ~f:Fn.id
                (* ~f:(fun (n, q, a, ty) -> (n, q, a, F.mk_e_app bds ty)) *)
                fields)
            items
        in
        let constraints_fields : FStar_Parser_AST.tycon_record =
          generics.constraints
          |> List.map ~f:(fun c ->
                 let bound =
                   match c with GCType { bound; _ } -> bound | _ -> .
                 in
                 let name = "_super_" ^ name_of_trait_ref e.span bound in
                 let typ = pgeneric_constraint_type e.span c in
                 (F.id name, None, [ F.Attrs.no_method ], typ))
        in
        let fields : FStar_Parser_AST.tycon_record =
          constraints_fields @ fields
        in
        let fields : FStar_Parser_AST.tycon_record =
          if List.is_empty fields then
            let marker_field = "__marker_trait_" ^ name_str in
            [ (F.id marker_field, None, [], pty e.span U.unit_typ) ]
          else fields
        in
        let tcdef = F.AST.TyconRecord (name, bds, None, [], fields) in
        let d = F.AST.Tycon (false, true, [ tcdef ]) in
        [ `Item { d; drange = F.dummyRange; quals = []; attrs = [] } ]
    | Impl { generics; self_ty = _; of_trait = trait, generic_args; items } ->
        let pat =
          let name = U.Concrete_ident_view.to_definition_name e.ident in
          F.pat @@ F.AST.PatVar (F.id name, None, [])
        in
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
                      List.map ~f:(pgeneric_param ii_span) ii_generics.params
                      @ List.mapi
                          ~f:(pgeneric_constraint ii_span)
                          ii_generics.constraints
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
        let tcinst = F.term @@ F.AST.Var FStar_Parser_Const.tcinstance_lid in
        F.decls ~quals:[ F.AST.Inline_for_extraction ] ~attrs:[ tcinst ]
        @@ F.AST.TopLevelLet (NoLetQualifier, [ (pat, body) ])
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

let make (module M : Attrs.WITH_ITEMS) ctx =
  (module Make
            (M)
            (struct
              let ctx = ctx
            end) : S)

let string_of_item m items (item : item) : string =
  let (module Print) =
    make m
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

let string_of_items m items =
  List.map ~f:(string_of_item m items) items
  |> List.map ~f:String.strip
  |> List.filter ~f:(String.is_empty >> not)
  |> String.concat ~sep:"\n\n"

let fstar_headers (bo : BackendOptions.t) =
  let opts =
    Printf.sprintf {|#set-options "--fuel %Ld --ifuel %Ld --z3rlimit %Ld"|}
      bo.fuel bo.ifuel bo.z3rlimit
  in
  [ opts; "open Core"; "open FStar.Mul" ] |> String.concat ~sep:"\n"

let translate m (bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  let show_view Concrete_ident.{ crate; path; definition } =
    crate :: (path @ [ definition ]) |> String.concat ~sep:"::"
  in
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
               "module " ^ mod_name ^ "\n" ^ fstar_headers bo ^ "\n\n"
               ^ string_of_items m items ^ "\n";
           })

open Phase_utils
module DepGraph = Dependencies.Make (InputLanguage)
module DepGraphR = Dependencies.Make (Features.Rust)

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.RawOrMutPointer(Features.Rust)
  (* |> Phases.And_mut_defsite *)
  |> Phases.Reconstruct_for_loops
  |> Phases.Reconstruct_for_index_loops
  (* |> Phases.Direct_and_mut *)
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
