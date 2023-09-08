open! Prelude
open Ast
open Ast.Full

module Concrete_ident_view = Concrete_ident.MakeViewAPI (struct
  include Concrete_ident.DefaultNamePolicy

  let index_field_transform field = "_" ^ field
end)

module AnnotatedString = struct
  module T = struct
    type t = (span * string) list [@@deriving show]

    let empty : t = []
    let append : t -> t -> t = List.append

    let concat ?(sep : t option) (l : t list) : t =
      List.concat
      @@ match sep with None -> l | Some (sep : t) -> List.intersperse ~sep l

    let pure : span -> string -> t = fun meta s -> [ (meta, s) ]
    let ( & ) = append
    let to_string = List.map ~f:snd >> String.concat ~sep:""
    let split_re = Re.Pcre.regexp "[\t\n ]+|[^A-Za-z0-9_]"

    let split =
      let open Re.Pcre in
      full_split ~rex:split_re
      >> List.concat_map ~f:(function
           | (Text s | Delim s | Group (_, s)) when not (String.is_empty s) ->
               [ s ]
           | _ -> [])

    let tokenize : t -> t =
      List.concat_map ~f:(fun (span, s) -> split s |> List.map ~f:(tup2 span))
  end

  include T

  module Output = struct
    type t = { string : string; map : (int * int * string) list }
    [@@deriving show, yojson]

    let convert (v : T.t) : t =
      (* let annotations, map = *)
      let map =
        List.map v ~f:(fun (span, s) -> (String.length s, Span.id_of span, s))
      in
      (*   List.fold v ~init:([], []) ~f:(fun (annotations, acc) (span, s) -> *)
      (*       let len = String.length s in *)
      (*       let i, annotations = *)
      (*         match List.findi ~f:(Fn.const @@ equal_span span) annotations with *)
      (*         | Some (i, _) -> (i, annotations) *)
      (*         | None -> (List.length annotations, annotations @ [ span ]) *)
      (*       in *)
      (*       (annotations, (len, i) :: acc)) *)
      (* in *)
      { map; string = T.to_string v }

    let raw_string : t -> string = fun { string; _ } -> string
  end
end

let re_matches rex (s : string) : bool =
  try Re.Pcre.pmatch ~rex s with _ -> false

module Raw = struct
  open AnnotatedString

  let pliteral span (e : literal) : AnnotatedString.t =
    pure span
    @@
    match e with
    | String s -> "\"" ^ String.escaped s ^ "\""
    | Char c -> "'" ^ Char.to_string c ^ "'"
    | Int { value; _ } -> value
    | Float { value; kind = F32 } -> value ^ "f32"
    | Float { value; kind = F64 } -> value ^ "f64"
    | Bool b -> Bool.to_string b

  let pprimitive_ident span : _ -> AnnotatedString.t =
    pure span << function
    | Deref -> "deref"
    | Cast -> "cast"
    | LogicalOp op -> "BinOp::" ^ [%show: logical_op] op

  let rec pglobal_ident' prefix span (e : global_ident) : AnnotatedString.t =
    let ( ! ) s = pure span (prefix ^ s) in
    match e with
    | `Concrete c -> !(Concrete_ident_view.show c)
    | `Primitive p -> pprimitive_ident span p
    | `TupleType n -> ![%string "tuple%{Int.to_string n}"]
    | `TupleCons n -> ![%string "Tuple%{Int.to_string n}"]
    | `TupleField (n, _) -> ![%string "proj_tuple%{Int.to_string n}"]
    | `Projector o -> pglobal_ident' "proj_" span (o :> global_ident)

  let pglobal_ident = pglobal_ident' ""

  let plocal_ident span (e : LocalIdent.t) : AnnotatedString.t =
    pure span e.name

  let dmutability span : _ -> AnnotatedString.t =
    pure span << function Mutable _ -> "mut " | _ -> ""

  let dbinding_mode span =
    pure span << function ByValue -> "" | ByRef _ -> "&"

  let pborrow_kind span = pure span << function Mut _ -> "mut " | _ -> ""

  let last_of_global_ident (g : global_ident) span =
    match g with
    | `Concrete c -> Concrete_ident_view.to_definition_name c
    | _ ->
        Diagnostics.report
          {
            context = DebugPrintRust;
            kind =
              AssertionFailure
                {
                  details =
                    "[last_of_global_ident] was given a non-concrete global \
                     ident";
                };
            span = Span.to_thir span;
          };
        "print_rust_last_of_global_ident_error"

  let rec pty span (e : ty) =
    let ( ! ) = pure span in
    match e with
    | TBool -> !"bool"
    | TChar -> !"char"
    | TInt _k -> !"int"
    | TFloat _k -> !"float"
    | TStr -> !"String"
    | TApp { ident; args = [] } -> pglobal_ident span ident
    | TApp { ident; args } ->
        let args : AnnotatedString.t =
          List.map ~f:(pgeneric_value span) args |> concat ~sep:!", "
        in
        pglobal_ident span ident & !"<" & args & !">"
    | TArray { typ; length } -> !"[" & pty span typ & !";" & pexpr length & !"]"
    | TSlice { ty; _ } -> !"[" & pty span ty & !"]"
    | TRawPointer _ -> !"raw_pointer!()"
    | TRef { typ; mut; _ } -> !"&" & dmutability span mut & pty span typ
    | TParam i -> plocal_ident span i
    | TArrow (inputs, output) ->
        let arrow =
          List.map ~f:(pty span) (inputs @ [ output ]) |> concat ~sep:!" -> "
        in
        !"arrow!(" & arrow & !")"
    | TProjectedAssociatedType _ -> !"proj_asso_type!()"

  and pgeneric_value span (e : generic_value) : AnnotatedString.t =
    match e with
    | GLifetime _ -> pure span "lifetime!(something)"
    | GType t -> pty span t
    | _ -> pure span "generic_value!(todo)"

  and ppat (e : pat) =
    let ( ! ) = pure e.span in
    match e.p with
    | PWild -> !"_"
    | PAscription { typ; pat; _ } ->
        !"pat_ascription!(" & ppat pat & !" as " & pty e.span typ & !")"
    | PConstruct { name; args; is_record; _ } ->
        pglobal_ident e.span name
        &
        if List.is_empty args then !""
        else if is_record then
          !"{"
          & concat ~sep:!", "
              (List.map
                 ~f:(fun { field; pat } ->
                   !(last_of_global_ident field e.span) & !":" & ppat pat)
                 args)
          & !"}"
        else
          !"("
          & concat ~sep:!", " (List.map ~f:(fun { pat; _ } -> ppat pat) args)
          & !")"
    | PArray { args } -> !"[" & concat ~sep:!"," (List.map ~f:ppat args) & !"]"
    | PDeref { subpat; _ } -> !"&" & ppat subpat
    | PConstant { lit } -> pliteral e.span lit
    | PBinding { mut; mode; var; typ = _; subpat } ->
        let subpat =
          match subpat with Some (p, _) -> !" @ " & ppat p | None -> !""
        in
        dbinding_mode e.span mode & dmutability e.span mut
        & plocal_ident e.span var & subpat

  and psupported_monads span m =
    let ( ! ) = pure span in
    match m with
    | MException t -> !"MException<" & pty span t & !">"
    | MResult t -> !"MResult<" & pty span t & !">"
    | MOption -> !"MOption"

  and pexpr' (e : expr) =
    let ( ! ) = pure e.span in
    match e.e with
    | If { cond; then_; else_ } ->
        let else_ =
          match else_ with Some e -> !" else {" & pexpr e & !"}" | None -> !""
        in
        !"(" & !"if " & pexpr cond & !"{" & pexpr then_ & !"}" & else_ & !")"
    | App { f = { e = GlobalVar _; _ } as f; args } ->
        let args = concat ~sep:!"," @@ List.map ~f:pexpr args in
        pexpr f & !"(" & args & !")"
    | App { f; args } ->
        let args = concat ~sep:!"," @@ List.map ~f:pexpr args in
        pexpr f & !"(" & args & !")"
    | Literal l -> pliteral e.span l
    | Block (e, _) -> !"{" & pexpr e & !"}"
    | Array l -> !"[" & concat ~sep:!"," (List.map ~f:pexpr l) & !"]"
    | Construct { is_record = false; constructor; fields; _ } ->
        let fields = List.map ~f:(snd >> pexpr) fields |> concat ~sep:!"," in
        pglobal_ident e.span constructor & !"(" & fields & !")"
    | Construct { is_record = true; constructor; fields; base; _ } ->
        let fields =
          List.map
            ~f:(fun (field, value) ->
              !(last_of_global_ident field e.span) & !":" & pexpr value)
            fields
          |> concat ~sep:!","
        in
        let base =
          match base with
          | Some (base, _) -> !"..(" & pexpr base & !")"
          | _ -> !""
        in
        pglobal_ident e.span constructor & !"{" & fields & !"," & base & !"}"
    | Match { scrutinee; arms } ->
        let arms =
          List.map
            ~f:(fun { arm = { arm_pat; body }; _ } ->
              ppat arm_pat & !" => {" & pexpr body & !"}")
            arms
          |> concat ~sep:!","
        in
        !"(match " & pexpr scrutinee & !" {" & arms & !"})"
    (* | Let { monadic = Some _; _ } -> !"monadic_let!()" *)
    | Let { monadic; lhs; rhs; body } ->
        (* TODO: here, [rhs.typ]! *)
        let lhs_typ = pty lhs.span lhs.typ in
        let rhs_typ = pty rhs.span rhs.typ in
        let note =
          if String.equal (to_string lhs_typ) (to_string rhs_typ) then !""
          else !"// Note: rhs.typ=" & rhs_typ & !"\n"
        in
        let monadic =
          match monadic with
          | Some (m, _) ->
              !"#[monadic_let(" & psupported_monads e.span m & !")]"
          | _ -> !""
        in
        note & monadic & !"let " & ppat lhs & !": " & lhs_typ & !" = {"
        & pexpr rhs & !"};" & pexpr body
    | LocalVar local_ident -> plocal_ident e.span local_ident
    | GlobalVar global_ident -> pglobal_ident e.span global_ident
    | Ascription { e = e'; typ } ->
        !"(" & pexpr e' & !" as " & pty e.span typ & !")"
    | MacroInvokation { macro; args; _ } ->
        pglobal_ident e.span macro & !"!(" & !args & !")"
    | Assign { lhs; e; _ } -> !"(" & plhs lhs e.span & !" = " & pexpr e & !")"
    | Loop { body; kind; state; _ } -> (
        let header =
          match kind with
          | UnconditionalLoop -> !"loop"
          | ForLoop { it; pat; _ } ->
              !"for " & ppat pat & !" in (" & pexpr it & !")"
          | ForIndexLoop { start; end_; var; _ } ->
              !"for " & plocal_ident e.span var & !" in (" & pexpr start
              & !")..(" & pexpr end_ & !")"
        in
        let body_wrapper body =
          match state with
          | Some { bpat; _ } -> !"|" & ppat bpat & !"| {" & body & !"}"
          | None -> body
        in
        let main = header & !" { " & body_wrapper (pexpr body) & !" }" in
        match state with
        | Some { init; _ } -> !"(" & main & !")(" & pexpr init & !")"
        | None -> main)
    | Break { e; _ } -> !"(break (" & pexpr e & !"))"
    | Continue { e = None; _ } -> !"continue"
    | Continue { e = Some (_, e); _ } ->
        !"state_passing_continue!(" & pexpr e & !")"
    | Return { e; _ } -> !"(return " & pexpr e & !")"
    | QuestionMark { e; _ } -> !"(" & pexpr e & !")?"
    | Borrow { kind; e; _ } ->
        !"&" & pborrow_kind e.span kind & !"(" & pexpr e & !")"
    | AddressOf _ -> !"address_of"
    | EffectAction _ -> !"EffectAction"
    | Closure { params; body; _ } ->
        let params = List.map ~f:ppat params |> concat ~sep:!"," in
        !"(|" & params & !"| {" & pexpr body & !"})"
  (* | _ -> "todo!()" *)

  and plhs (e : lhs) span =
    let ( ! ) = pure span in
    match e with
    | LhsFieldAccessor { e; field; _ } ->
        let field =
          match field with
          | `Projector field -> (field :> global_ident)
          | _ -> field
        in
        plhs e span & !"." & !(last_of_global_ident field span)
    | LhsArrayAccessor { e; index; _ } ->
        plhs e span & !"[" & pexpr index & !"]"
    | LhsLocalVar { var; _ } -> plocal_ident span var
    | LhsArbitraryExpr { e; _ } -> pexpr e

  and pexpr (e : expr) =
    let ( ! ) = pure e.span in
    let need_braces = [%matches? Let _ | Loop _] e.e in
    let e = pexpr' e in
    if need_braces then !"{" & e & !"}" else e

  let pattr (attr : attr) =
    let ( ! ) = pure attr.span in
    match attr.kind with
    | Tool { path; tokens } -> !"#[" & !path & !"(" & !tokens & !")" & !"]"
    | DocComment { kind = _; body } -> !"/**" & !body & !"*/"

  let pattrs attrs = List.map ~f:pattr attrs |> concat

  let pgeneric_param_kind span (pk : generic_param_kind) =
    let ( ! ) = pure span in
    match pk with
    | GPLifetime _ -> (empty, !": 'unk")
    | GPType { default = Some default } -> (empty, !" = " & pty span default)
    | GPType { default = None } -> (empty, empty)
    | GPConst { typ } -> (!"const ", !":" & pty span typ)

  let pgeneric_param (p : generic_param) =
    let prefix, suffix = pgeneric_param_kind p.span p.kind in
    let id =
      plocal_ident p.span
        (if String.equal p.ident.name "_" then
         { p.ident with name = "Anonymous" }
        else p.ident)
    in
    pattrs p.attrs & prefix & id & suffix

  let pgeneric_params (pl : generic_param list) =
    match pl with
    | { span; _ } :: _ ->
        let ( ! ) = pure span in
        !"<" & concat ~sep:!", " (List.map ~f:pgeneric_param pl) & !">"
    | _ -> empty

  let ptrait_ref span { trait; args; bindings = _ } =
    let ( ! ) = pure span in
    let args = List.map ~f:(pgeneric_value span) args |> concat ~sep:!", " in
    !(Concrete_ident_view.show trait)
    & if List.is_empty args then empty else !"<" & args & !">"

  let pgeneric_constraint span (p : generic_constraint) =
    let ( ! ) = pure span in
    match p with
    | GCLifetime _ -> !"'unk: 'unk"
    | GCType { typ; implements } ->
        pty span typ & !":" & ptrait_ref span implements

  let pgeneric_constraints span (constraints : generic_constraint list) =
    if List.is_empty constraints then empty
    else
      let ( ! ) = pure span in
      !" where "
      & concat ~sep:!"," (List.map ~f:(pgeneric_constraint span) constraints)

  let pvariant_body span { name = _; arguments; attrs = _; is_record } =
    let ( ! ) = pure span in
    if is_record then
      !"{"
      & concat ~sep:!","
          (List.map arguments ~f:(fun (id, ty, attrs) ->
               pattrs attrs
               & !(Concrete_ident_view.to_definition_name id)
               & !":" & pty span ty))
      & !"}"
    else
      !"("
      & concat ~sep:!","
          (List.map arguments ~f:(fun (_, ty, attrs) ->
               pattrs attrs & pty span ty))
      & !")"

  let pvariant span (variant : variant) =
    let ( ! ) = pure span in
    pattrs variant.attrs
    & !(Concrete_ident_view.to_definition_name variant.name)
    & pvariant_body span variant

  let pvariants span variants =
    let ( ! ) = pure span in
    concat ~sep:!", " (List.map ~f:(pvariant span) variants)

  let pitem (e : item) =
    let exception NotImplemented in
    let ( ! ) = pure e.span in
    try
      let pi =
        match e.v with
        | Fn { name; body; generics; params } ->
            let return_type = pty e.span body.typ in
            let params =
              List.map
                ~f:(fun { pat; typ; typ_span; attrs } ->
                  pattrs attrs & ppat pat & !": "
                  & pty (Option.value ~default:pat.span typ_span) typ)
                params
              |> concat ~sep:!","
            in
            !"fn "
            & !(Concrete_ident_view.to_definition_name name)
            & pgeneric_params generics.params
            & !"(" & params & !") -> " & return_type
            & pgeneric_constraints e.span generics.constraints
            & !"{" & pexpr body & !"}"
        | TyAlias { name; generics; ty } ->
            !"type "
            & !(Concrete_ident_view.to_definition_name name)
            & pgeneric_params generics.params
            & pgeneric_constraints e.span generics.constraints
            & !"=" & pty e.span ty & !";"
        | Type { name; generics; variants = [ variant ]; is_struct = true } ->
            !"struct "
            & !(Concrete_ident_view.to_definition_name name)
            & pgeneric_params generics.params
            & pgeneric_constraints e.span generics.constraints
            & pvariant_body e.span variant
            & if variant.is_record then !"" else !";"
        | Type { name; generics; variants; _ } ->
            !"enum "
            & !(Concrete_ident_view.to_definition_name name)
            & pgeneric_params generics.params
            & pgeneric_constraints e.span generics.constraints
            &
            if List.is_empty variants then empty
            else !"{" & pvariants e.span variants & !"}"
        | _ -> raise NotImplemented
      in
      pattrs e.attrs & pi
    with NotImplemented -> !"/* print_rust: pitem: not implemented */"
end

let rustfmt (s : string) : string =
  let open Utils.Command in
  let { stderr; stdout } = run "rustfmt" s in
  if String.is_empty stderr then stdout
  else
    let err =
      [%string
        "\n\n\
         #######################################################\n\
         ########### WARNING: Failed running rustfmt ###########\n\
         #### STDOUT:\n\
         %{stdout}\n\
         #### STDERR:\n\
         %{stderr}\n\
         #######################################################\n"]
    in
    Stdio.prerr_endline err;
    [%string "/*\n%{err}\n*/\n\n%{s}"]

let rustfmt_annotated' (x : AnnotatedString.t) : AnnotatedString.t =
  let original = AnnotatedString.tokenize x in
  let tokens = AnnotatedString.(to_string x |> rustfmt |> split) in
  let is_symbol = re_matches AnnotatedString.split_re in
  let all_symbol = List.for_all ~f:(snd >> is_symbol) in
  let f (original, result) s =
    let last =
      List.hd result |> Option.map ~f:fst
      |> Option.value_or_thunk ~default:Span.dummy
    in
    let original', tuple =
      match List.split_while ~f:(snd >> String.equal s >> not) original with
      | prev, (span, s') :: original' ->
          assert (String.equal s s');
          if all_symbol prev then
            (* it is fine to skip symbols *)
            (original', (span, s))
          else if is_symbol s then
            (* if [s] is a symbol as well, this is fine *)
            (original, (Span.dummy (), s))
          else (
            Stdio.prerr_endline @@ "\n##### RUSTFMT TOKEN ERROR #####";
            Stdio.prerr_endline @@ "prev=" ^ [%show: AnnotatedString.t] prev;
            Stdio.prerr_endline @@ "s=" ^ s;
            failwith "rustfmt retokenization")
      | _ -> (original, (last, s))
    in
    (original', tuple :: result)
  in
  let r = snd @@ List.fold_left tokens ~init:(original, []) ~f in
  List.rev r

let rustfmt_annotated (x : AnnotatedString.t) : AnnotatedString.t =
  let rf = Option.value ~default:"" (Sys.getenv "HAX_RUSTFMT") in
  if String.equal rf "no" then x else rustfmt_annotated' x

let pitem : item -> AnnotatedString.Output.t =
  Raw.pitem >> rustfmt_annotated >> AnnotatedString.Output.convert

let pitems : item list -> AnnotatedString.Output.t =
  List.concat_map ~f:Raw.pitem
  >> rustfmt_annotated >> AnnotatedString.Output.convert

let pitem_str : item -> string = pitem >> AnnotatedString.Output.raw_string

let pexpr_str (e : expr) : string =
  let e = Raw.pexpr e in
  let ( ! ) = AnnotatedString.pure @@ Span.dummy () in
  let ( & ) = AnnotatedString.( & ) in
  let prefix = "fn expr_wrapper() {" in
  let suffix = "}" in
  let item = !prefix & e & !suffix in
  rustfmt_annotated item |> AnnotatedString.Output.convert
  |> AnnotatedString.Output.raw_string |> Caml.String.trim
  |> String.chop_suffix_if_exists ~suffix
  |> String.chop_prefix_if_exists ~prefix
  |> Caml.String.trim
