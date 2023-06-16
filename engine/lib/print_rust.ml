open Base
open Ppx_yojson_conv_lib.Yojson_conv.Primitives
open Ast
open Ast.Full
open Utils

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
    let split_re = Re.Str.regexp "\\([\t\n ]+\\|[^A-Za-z0-9_]\\)"

    let split =
      let open Re.Str in
      full_split split_re >> List.map ~f:(function Text s | Delim s -> s)

    let tokenize : t -> t =
      List.concat_map
        ~f:(Fn.id *** split >> uncurry (fun span -> List.map ~f:(tup2 span)))
  end

  include T

  module Output = struct
    type t = { string : string; map : (int * int * string) list }
    [@@deriving show, yojson]

    let id_of_span = function Dummy { id } | Span { id; _ } -> id

    let convert (v : T.t) : t =
      (* let annotations, map = *)
      let map =
        List.map v ~f:(fun (span, s) -> (String.length s, id_of_span span, s))
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

let re_matches re (s : string) : bool =
  try
    let _ = Re.Str.search_forward re s 0 in
    true
  with _ -> false

module Raw = struct
  open AnnotatedString

  let pliteral span (e : literal) : AnnotatedString.t =
    pure span
    @@
    match e with
    | String s -> "\"" ^ s ^ "\""
    | Char c -> "'" ^ Char.to_string c ^ "'"
    | Int { value; _ } -> value
    | Float _ -> "float_todo"
    | Bool b -> Bool.to_string b

  let pprimitive_ident span : _ -> AnnotatedString.t =
    pure span << function
    | Box -> "Box::new"
    | Deref -> "deref"
    | Cast -> "cast"
    | BinOp op -> "BinOp::" ^ [%show: bin_op] op
    | UnOp op -> "BinOp::" ^ [%show: un_op] op
    | LogicalOp op -> "BinOp::" ^ [%show: logical_op] op

  let rec pglobal_ident' prefix span (e : global_ident) : AnnotatedString.t =
    let ( ! ) s = pure span (prefix ^ s) in
    match e with
    | `Concrete c ->
        let path, crate = Concrete_ident.(path c, crate c) in
        !(String.concat ~sep:"::" (crate :: Non_empty_list.to_list path))
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
    | `Concrete c -> Non_empty_list.last (Concrete_ident.path c)
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
            span = Diagnostics.to_thir_span span;
          };
        "print_rust_last_of_global_ident_error"

  let rec pty span (e : ty) =
    let ( ! ) = pure span in
    match e with
    | TBool -> !"bool"
    | TChar -> !"char"
    | TInt _k -> !"int"
    | TFloat -> !"float"
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
    | TFalse -> !"!"
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
    | PConstruct { name; args; record; _ } ->
        pglobal_ident e.span name
        &
        if List.is_empty args then !""
        else if record then
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
    | Array l -> !"[" & concat ~sep:!"," (List.map ~f:pexpr l) & !"]"
    | Construct { constructs_record = false; constructor; fields; base = _ } ->
        let fields = List.map ~f:(snd >> pexpr) fields |> concat ~sep:!"," in
        pglobal_ident e.span constructor & !"(" & fields & !")"
    | Construct { constructs_record = true; constructor; fields; base } ->
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

  let pitem (e : item) =
    let ( ! ) = pure e.span in
    match e.v with
    | Fn { name; body; generics = _todo; params } ->
        let return_type = pty e.span body.typ in
        let params =
          List.map
            ~f:(fun { pat; typ; typ_span } ->
              ppat pat & !": "
              & pty (Option.value ~default:pat.span typ_span) typ)
            params
          |> concat ~sep:!","
        in
        !"fn "
        & !(last_of_global_ident name e.span)
        & !"(" & params & !") -> " & return_type & !"{" & pexpr body & !"}"
    | _ -> !"/* TO DO */"
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
    Caml.prerr_endline err;
    [%string "/*\n%{err}\n*/\n\n%{s}"]

let rustfmt_annotated (x : AnnotatedString.t) : AnnotatedString.t =
  let x = AnnotatedString.tokenize x in
  let s = AnnotatedString.to_string x |> rustfmt |> AnnotatedString.split in
  let f (x, result) s =
    let last =
      let default = Dummy { id = -1 } in
      List.hd result |> Option.map ~f:fst |> Option.value ~default
    in
    let x, tuple =
      match List.split_while ~f:(snd >> String.equal s >> not) x with
      | prev, (span, s') :: x' ->
          let symbols_only =
            List.for_all prev ~f:(snd >> re_matches AnnotatedString.split_re)
          in
          if symbols_only then (x', (span, s))
          else
            let span, _ = List.hd_exn prev in
            (x, (span, s))
      | _ -> (x, (last, s))
    in
    (x, tuple :: result)
  in
  let r = snd @@ List.fold_left s ~init:(x, []) ~f in
  List.rev r

(* module U = Ast_utils.Make (Features.Full) *)

let pitem : item -> AnnotatedString.Output.t =
  (* U.Mappers.regenerate_span_ids#visit_item () *)
  Raw.pitem >> rustfmt_annotated >> AnnotatedString.Output.convert

let pitems : item list -> AnnotatedString.Output.t =
  List.concat_map ~f:Raw.pitem
  >> rustfmt_annotated >> AnnotatedString.Output.convert

let pitem_str : item -> string = pitem >> AnnotatedString.Output.raw_string

let pexpr_str (e : expr) : string =
  let e = Raw.pexpr e in
  let ( ! ) = AnnotatedString.pure (Dummy { id = 0 }) in
  let ( & ) = AnnotatedString.( & ) in
  let prefix = "fn expr_wrapper() {" in
  let suffix = "}" in
  let item = !prefix & e & !suffix in
  rustfmt_annotated item |> AnnotatedString.Output.convert
  |> AnnotatedString.Output.raw_string |> Caml.String.trim
  |> String.chop_suffix_if_exists ~suffix
  |> String.chop_prefix_if_exists ~prefix
  |> Caml.String.trim
