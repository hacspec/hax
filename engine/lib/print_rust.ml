open Base
open Ast
open Ast.Full
open Utils

module Raw = struct
  let pliteral (e : literal) =
    match e with
    | String s -> [%string "\"%{s}\""]
    | Char c -> [%string "'%{Char.to_string c}'"]
    | Int { value; _ } -> value
    | Float _ -> "float_todo"
    | Bool b -> Bool.to_string b

  let pprimitive_ident = function
    | Box -> "Box::new"
    | Deref -> "deref"
    | Cast -> "cast"
    | BinOp op -> [%string "BinOp::%{[%show: bin_op] op}"]
    | UnOp op -> [%string "BinOp::%{[%show: un_op] op}"]
    | LogicalOp op -> [%string "BinOp::%{[%show: logical_op] op}"]

  let pglobal_ident (e : global_ident) =
    match e with
    | `Concrete { crate; path } ->
        String.concat ~sep:"::" @@ (crate :: Non_empty_list.to_list path)
    | `Primitive p -> pprimitive_ident p
    | `TupleType n -> [%string "tuple%{Int.to_string n}"]
    | `TupleCons n -> [%string "Tuple%{Int.to_string n}"]
    | `TupleField (n, _) -> [%string "proj_tuple%{Int.to_string n}"]
    | `Projector _n -> show_global_ident e

  let plocal_ident (e : LocalIdent.t) = e.name
  let dmutability = function Mutable _ -> "mut " | _ -> ""
  let dbinding_mode = function ByValue -> "" | ByRef _ -> "&"

  let rec pty (e : ty) =
    match e with
    | TBool -> "bool"
    | TChar -> "char"
    | TInt _k -> "int"
    | TFloat -> "float"
    | TStr -> "String"
    | TApp { ident; args = [] } -> [%string "%{pglobal_ident ident}"]
    | TApp { ident; args } ->
        let args = List.map ~f:pgeneric_value args |> String.concat ~sep:", " in
        [%string "%{pglobal_ident ident}<%{args}>"]
    | TArray { typ; length } ->
        [%string "[%{pty typ}; %{Int.to_string length}]"]
    | TSlice { ty; _ } -> [%string "[%{pty ty}]"]
    | TRawPointer _ -> [%string "raw_pointer!()"]
    | TRef { typ; mut; _ } -> [%string "&%{dmutability mut}%{pty typ}"]
    | TFalse -> [%string "!"]
    | TParam i -> plocal_ident i
    | TArrow (inputs, output) ->
        let arrow =
          List.map ~f:pty (inputs @ [ output ]) |> String.concat ~sep:" -> "
        in
        [%string "arrow!(%{arrow})"]
    | TProjectedAssociatedType _ -> "proj_asso_type!()"

  and pgeneric_value (e : generic_value) =
    match e with
    | GLifetime _ -> "lifetime!(something)"
    | GType t -> pty t
    | _ -> "generic_value!(todo)"

  let pborrow_kind (e : borrow_kind) = match e with Mut _ -> "mut " | _ -> ""

  let last_of_global_ident (g : global_ident) span =
    match g with
    | `Concrete { path; crate = _ } -> Non_empty_list.last path
    | _ ->
        Diagnostics.failure ~context:DebugPrintRust ~span
          (AssertionFailure
             {
               details =
                 "[last_of_global_ident] was given a non-concrete global ident";
             })

  let rec ppat (e : pat) =
    match e.p with
    | PWild -> "_"
    | PAscription { typ; pat; _ } ->
        [%string "pat_ascription!(%{ppat pat} as %{pty typ})"]
    | PConstruct { name; args; record; _ } ->
        pglobal_ident name
        ^
        if List.is_empty args then ""
        else if record then
          "{"
          ^ String.concat ~sep:", "
              (List.map
                 ~f:(fun { field; pat } ->
                   last_of_global_ident field e.span ^ ":" ^ ppat pat)
                 args)
          ^ "}"
        else
          "("
          ^ String.concat ~sep:", "
              (List.map ~f:(fun { pat; _ } -> ppat pat) args)
          ^ ")"
    | PArray { args } ->
        "[" ^ String.concat ~sep:"," (List.map ~f:ppat args) ^ "]"
    | PDeref { subpat; _ } -> [%string "&%{ppat subpat}"]
    | PConstant { lit } -> pliteral lit
    | PBinding { mut; mode; var; typ = _; subpat } ->
        let subpat =
          match subpat with Some (p, _) -> " @ " ^ ppat p | None -> ""
        in
        [%string
          "%{dbinding_mode mode}%{dmutability mut}%{plocal_ident var}%{subpat}"]

  let rec pexpr' (e : expr) : string =
    match e.e with
    | If { cond; then_; else_ } ->
        let else_ =
          match else_ with Some e -> " else {" ^ pexpr e ^ "}" | None -> ""
        in
        [%string "(if %{pexpr cond} %{pexpr then_}%{else_})"]
    | App { f = { e = GlobalVar _; _ } as f; args } ->
        let args = String.concat ~sep:"," @@ List.map ~f:pexpr args in
        [%string "%{pexpr f}(%{args})"]
    | App { f; args } ->
        let args = String.concat ~sep:"," @@ List.map ~f:pexpr args in
        [%string "(%{pexpr f})(%{args})"]
    | Literal e -> pliteral e
    | Array l -> "[" ^ String.concat ~sep:"," (List.map ~f:pexpr l) ^ "]"
    | Construct { constructs_record = false; constructor; fields; base = _ } ->
        let fields =
          List.map ~f:(snd >> pexpr) fields |> String.concat ~sep:","
        in
        [%string "%{pglobal_ident constructor} (%{fields})"]
    | Construct { constructs_record = true; constructor; fields; base } ->
        let fields =
          List.map
            ~f:(fun (field, value) ->
              last_of_global_ident field e.span ^ ":" ^ pexpr value)
            fields
          |> String.concat ~sep:","
        in
        let base =
          match base with Some base -> [%string "..(%{pexpr base})"] | _ -> ""
        in
        [%string "%{pglobal_ident constructor} {%{fields},%{base}}"]
    | Match { scrutinee; arms } ->
        let arms =
          List.map
            ~f:(fun { arm = { pat; body }; _ } ->
              [%string "%{ppat pat} => {%{pexpr body}}"])
            arms
          |> String.concat ~sep:","
        in
        [%string "(match %{pexpr scrutinee} {%{arms}})"]
    | Let { monadic = Some _; _ } -> "monadic_let!()"
    | Let { monadic = _; lhs; rhs; body } ->
        (* TODO: here, [rhs.typ]! *)
        [%string
          "let %{ppat lhs}: %{pty lhs.typ} = {%{pexpr rhs}}; %{pexpr body}"]
    | LocalVar local_ident -> plocal_ident local_ident
    | GlobalVar global_ident -> pglobal_ident global_ident
    | Ascription { e; typ } -> [%string "(%{pexpr e} as %{pty typ})"]
    | MacroInvokation { macro; args; _ } ->
        [%string "%{pglobal_ident macro}!(%{args})"]
    | Assign { lhs; e; _ } -> [%string "(%{plhs lhs e.span} = %{pexpr e})"]
    | Loop { body; kind; state; _ } -> (
        let header =
          match kind with
          | UnconditionalLoop -> "loop"
          | ForLoop { start; end_; var; _ } ->
              [%string
                "for %{plocal_ident var} in (%{pexpr start})..(%{pexpr end_})"]
        in
        let body_wrapper body =
          match state with
          | Some { bpat; _ } -> [%string "|%{ppat bpat}| {%{body}}"]
          | None -> body
        in
        let main = [%string "%{header} { %{body_wrapper (pexpr body)} }"] in
        match state with
        | Some { init; _ } -> [%string "(%{main})(%{pexpr init});"]
        | None -> main)
    | Break { e; _ } -> [%string "(break (%{pexpr e}))"]
    | Continue { e = None; _ } -> "continue"
    | Continue { e = Some (_, e); _ } ->
        [%string "state_passing_continue!(%{pexpr e})"]
    | Return { e; _ } -> [%string "(return %{pexpr e})"]
    | Borrow { kind; e; _ } -> [%string "%{pborrow_kind kind}(%{pexpr e})"]
    | AddressOf _ -> "address_of"
    | EffectAction _ -> "EffectAction"
    | Closure { params; body; _ } ->
        let params = List.map ~f:ppat params |> String.concat ~sep:"," in
        [%string "(|%{params}| {%{pexpr body}})"]
  (* | _ -> "todo!()" *)

  and plhs (e : lhs) span =
    match e with
    | LhsFieldAccessor { e; field; _ } ->
        [%string "%{plhs e span}.%{last_of_global_ident field span}"]
    | LhsArrayAccessor { e; index; _ } ->
        [%string "%{plhs e span}[%{pexpr index}]"]
    | LhsLocalVar { var; _ } -> plocal_ident var
    | LhsArbitraryExpr { e; _ } -> pexpr e

  and pexpr (e : expr) : string =
    let need_braces = [%matches? Let _ | Loop _] e.e in
    let e = pexpr' e in
    if need_braces then "{" ^ e ^ "}" else e

  let pitem (e : item) =
    match e.v with
    | Fn { name; body; generics = _todo; params } ->
        let return_type = pty body.typ in
        let params =
          List.map ~f:(fun { pat; typ; _ } -> ppat pat ^ ": " ^ pty typ) params
          |> String.concat ~sep:","
        in
        [%string
          "fn %{last_of_global_ident name e.span}(%{params}) -> %{return_type} \
           { %{pexpr body} }"]
    | _ -> "/* TODO */"
end

let rustfmt (s : string) : string =
  let stdout, stdin, stderr =
    Unix.open_process_full "rustfmt" (Unix.environment ())
  in
  Out_channel.(
    output_string stdin s;
    flush stdin;
    close stdin);
  let strout = In_channel.input_all stdout in
  let strerr = In_channel.input_all stderr |> Caml.String.trim in
  if String.is_empty strerr then strout
  else
    let err =
      [%string
        "\n\n\
         #######################################################\n\
         ########### WARNING: Failed running rustfmt ###########\n\
         #### STDOUT:\n\
         %{strout}\n\
         #### STDERR:\n\
         %{strerr}\n\
         #######################################################\n"]
    in
    Caml.prerr_endline err;
    [%string "/*\n%{err}\n*/\n\n%{s}"]

let pitem : item -> string = Raw.pitem >> rustfmt
