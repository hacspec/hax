open Hax_engine
open Utils
open Base

module type Library = sig
  module Notation : sig
    val int_repr : string -> string -> string
    val type_str : string
    val bool_str : string
    val unit_str : string
  end
end

module Coq =
functor
  (Lib : Library)
  ->
  struct
    module AST = struct
      type int_size = U8 | U16 | U32 | U64 | U128 | USize
      type int_type = { size : int_size; signed : bool }

      type ty =
        | WildTy
        | Bool
        | Unit
        | TypeTy
        | Int of int_type
        | NameTy of string
        | RecordTy of string * (string * ty) list
        | Product of ty list
        | Coproduct of ty list
        | Arrow of ty * ty
        | ArrayTy of ty * string (* int *)
        | SliceTy of ty
        | AppTy of ty * ty list
        | NatMod of string * int * string
        | Forall of string list * string list * ty
        | Exists of string list * string list * ty

      type literal =
        | Const_string of string
        | Const_char of int
        | Const_int of string * int_type
        | Const_bool of bool

      type pat =
        | WildPat
        | UnitPat
        | Ident of string
        | Lit of literal
        | RecordPat of string * (string * pat) list
        | ConstructorPat of string * pat list
        | TuplePat of pat list
        | AscriptionPat of pat * ty
        | DisjunctivePat of pat list

      type monad_type = Option | Result of ty | Exception of ty

      type term =
        | UnitTerm
        | Let of let_args
        | If of term * term * term
        | Match of term * (pat * term) list
        | Const of literal
        | Literal of string
        | AppFormat of string list * notation_elements list
        | App of term * term list
        | Var of string
        | NameTerm of string
        | RecordConstructor of string * (string * term) list
        | RecordUpdate of string * term * (string * term) list
        | Type of ty
        | Lambda of pat list * term
        | Tuple of term list
        | Array of term list
        | TypedTerm of term * ty

      and notation_elements =
        | Newline of int
        | Typing of ty * int
        | Variable of pat * int
        | Value of term * bool * int

      and assign_args = {
        pattern : pat;
        value : term;
        value_typ : ty;
      }

      and let_args = {
        pattern : pat;
        mut : bool;
        value : term;
        body : term;
        value_typ : ty;
        monad_typ : monad_type option;
      }

      (* TODO: I don't get why you've got InductiveCase VS BaseCase. Why not an inductive case (i.e. a variant, right?) is a name + a list of types? *)
      type inductive_case = InductiveCase of string * ty | BaseCase of string

      type argument =
        | Implicit of pat * ty
        | Explicit of pat * ty
        | Typeclass of string option * ty

      (* name, arguments, body, type *)
      type definition_type = string * argument list * term * ty
      type record_field = Named of string * ty | Coercion of string * ty

      type instance_decl =
        | InlineDef of definition_type
        | LetDef of definition_type

      type instance_decls =
        | InstanceDecls of instance_decl list
        | TermDef of term

      type decl =
        | MultipleDecls of decl list
        | Unimplemented of string
        | Comment of string
        | Definition of definition_type
        | ProgramDefinition of definition_type
        | Equations of definition_type
        | EquationsQuestionmark of definition_type
        | Notation of string * term * string option
        | Record of string * argument list * record_field list
        | Inductive of string * argument list * inductive_case list
        | Class of string * argument list * record_field list
        | Instance of
            string * argument list * ty * ty list * definition_type list
        | ProgramInstance of
            string * argument list * ty * ty list * instance_decls
        | Require of string option * string list * string option
        | ModuleType of string * argument list * record_field list
        | Module of string * string * argument list * record_field list
        | Parameter of string * ty (* definition_type minus 'term' *)
        | HintUnfold of string * ty option
    end

    let __TODO_pat__ s = AST.Ident (s ^ " todo(pat)")
    let __TODO_ty__ s : AST.ty = AST.NameTy (s ^ " todo(ty)")
    let __TODO_term__ s = AST.Const (AST.Const_string (s ^ " todo(term)"))
    let __TODO_item__ s = AST.Unimplemented (s ^ " todo(item)")

    let int_size_to_string (x : AST.int_size) : string =
      match x with
      | AST.U8 -> "8"
      | AST.U16 -> "16"
      | AST.U32 -> "32"
      | AST.U64 -> "64"
      | AST.U128 -> "128"
      | AST.USize -> "32"

    let rec ty_to_string (x : AST.ty) : string =
      match x with
      | AST.WildTy -> "_"
      | AST.Bool -> Lib.Notation.bool_str
      | AST.Coproduct [] -> "⊥"
      | AST.Coproduct l ->
          let ty_str =
            String.concat ~sep:(" " ^ "∐" ^ " ") (List.map ~f:ty_to_string l)
          in
          "(" ^ ty_str ^ ")"
      | AST.Product [] | AST.Unit -> Lib.Notation.unit_str
      | AST.TypeTy -> Lib.Notation.type_str
      | AST.Int { size = AST.USize; signed } -> "uint_size"
      | AST.Int { size; signed } -> "int" ^ int_size_to_string size
      | AST.NameTy s -> s
      | AST.RecordTy (name, fields) -> (* [ AST.Record (name, fields) ] *) name
      | AST.Product l ->
          let ty_str =
            String.concat ~sep:(" " ^ "×" ^ " ") (List.map ~f:ty_to_string l)
          in
          "(" ^ ty_str ^ ")"
      | AST.Arrow (a, b) ->
          let a_ty_str = ty_to_string a in
          let b_ty_str = ty_to_string b in
          a_ty_str ^ " " ^ "->" ^ " " ^ b_ty_str
      | AST.ArrayTy (t, l) ->
          let ty_str = ty_to_string t in
          "nseq" ^ " (" ^ ty_str ^ ") " ^ (* Int.to_string *) l
      | AST.SliceTy t ->
          let ty_str = ty_to_string t in
          "seq" ^ " " ^ ty_str
      | AST.AppTy (i, []) -> ty_to_string i
      (* | AST.AppTy (i, [ y ]) -> *)
      (*     let ty_defs, ty_str = ty_to_string y in *)
      (*     (ty_defs, i ^ " " ^ ty_str) *)
      | AST.AppTy (i, p) ->
          let ty_str = String.concat ~sep:") (" (List.map ~f:ty_to_string p) in
          ty_to_string i ^ " " ^ "(" ^ ty_str ^ ")"
      | AST.NatMod (t, i, s) ->
          (* [ *)
          (*   AST.Notation *)
          (*     ( t, *)
          (*       AST.ArrayTy *)
          (*         (AST.Int { size = U8; signed = false }, Int.to_string i) ); *)
          (* ] *)
          "nat_mod 0x" ^ s
      | AST.Forall ([], [], ty) -> ty_to_string ty
      | AST.Forall (implicit_vars, [], ty) ->
          "forall" ^ " " ^ "{"
          ^ String.concat ~sep:" " implicit_vars
          ^ "}" ^ "," ^ " " ^ ty_to_string ty
      | AST.Forall ([], vars, ty) ->
          "forall" ^ " "
          ^ String.concat ~sep:" " vars
          ^ "," ^ " " ^ ty_to_string ty
      | AST.Forall (implicit_vars, vars, ty) ->
          "forall" ^ " " ^ "{"
          ^ String.concat ~sep:" " implicit_vars
          ^ "}" ^ "," ^ " "
          ^ String.concat ~sep:" " vars
          ^ "," ^ " " ^ ty_to_string ty
      | AST.Exists ([], [], ty) -> ty_to_string ty
      | AST.Exists (implicit_vars, [], ty) ->
          "exists" ^ " " ^ "{"
          ^ String.concat ~sep:" " implicit_vars
          ^ "}" ^ "," ^ " " ^ ty_to_string ty
      | AST.Exists ([], vars, ty) ->
          "exists" ^ " "
          ^ String.concat ~sep:" " vars
          ^ "," ^ " " ^ ty_to_string ty
      | AST.Exists (implicit_vars, vars, ty) ->
          "exists" ^ " " ^ "{"
          ^ String.concat ~sep:" " implicit_vars
          ^ "}" ^ "," ^ " "
          ^ String.concat ~sep:" " vars
          ^ "," ^ " " ^ ty_to_string ty
      | _ -> .

    let literal_to_string (x : AST.literal) : string =
      match x with
      | Const_string s -> s
      | Const_char c -> Int.to_string c (* TODO *)
      | Const_int (i, { size; signed }) ->
          Lib.Notation.int_repr (int_size_to_string size) i
      (*  *)
      | Const_bool b -> Bool.to_string b

    let rec pat_to_string (x : AST.pat) (is_top_expr : bool) depth : string =
      match x with
      | AST.WildPat -> "_"
      | AST.UnitPat -> tick_if is_top_expr ^ "tt"
      | AST.Ident s -> s
      | AST.Lit l -> literal_to_string l
      | AST.ConstructorPat (name, args) ->
          name ^ " " ^ String.concat ~sep:" "
          @@ List.map ~f:(fun pat -> pat_to_string pat false depth) args
      | AST.RecordPat (name, []) -> "(* Empty Record *)" (* TODO *)
      | AST.RecordPat (name, args) ->
          (* name ^ " " ^ *)
          "{|"
          ^ String.concat ~sep:";"
              (List.map
                 ~f:(fun (name, pat) ->
                   newline_indent (depth + 1)
                   ^ name ^ " " ^ ":=" ^ " "
                   ^ pat_to_string pat true (depth + 1))
                 args)
          ^ newline_indent depth ^ "|}"
      | AST.TuplePat [] -> "_" (* TODO: empty tuple pattern? *)
      | AST.TuplePat [ v ] -> pat_to_string v is_top_expr (depth + 1)
      | AST.TuplePat vals ->
          tick_if is_top_expr ^ "("
          ^ String.concat ~sep:","
              (List.map ~f:(fun t -> pat_to_string t false (depth + 1)) vals)
          ^ ")"
      | AST.AscriptionPat (p, ty) ->
          "(" ^ pat_to_string p true depth ^ " " ^ ":" ^ " " ^ ty_to_string ty
          ^ ")" (* TODO: Should this be true of false? *)
      | AST.DisjunctivePat pats ->
          let f pat = pat_to_string pat true depth in
          String.concat ~sep:" | " @@ List.map ~f pats

    and tick_if is_top_expr = if is_top_expr then "'" else ""

    let rec term_to_string (x : AST.term) depth : string * bool =
      match x with
      | AST.UnitTerm -> ("tt", false)
      | AST.Let
          {
            pattern = pat;
            mut;
            value = bind;
            value_typ = typ;
            body = term;
            monad_typ;
          } ->
          (* TODO: propegate type definition *)
          let var_str = pat_to_string pat true depth in
          let expr_str = term_to_string_without_paren bind (depth + 1) in
          let typ_str = ty_to_string typ in
          let body_str = term_to_string_without_paren term depth in
          ( "let" ^ " " ^ var_str ^ " " ^ ":=" ^ " " ^ expr_str ^ " " ^ ":"
            ^ " " ^ typ_str ^ " " ^ "in" ^ newline_indent depth ^ body_str,
            true )
      | AST.If (cond, then_, else_) ->
          ( "if" ^ " "
            ^ term_to_string_without_paren cond (depth + 1)
            ^ newline_indent depth ^ "then" ^ " "
            ^ term_to_string_without_paren then_ (depth + 1)
            ^ newline_indent depth ^ "else" ^ " "
            ^ term_to_string_without_paren else_ (depth + 1),
            true )
      | AST.Match (match_val, arms) ->
          ( "match" ^ " "
            ^ term_to_string_without_paren match_val (depth + 1)
            ^ " " ^ "with" ^ newline_indent depth
            ^ String.concat ~sep:(newline_indent depth)
                (List.map
                   ~f:(fun (pat, body) ->
                     "|" ^ " "
                     ^ pat_to_string pat true depth
                     ^ " " ^ "=>"
                     ^ newline_indent (depth + 1)
                     ^ term_to_string_without_paren body (depth + 1))
                   arms)
            ^ newline_indent depth ^ "end",
            false )
      | AST.Const c -> (literal_to_string c, false)
      | AST.Literal s -> (s, false)
      | AST.AppFormat (format, args) ->
          ( format_to_string format
              (List.map
                 ~f:(function
                   | AST.Newline n -> newline_indent (depth + n)
                   | AST.Typing (typ, n) -> ty_to_string typ
                   | AST.Value (x, true, n) ->
                       term_to_string_with_paren x (depth + n)
                   | AST.Value (x, false, n) ->
                       term_to_string_without_paren x (depth + n)
                   | AST.Variable (p, n) -> pat_to_string p true (depth + n))
                 args),
            true (* TODO? Notation does not always need paren *) )
      | AST.App (f, args) ->
          let f_s, f_b = term_to_string f depth in
          (f_s ^ term_list_to_string args depth, f_b || List.length args > 0)
      | AST.Var s -> (s, false)
      | AST.NameTerm s -> (s, false)
      | AST.RecordConstructor (f, args) ->
          ( "Build_" ^ f
            ^ (if List.length args > 0 then " " else "")
            ^ String.concat ~sep:" "
                (List.map
                   ~f:(fun (n, t) ->
                     "(" ^ n ^ " " ^ ":=" ^ " "
                     ^ term_to_string_without_paren t depth
                     ^ ")")
                   args),
            true )
      | AST.RecordUpdate (f, base, args) ->
          ( "Build_" ^ f ^ "["
            ^ term_to_string_without_paren base depth
            ^ "]"
            ^ (if List.length args > 0 then " " else "")
            ^ String.concat ~sep:" "
                (List.map
                   ~f:(fun (n, t) ->
                     "(" ^ n ^ " " ^ ":=" ^ " "
                     ^ term_to_string_without_paren t depth
                     ^ ")")
                   args),
            true )
      | AST.Type t ->
          let ty_str = ty_to_string t in
          (* TODO: Make definitions? *)
          (ty_str, true (* TODO? does this always need paren? *))
      | AST.Lambda (params, body) ->
          ( String.concat ~sep:" "
              (List.map
                 ~f:(fun x ->
                   "fun" ^ " " ^ pat_to_string x true depth ^ " " ^ "=>")
                 params)
            ^ newline_indent (depth + 1)
            ^ term_to_string_without_paren body (depth + 1),
            true )
      | AST.Tuple [] -> ("tt (* Empty tuple *)", false) (* TODO: Empty tuple? *)
      | AST.Tuple vals ->
          ( "("
            ^ String.concat ~sep:","
                (List.map
                   ~f:(fun t -> term_to_string_without_paren t (depth + 1))
                   vals)
            ^ ")",
            false )
      | AST.Array (t :: ts) ->
          ( "array_from_list" ^ " " ^ "["
            ^ List.fold_left
                ~init:(term_to_string_without_paren t (depth + 1))
                ~f:(fun x y ->
                  x ^ ";"
                  ^ newline_indent (depth + 1)
                  ^ term_to_string_without_paren y (depth + 1))
                ts
            ^ "]",
            true )
      | AST.Array [] -> ("!TODO empty array!", false)
      | AST.TypedTerm (e, t) ->
          ( term_to_string_without_paren e depth
            ^ " " ^ ":" ^ " " ^ ty_to_string t,
            true )
      | _ -> .

    and term_to_string_with_paren (x : AST.term) depth : string =
      let s, b = term_to_string x depth in
      if b then "(" ^ s ^ ")" else s

    and term_to_string_without_paren (x : AST.term) depth : string =
      let s, _ = term_to_string x depth in
      s

    and format_to_string (format : string list) (args : string list) : string =
      match format with
      | f :: fs -> (
          match args with x :: xs -> f ^ x ^ format_to_string fs xs | [] -> f)
      | [] -> failwith "incorrect formatting"

    and term_list_to_string (terms : AST.term list) depth : string =
      (if List.is_empty terms then "" else " ")
      ^ String.concat ~sep:" "
          (List.map ~f:(fun t -> term_to_string_with_paren t depth) terms)

    let rec decl_to_string (x : AST.decl) : string =
      match x with
      | AST.MultipleDecls decls ->
          String.concat ~sep:"\n" (List.map ~f:decl_to_string decls)
      | AST.Unimplemented s -> "(*" ^ s ^ "*)"
      | AST.Comment s -> "(**" ^ " " ^ s ^ " " ^ "**)"
      | AST.Definition (name, arguments, term, ty) ->
          "Definition" ^ " "
          ^ definition_value_to_string (name, arguments, term, ty)
      | AST.ProgramDefinition (name, arguments, term, ty) ->
          "Program" ^ " " ^ "Definition" ^ " "
          ^ definition_value_to_string (name, arguments, term, ty)
          ^ fail_next_obligation
      | AST.Equations (name, arguments, term, ty) ->
          "Equations" ^ " "
          ^ definition_value_to_equation_definition (name, arguments, term, ty)
      | AST.EquationsQuestionmark (name, arguments, term, ty) ->
          "Equations?" ^ " "
          ^ definition_value_to_equation_definition (name, arguments, term, ty)
      | AST.Notation (notation, value, extra) ->
          "Notation" ^ " " ^ "\"" ^ notation ^ "\"" ^ " " ^ ":=" ^ " "
          ^ term_to_string_with_paren value 0
          ^ (match extra with None -> "" | Some x -> " " ^ "(" ^ x ^ ")")
          ^ "."
      | AST.Record (name, arguments, variants) ->
          let variants_str =
            variants_to_string variants (newline_indent 1) ";"
          in
          "Record" ^ " " ^ name
          ^ params_to_string_typed arguments
          ^ " " ^ ":" ^ " " ^ "Type" ^ " " ^ ":=" ^ " " ^ "{" ^ variants_str
          ^ newline_indent 0 ^ "}."
      | AST.Inductive (name, arguments, variants) ->
          let name_arguments = name ^ params_to_string_typed arguments in
          let variants_str =
            String.concat ~sep:(newline_indent 0)
              (List.map
                 ~f:(fun x ->
                   let mid_str =
                     match x with
                     | AST.BaseCase ty_name -> ty_name ^ " : "
                     | AST.InductiveCase (ty_name, ty) ->
                         let ty_str = ty_to_string ty in
                         ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ "->" ^ " "
                   in
                   ("|" ^ " ") ^ mid_str ^ name_arguments)
                 variants)
          in
          let args_str =
            if List.is_empty arguments then ""
            else
              inductive_case_args_to_string variants
                (newline_indent 0 ^ "Arguments" ^ " ")
                (List.fold_left ~init:"" ~f:(fun a b -> a ^ " {_}") arguments)
                "."
          in
          "Inductive" ^ " " ^ name_arguments ^ " " ^ ":" ^ " " ^ "Type" ^ " "
          ^ ":=" ^ newline_indent 0 ^ variants_str ^ "." ^ args_str
      | AST.Class (name, arguments, trait_items) ->
          let field_str =
            List.fold_left ~init:""
              ~f:(fun x y ->
                let field_name, sep, field_ty =
                  match y with
                  | Named (field_name, field_ty) -> (field_name, ":", field_ty)
                  | Coercion (field_name, field_ty) ->
                      (field_name, ":>", field_ty)
                  (* Should be "::" in newer versions of coq *)
                in
                let ty_str = ty_to_string field_ty in
                x ^ newline_indent 1 ^ field_name ^ " " ^ sep ^ " " ^ ty_str
                ^ " " ^ ";")
              trait_items
          in
          "Class" ^ " " ^ name ^ " " ^ "(Self : " ^ ty_to_string AST.TypeTy
          ^ ")"
          ^ params_to_string_typed arguments
          ^ " " ^ ":=" ^ " " ^ "{" ^ field_str ^ newline_indent 0 ^ "}" ^ "."
      | AST.ModuleType (name, arguments, trait_items) ->
          let field_str =
            List.fold_left ~init:""
              ~f:(fun x y ->
                x ^ newline_indent 1
                ^
                match y with
                | Named (field_name, field_ty) ->
                    decl_to_string (AST.Parameter (field_name, field_ty))
                | Coercion (field_name, field_ty) ->
                    decl_to_string
                      (AST.Module (field_name, ty_to_string field_ty, [], []))
                (* Should be "::" in newer versions of coq *))
              trait_items
          in
          let arguments_str = params_to_string_typed arguments in
          "Module Type" ^ " " ^ name ^ arguments_str ^ "." ^ newline_indent 1
          ^ field_str ^ newline_indent 0 ^ "End" ^ " " ^ name ^ "."
      | AST.Parameter (name, typ) ->
          String.concat ~sep:" " [ name; ":"; ty_to_string typ ]
      | AST.Module (name, typ, arguments, trait_items) ->
          let field_str =
            List.fold_left ~init:""
              ~f:(fun x y ->
                x ^ newline_indent 1
                ^
                match y with
                | Named (field_name, field_ty) ->
                    decl_to_string (AST.Parameter (field_name, field_ty))
                | Coercion (field_name, field_ty) ->
                    decl_to_string
                      (AST.Module (field_name, ty_to_string field_ty, [], []))
                (* Should be "::" in newer versions of coq *))
              trait_items
          in
          let arguments_str = params_to_string_typed arguments in
          "Module" ^ " " ^ name ^ arguments_str ^ " " ^ ":" ^ " " ^ typ ^ "."
          ^ " " ^ "End" ^ " " ^ name ^ "."
      | AST.Instance (name, arguments, self_ty, ty_list, impl_list) ->
          let ty_list_str =
            String.concat ~sep:" " (List.map ~f:ty_to_string ty_list)
          in
          let impl_str =
            List.fold_left ~init:""
              ~f:(fun x (name, arguments, term, ty) ->
                x ^ newline_indent 1 ^ name
                ^ params_to_string_typed arguments
                ^ " " ^ ":=" ^ " "
                ^ term_to_string_without_paren term 1
                ^ ";")
              impl_list
          in
          let ty_str = ty_to_string self_ty in
          "#[global] Instance" ^ " " ^ ty_str ^ "_" ^ name
          ^ params_to_string_typed arguments
          ^ " " ^ ":" ^ " " ^ name ^ " " ^ ty_list_str ^ " " ^ ":=" ^ " " ^ "{"
          ^ impl_str ^ newline_indent 0 ^ "}" ^ "."
      | AST.ProgramInstance
          (name, arguments, self_ty, ty_list, InstanceDecls impl_list) ->
          let ty_list_str =
            String.concat ~sep:" " (List.map ~f:ty_to_string ty_list)
          in
          let impl_str, impl_str_empty =
            let fl =
              List.filter_map
                ~f:(function
                  | LetDef (name, arguments, term, ty) ->
                      Some
                        ("let" ^ " " ^ name ^ " " ^ ":=" ^ " "
                        ^ (if List.is_empty arguments then ""
                          else
                            "fun" ^ " "
                            ^ params_to_string_typed arguments
                            ^ " " ^ "=>" ^ " ")
                        ^ term_to_string_without_paren term 1
                        ^ " " ^ ":" ^ " " ^ ty_to_string ty ^ " " ^ "in")
                  | _ -> None)
                impl_list
            in
            (String.concat ~sep:(newline_indent 1) fl, List.length fl == 0)
          in
          let arg_str =
            String.concat
              ~sep:(";" ^ newline_indent 1)
              (List.map
                 ~f:(function
                   | LetDef (name, arguments, term, ty) ->
                       name ^ " " ^ ":=" ^ " " ^ "(" ^ "@" ^ name ^ ")"
                   | InlineDef (name, arguments, term, ty) ->
                       name ^ " " ^ ":=" ^ " " ^ "("
                       ^ (if List.is_empty arguments then ""
                         else
                           "fun" ^ " "
                           ^ params_to_string_typed arguments
                           ^ " " ^ "=>" ^ " ")
                       ^ term_to_string_without_paren term 1
                       ^ " " ^ ":" ^ " " ^ ty_to_string ty ^ ")")
                 impl_list)
          in
          let ty_str = ty_to_string self_ty in
          "#[global] Program Instance" ^ " " ^ ty_str ^ "_" ^ name
          ^ params_to_string_typed arguments
          ^ " " ^ ":" ^ " " ^ name ^ " " ^ ty_list_str ^ " " ^ ":="
          ^ newline_indent 1 ^ impl_str
          ^ (if impl_str_empty then "" else newline_indent 1)
          ^ (match impl_list with
            | [] -> "_"
            | _ -> "{|" (* ^ name ^ " " ^ ty_list_str *) ^ " " ^ arg_str ^ "|}")
          ^ "." ^ fail_next_obligation
      | AST.ProgramInstance (name, arguments, self_ty, ty_list, TermDef term) ->
          let ty_list_str =
            String.concat ~sep:" " (List.map ~f:ty_to_string ty_list)
          in
          let ty_str = ty_to_string self_ty in
          "#[global] Program Instance" ^ " " ^ ty_str ^ "_" ^ name
          ^ params_to_string_typed arguments
          ^ " " ^ ":" ^ " " ^ name ^ " " ^ ty_list_str ^ " " ^ ":="
          ^ newline_indent 1
          ^ term_to_string_without_paren term 1
          ^ "." ^ fail_next_obligation
      | AST.Require (_, [], rename) -> ""
      | AST.Require (None, import :: imports, rename) ->
          (* map_first_letter String.uppercase import *)
          let import_name =
            match rename with
            | Some s -> s
            | _ ->
                List.fold_left
                  ~init:(map_first_letter String.uppercase import)
                  ~f:(fun x y -> x ^ "_" ^ map_first_letter String.uppercase y)
                  imports
          in
          "Require Import" ^ " " ^ import_name ^ "." ^ newline_indent 0
          ^ "Export" ^ " " ^ import_name ^ "."
      | AST.Require (Some x, imports, rename) ->
          "From" ^ " " ^ x ^ " "
          ^ decl_to_string (AST.Require (None, imports, rename))
      | AST.HintUnfold (n, Some typ) ->
          let ty_str = ty_to_string typ in
          "Hint Unfold" ^ " " ^ ty_str ^ "_" ^ n ^ "."
      | AST.HintUnfold (n, None) -> "Hint Unfold" ^ " " ^ n ^ "."

    and definition_value_to_equation_definition
        ((name, arguments, term, ty) : AST.definition_type) =
      let ty_str = ty_to_string ty in
      definition_value_to_shell_string
        (name, arguments, term, ty)
        (name ^ " "
        ^ params_to_string
            (List.filter_map
               ~f:(fun x ->
                 match x with Explicit (y, z) -> Some (y, z) | _ -> None)
               arguments)
        ^ " " ^ ":=" ^ newline_indent 2
        ^ term_to_string_without_paren term 2
        ^ " " ^ ":" ^ " " ^ ty_str)
      ^ fail_next_obligation

    and definition_value_to_shell_string
        ((name, arguments, _, ty) : AST.definition_type) (body : string) :
        string =
      let ty_str = ty_to_string ty in
      name
      ^ params_to_string_typed arguments
      ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ ":=" ^ newline_indent 1 ^ body ^ "."

    and definition_value_to_string
        ((name, arguments, term, ty) : AST.definition_type) : string =
      definition_value_to_shell_string
        (name, arguments, term, ty)
        (term_to_string_without_paren term 1)

    and fail_next_obligation : string =
      newline_indent 0 ^ "Fail" ^ " " ^ "Next" ^ " " ^ "Obligation."

    and params_to_string_typed params : string =
      if List.is_empty params then ""
      else
        " "
        ^ String.concat ~sep:" "
            (List.map
               ~f:(fun param ->
                 match param with
                 | Implicit (pat, ty) ->
                     "{" ^ pat_to_string pat true 0 ^ " " ^ ":" ^ " "
                     ^ ty_to_string ty ^ "}"
                 | Explicit (pat, ty) ->
                     "(" ^ pat_to_string pat true 0 ^ " " ^ ":" ^ " "
                     ^ ty_to_string ty ^ ")"
                 | Typeclass (None, ty) -> "`{" ^ " " ^ ty_to_string ty ^ "}"
                 | Typeclass (Some name, ty) ->
                     "`{" ^ name ^ " " ^ ":" ^ " " ^ ty_to_string ty ^ "}")
               params)

    and params_to_string params : string =
      String.concat ~sep:""
        (List.map
           ~f:(fun (pat, ty) ->
             let ty_str = ty_to_string ty in
             pat_to_string pat true 0 ^ " ")
           params)

    (* and inductive_case_to_string variants pre post : string = *)
    (*   match variants with *)
    (*   | x :: xs -> *)
    (*       let mid_str = *)
    (*         match x with *)
    (*         | AST.BaseCase ty_name -> ty_name *)
    (*         | AST.InductiveCase (ty_name, ty) -> *)
    (*             let ty_str = ty_to_string ty in *)
    (*             ty_name ^ " " ^ ":" ^ " " ^ ty_str ^ " " ^ "->" ^ " " *)
    (*       in *)
    (*       let variants_str = inductive_case_to_string xs pre post in *)
    (*       pre ^ mid_str ^ post ^ variants_str *)
    (*   | [] -> "" *)

    and inductive_case_args_to_string variants pre mid post : string =
      String.concat ~sep:""
        (List.map
           ~f:(fun x ->
             let mid_str, ty_str =
               match x with
               | AST.BaseCase ty_name -> (ty_name, "")
               | AST.InductiveCase (ty_name, ty) ->
                   (ty_name, " " ^ ty_to_string ty)
             in
             pre ^ mid_str ^ mid ^ ty_str ^ post)
           variants)

    and variants_to_string variants pre post : string =
      String.concat ~sep:""
        (List.map
           ~f:(fun y ->
             let ty_name, sep, ty =
               match y with
               | Named (ty_name, ty) -> (ty_name, ":", ty)
               | Coercion (ty_name, ty) -> (ty_name, ":>", ty)
               (* Should be "::" in newer versions of coq *)
             in
             pre ^ ty_name ^ " " ^ ":" ^ " " ^ ty_to_string ty ^ post)
           variants)
  end
