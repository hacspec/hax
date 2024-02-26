open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Macro
      include On.Question_mark
      include On.Early_exit
      include On.Slice
      include On.Quote
      include On.Construct_base
    end)
    (struct
      let backend = Diagnostics.Backend.ProVerif
    end)

module SubtypeToInputLanguage
    (FA : Features.T
          (*  type loop = Features.Off.loop *)
          (* and type for_loop = Features.Off.for_loop *)
          (* and type for_index_loop = Features.Off.for_index_loop *)
          (* and type state_passing_loop = Features.Off.state_passing_loop *)
          (* and type continue = Features.Off.continue *)
          (* and type break = Features.Off.break *)
          (* and type mutable_variable = Features.Off.mutable_variable *)
          (* and type mutable_reference = Features.Off.mutable_reference *)
          (* and type mutable_pointer = Features.Off.mutable_pointer *)
          (* and type reference = Features.Off.reference *)
          (* and type slice = Features.Off.slice *)
          (* and type raw_pointer = Features.Off.raw_pointer *)
            with type early_exit = Features.On.early_exit
             and type slice = Features.On.slice
             and type question_mark = Features.On.question_mark
             and type macro = Features.On.macro
             and type quote = Features.On.quote
             and type construct_base = Features.On.construct_base
    (* and type as_pattern = Features.Off.as_pattern *)
    (* and type nontrivial_lhs = Features.Off.nontrivial_lhs *)
    (* and type arbitrary_lhs = Features.Off.arbitrary_lhs *)
    (* and type lifetime = Features.Off.lifetime *)
    (* and type construct_base = Features.Off.construct_base *)
    (* and type monadic_action = Features.Off.monadic_action *)
    (* and type monadic_binding = Features.Off.monadic_binding *)
    (* and type block = Features.Off.block *)) =
struct
  module FB = InputLanguage

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let continue = reject
        let loop = reject
        let for_loop = reject
        let while_loop = reject
        let for_index_loop = reject
        let state_passing_loop = reject
        let continue = reject
        let break = reject
        let mutable_variable = reject
        let mutable_reference = reject
        let mutable_pointer = reject
        let reference = reject
        let raw_pointer = reject
        let as_pattern = reject
        let nontrivial_lhs = reject
        let arbitrary_lhs = reject
        let lifetime = reject
        let monadic_action = reject
        let monadic_binding = reject
        let block = reject
        let dyn = reject
        let match_guard = reject
        let trait_item_default = reject
        let unsafe = reject
        let metadata = Phase_reject.make_metadata (NotInBackendLang ProVerif)
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module BackendOptions = struct
  type t = Hax_engine.Types.pro_verif_options
end

open Ast

module ProVerifNamePolicy = struct
  include Concrete_ident.DefaultNamePolicy

  [@@@ocamlformat "disable"]

  let index_field_transform index = Fn.id index

  let reserved_words = Hash_set.of_list (module String) [
  "among"; "axiom"; "channel"; "choice"; "clauses"; "const"; "def"; "diff"; "do"; "elimtrue"; "else"; "equation"; "equivalence"; "event"; "expand"; "fail"; "for"; "forall"; "foreach"; "free"; "fun"; "get"; "if"; "implementation"; "in"; "inj-event"; "insert"; "lemma"; "let"; "letfun"; "letproba"; "new"; "noninterf"; "noselect"; "not"; "nounif"; "or"; "otherwise"; "out"; "param"; "phase"; "pred"; "proba"; "process"; "proof"; "public vars"; "putbegin"; "query"; "reduc"; "restriction"; "secret"; "select"; "set"; "suchthat"; "sync"; "table"; "then"; "type"; "weaksecret"; "yield"
  ]

  let field_name_transform ~struct_name field_name = struct_name ^ "_" ^ field_name

  let enum_constructor_name_transform ~enum_name constructor_name = enum_name ^ "_" ^ constructor_name ^ "_c"

  let struct_constructor_name_transform constructor_name =  constructor_name ^ "_c"
end

module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (ProVerifNamePolicy)
open AST

module type OPTS = sig
  val options : Hax_engine.Types.pro_verif_options
end

module type MAKE = sig
  module Preamble : sig
    val print : item list -> string
  end

  module DataTypes : sig
    val print : item list -> string
  end

  module Letfuns : sig
    val print : item list -> string
  end

  module Processes : sig
    val print : item list -> string
  end

  module Toplevel : sig
    val print : item list -> string
  end
end

module Make (Options : OPTS) : MAKE = struct
  module Print = struct
    module GenericPrint =
      Generic_printer.Make (InputLanguage) (U.Concrete_ident_view)

    open Generic_printer_base.Make (InputLanguage)
    open PPrint

    let iblock f = group >> jump 2 0 >> terminate (break 0) >> f >> group

    (* TODO: Give definitions for core / known library functions, cf issues #447, #448 *)
    let library_functions :
        (Concrete_ident_generated.t * (AST.expr list -> document)) list =
      []

    let library_constructors :
        (Concrete_ident_generated.t
        * ((global_ident * AST.expr) list -> document))
        list =
      []

    let library_constructor_patterns :
        (Concrete_ident_generated.t * (field_pat list -> document)) list =
      []

    let library_types : (Concrete_ident_generated.t * document) list = []

    let assoc_known_name name (known_name, _) =
      Global_ident.eq_name known_name name

    let translate_known_name name ~dict =
      List.find ~f:(assoc_known_name name) dict

    class print aux =
      object (print)
        inherit GenericPrint.print as super

        (* Backend-specific utilities *)

        method pv_event_def name =
          string "event" ^^ space ^^ name ^^ dot ^^ hardline
        (** Print a ProVerif event definition. (without arguments)*)

        method pv_event_emission name =
          string "event" ^^ space ^^ name ^^ semi ^^ hardline
        (** Print a ProVerif event emission process term. (no arguments)*)

        (* ProVerif syntax *)
        method pv_comment content =
          string "(*" ^^ space ^^ content ^^ space ^^ string "*)" ^^ hardline
        (** Print a ProVerif comment and end the line. *)

        method pv_const name typ =
          string "const" ^^ space ^^ name ^^ colon ^^ space ^^ typ ^^ dot
        (** Print a ProVerif constant declaration of the given typ (provided as a document).*)

        method pv_constructor ?(is_data = false) ?(is_typeconverter = false)
            name arg_types typ =
          let options = if is_data then [ string "data" ] else [] in
          let options =
            if is_typeconverter then string "typeConverter" :: options
            else options
          in
          let options =
            space ^^ string "["
            ^^ separate (comma ^^ space) options
            ^^ string "]"
          in
          string "fun" ^^ space
          ^^ align
               (name
               ^^ iblock parens (separate (comma ^^ break 1) arg_types)
               ^^ hardline ^^ colon ^^ space ^^ typ ^^ options ^^ dot)
        (** Print a ProVerif constructor. *)

        method pv_type name = string "type" ^^ space ^^ name ^^ dot ^^ hardline
        (** Print a ProVerif type definition. *)

        method pv_letfun name args body =
          string "letfun" ^^ space
          ^^ align
               (name
               ^^ iblock parens (separate (comma ^^ break 1) args)
               ^^ space ^^ equals ^^ hardline ^^ body ^^ dot)
        (** Print a ProVerif letfun definition. *)

        method pv_letfun_call name args =
          name ^^ iblock parens (separate (comma ^^ break 1) args)
        (** Print a ProVerif letfun call. *)

        (* Helpers *)
        method default_value type_name = type_name ^^ string "_default_value"
        method default_letfun_name type_name = type_name ^^ string "_default"
        method error_letfun_name type_name = type_name ^^ string "_err"

        method field_accessor field_name =
          string "accessor" ^^ underscore ^^ print#concrete_ident field_name

        method match_arm scrutinee { arm_pat; body } =
          let body_typ = print#ty AlreadyPar body.typ in
          let body = print#expr_at Arm_body body in
          match arm_pat with
          | { p = PWild; _ } -> body
          | { p = PConstruct { name; _ } }
            when Global_ident.eq_name Core__result__Result__Err name ->
              print#pv_letfun_call (print#error_letfun_name body_typ) []
          | _ ->
              let pat =
                match arm_pat with
                | { p = PConstant { lit } } ->
                    iblock parens (string "=" ^^ print#literal Pat lit)
                | _ -> print#pat_at Arm_pat arm_pat |> group
              in
              let scrutinee = print#expr_at Expr_Match_scrutinee scrutinee in
              string "let" ^^ space ^^ pat ^^ string " = " ^^ scrutinee
              ^^ string " in " ^^ body

        val mutable wildcard_index = 0

        method wildcard =
          wildcard_index <- wildcard_index + 1;
          string "wildcard" ^^ OCaml.int wildcard_index

        method typed_wildcard = print#wildcard ^^ string ": bitstring"

        method tuple_elem_pat' : Generic_printer_base.par_state -> pat' fn =
          fun ctx ->
            let wrap_parens =
              group
              >>
              match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock parens
            in
            function
            | PBinding { mut; mode; var; typ; subpat } ->
                let p = print#local_ident var in
                p ^^ colon ^^ space ^^ print#ty ctx typ
            | p -> print#pat' ctx p

        method tuple_elem_pat : Generic_printer_base.par_state -> pat fn =
          fun ctx { p; span; _ } ->
            print#with_span ~span (fun _ -> print#tuple_elem_pat' ctx p)

        method tuple_elem_pat_at = print#par_state >> print#tuple_elem_pat

        (* Overridden methods *)
        method! pat' : Generic_printer_base.par_state -> pat' fn =
          fun ctx ->
            let wrap_parens =
              group
              >>
              match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock parens
            in
            fun pat ->
              match pat with
              | PConstant { lit } -> string "=" ^^ print#literal Pat lit
              | PConstruct { name; args }
                when Global_ident.eq_name Core__option__Option__None name ->
                  string "None()"
              | PConstruct { name; args }
              (* The `Some` constructor in ProVerif expects a
                 bitstring argument, so we use the appropriate
                 `_to_bitstring` type converter on the inner
                 expression. *)
                when Global_ident.eq_name Core__option__Option__Some name ->
                  let inner_field = List.hd_exn args in
                  let inner_field_type_doc =
                    print#ty AlreadyPar inner_field.pat.typ
                  in
                  let inner_field_doc = print#pat ctx inner_field.pat in
                  let inner_block =
                    match inner_field.pat.typ with
                    | TApp { ident = `TupleType _ }
                    (* Tuple types should be translated without conversion from bitstring *)
                      ->
                        iblock parens inner_field_doc
                    | _ ->
                        iblock parens
                          (inner_field_type_doc ^^ string "_to_bitstring"
                          ^^ iblock parens inner_field_doc)
                  in
                  string "Some" ^^ inner_block
              | PConstruct { name; args }
              (* We replace applications of the `Ok` constructor
                 with their contents. *)
                when Global_ident.eq_name Core__result__Result__Ok name ->
                  let inner_field = List.hd_exn args in
                  let inner_field_type_doc =
                    print#ty AlreadyPar inner_field.pat.typ
                  in
                  let inner_field_doc = print#pat ctx inner_field.pat in
                  inner_field_doc
              | PConstruct { name; args } -> (
                  match
                    translate_known_name name ~dict:library_constructor_patterns
                  with
                  | Some (_, translation) -> translation args
                  | None -> super#pat' ctx pat)
              | PWild ->
                  print#typed_wildcard
                  (* NOTE: Wildcard translation without collisions? *)
              | _ -> super#pat' ctx pat

        method! ty_bool = string "bool"
        method! ty_int _ = string "nat"

        method! pat_at : Generic_printer_base.ast_position -> pat fn =
          fun pos pat ->
            match pat with
            | { p = PWild } -> (
                match pos with
                | Param_pat -> print#wildcard
                | _ -> print#pat (print#par_state pos) pat)
            | _ -> print#pat (print#par_state pos) pat

        method! pat_construct_tuple : pat list fn =
          List.map ~f:(print#tuple_elem_pat_at Pat_ConstructTuple)
          >> print#doc_construct_tuple

        method! expr_app f args _generic_args =
          let args =
            separate_map
              (comma ^^ break 1)
              (print#expr_at Expr_App_arg >> group)
              args
          in
          let f =
            match f with
            | { e = GlobalVar name; _ } -> (
                match name with
                | `Projector (`Concrete i) | `Concrete i ->
                    print#concrete_ident i |> group
                | _ -> super#expr_at Expr_App_f f |> group)
          in
          f ^^ iblock parens args

        method! expr' : Generic_printer_base.par_state -> expr' fn =
          fun ctx e ->
            let wrap_parens =
              group
              >>
              match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock parens
            in
            match e with
            | QuestionMark { e; return_typ; _ } -> print#expr ctx e
            (* Translate known functions *)
            | App { f = { e = GlobalVar name; _ }; args } -> (
                let maps_to_identity fn_name =
                  Global_ident.eq_name Core__clone__Clone__clone name
                  || Global_ident.eq_name Rust_primitives__unsize name
                  || Global_ident.eq_name Core__ops__deref__Deref__deref name
                in
                match name with
                | `Primitive p -> (
                    match p with
                    | LogicalOp And ->
                        print#expr NeedsPar (List.hd_exn args)
                        ^^ space ^^ string "&&" ^^ space
                        ^^ print#expr NeedsPar (List.nth_exn args 1)
                    | LogicalOp Or ->
                        print#expr NeedsPar (List.hd_exn args)
                        ^^ space ^^ string "||" ^^ space
                        ^^ print#expr NeedsPar (List.nth_exn args 1)
                    | Cast -> print#expr NeedsPar (List.hd_exn args)
                    | _ -> empty)
                | _ -> (
                    if maps_to_identity name then
                      print#expr ctx (List.hd_exn args)
                    else
                      match
                        translate_known_name name ~dict:library_functions
                      with
                      | Some (name, translation) -> translation args
                      | None -> (
                          match name with
                          | `Projector (`Concrete name) ->
                              print#field_accessor name
                              ^^ iblock parens
                                   (separate_map
                                      (comma ^^ break 1)
                                      (fun arg -> print#expr AlreadyPar arg)
                                      args)
                          | _ -> super#expr' ctx e)))
            | Construct { constructor; fields; _ }
              when Global_ident.eq_name Core__option__Option__None constructor
              ->
                string "None()"
            | Construct { constructor; fields; _ }
              when Global_ident.eq_name Core__option__Option__Some constructor
              ->
                let inner_expr = snd (Option.value_exn (List.hd fields)) in
                let inner_expr_type_doc = print#ty AlreadyPar inner_expr.typ in
                let inner_expr_doc = super#expr ctx inner_expr in
                string "Some"
                ^^ iblock parens
                     (inner_expr_type_doc ^^ string "_to_bitstring"
                     ^^ iblock parens inner_expr_doc)
            (* Translate known constructors *)
            | Construct { constructor; fields } -> (
                match
                  translate_known_name constructor ~dict:library_constructors
                with
                | Some (name, translation) -> translation fields
                | None -> super#expr' ctx e)
            | Match { scrutinee; arms } ->
                separate_map
                  (hardline ^^ string "else ")
                  (fun { arm; span } -> print#match_arm scrutinee arm)
                  arms
            | If { cond; then_; else_ } -> (
                let if_then =
                  (string "if" ^//^ nest 2 (print#expr_at Expr_If_cond cond))
                  ^/^ string "then"
                  ^//^ (print#expr_at Expr_If_then then_ |> parens |> nest 1)
                in
                match else_ with
                | None -> if_then
                | Some else_ ->
                    if_then ^^ break 1 ^^ string "else" ^^ space
                    ^^ (print#expr_at Expr_If_else else_ |> iblock parens)
                    |> wrap_parens)
            | Let { monadic; lhs; rhs; body } ->
                (Option.map
                   ~f:(fun monad -> print#expr_monadic_let ~monad)
                   monadic
                |> Option.value ~default:print#expr_let)
                  ~lhs ~rhs body
                |> wrap_parens
            | _ -> super#expr' ctx e

        method! concrete_ident = print#concrete_ident' ~under_current_ns:false

        method! item_unwrapped item =
          let assume_item =
            List.rev Options.options.assume_items
            |> List.find ~f:(fun (clause : Types.inclusion_clause) ->
                   let namespace = clause.namespace in
                   Concrete_ident.matches_namespace namespace item.ident)
            |> Option.map ~f:(fun (clause : Types.inclusion_clause) ->
                   match clause.kind with Types.Excluded -> false | _ -> true)
            |> Option.value ~default:false
          in
          let fun_and_reduc base_name constructor =
            let field_prefix =
              if constructor.is_record then empty
              else print#concrete_ident base_name
            in
            let fun_args = constructor.arguments in
            let fun_args_full =
              separate_map
                (comma ^^ break 1)
                (fun (x, y, _z) ->
                  print#concrete_ident x ^^ string ": "
                  ^^ print#ty_at Param_typ y)
                fun_args
            in
            let fun_args_names =
              separate_map
                (comma ^^ break 1)
                (fst3 >> fun x -> print#concrete_ident x)
                fun_args
            in
            let fun_args_types =
              List.map ~f:(snd3 >> print#ty_at Param_typ) fun_args
            in
            let constructor_name = print#concrete_ident constructor.name in
            let fun_line =
              print#pv_constructor ~is_data:true constructor_name fun_args_types
                (print#concrete_ident base_name)
            in
            let reduc_line =
              string "reduc forall " ^^ iblock Fn.id fun_args_full ^^ semi
            in
            let build_accessor (ident, ty, attr) =
              print#field_accessor ident
              ^^ iblock parens (constructor_name ^^ iblock parens fun_args_names)
              ^^ blank 1 ^^ equals ^^ blank 1 ^^ print#concrete_ident ident
            in
            let reduc_lines =
              separate_map (dot ^^ hardline)
                (fun arg ->
                  reduc_line ^^ nest 4 (hardline ^^ build_accessor arg))
                fun_args
            in
            fun_line ^^ hardline ^^ reduc_lines
            ^^ if reduc_lines == empty then empty else dot
          in
          match item.v with
          (* `fn`s with empty parameter lists are really Rust consts. *)
          | Fn { name; body; params = [] } ->
              let const_typ =
                match body.typ with
                (* ProVerif does not allow `nat` constants. *)
                | TInt _ -> string "bitstring"
                | _ -> print#ty_at Item_Fn_body body.typ
              in
              print#pv_const (print#concrete_ident name) const_typ
          | Fn { name; generics; body; params } ->
              let as_constructor : attrs -> bool =
                Attr_payloads.payloads
                >> List.exists ~f:(fst >> [%matches? Types.PVConstructor])
              in
              let as_handwritten : attrs -> bool =
                Attr_payloads.payloads
                >> List.exists ~f:(fst >> [%matches? Types.PVHandwritten])
              in
              if as_constructor item.attrs then
                let arg_types =
                  List.map ~f:(fun p -> print#ty_at Param_typ p.typ) params
                in
                let return_typ = print#ty_at Item_Fn_body body.typ in
                print#pv_comment (string "marked as constructor")
                ^^ print#pv_constructor ~is_data:true
                     (print#concrete_ident name)
                     arg_types return_typ
              else
                let comment =
                  if assume_item then
                    print#pv_comment
                      (string "REPLACE by body of type: "
                      ^^ print#ty_at Item_Fn_body body.typ)
                  else if as_handwritten item.attrs then
                    print#pv_comment (string "REPLACE by handwritten model")
                  else empty
                in
                let reached_event_name =
                  string "Reached" ^^ underscore ^^ print#concrete_ident name
                in
                let exit_event_name =
                  string "Exit" ^^ underscore ^^ print#concrete_ident name
                in
                let body =
                  if assume_item || as_handwritten item.attrs then
                    let body_type = print#ty_at Item_Fn_body body.typ in
                    print#pv_letfun_call
                      (print#default_letfun_name body_type)
                      []
                  else print#expr_at Item_Fn_body body
                in
                comment
                ^^ print#pv_letfun
                     (print#concrete_ident name)
                     (List.map ~f:print#param params)
                     body
          | Type { name; generics; variants; is_struct } ->
              let type_name_doc = print#concrete_ident name in
              let type_line = print#pv_type type_name_doc in
              let to_bitstring_converter_line =
                print#pv_constructor ~is_typeconverter:true
                  (type_name_doc ^^ string "_to_bitstring")
                  [ type_name_doc ] (string "bitstring")
              in
              let from_bitstring_converter_line =
                print#pv_constructor ~is_typeconverter:true
                  (type_name_doc ^^ string "_from_bitstring")
                  [ string "bitstring" ]
                  type_name_doc
              in
              let default_line =
                let const_name = print#default_value type_name_doc in
                print#pv_const const_name type_name_doc
                ^^ hardline
                ^^ print#pv_letfun
                     (print#default_letfun_name type_name_doc)
                     [] const_name
              in
              let err_line =
                print#pv_letfun
                  (print#error_letfun_name type_name_doc)
                  []
                  (string "let x = construct_fail() in "
                  ^^ print#default_value type_name_doc)
              in

              if is_struct then
                let struct_constructor = List.hd variants in
                match struct_constructor with
                | None -> empty
                | Some constructor ->
                    type_line ^^ hardline ^^ to_bitstring_converter_line
                    ^^ hardline ^^ from_bitstring_converter_line ^^ hardline
                    ^^ default_line ^^ hardline ^^ err_line ^^ hardline
                    ^^ fun_and_reduc name constructor
              else
                type_line ^^ hardline ^^ to_bitstring_converter_line ^^ hardline
                ^^ from_bitstring_converter_line ^^ hardline ^^ default_line
                ^^ hardline ^^ err_line ^^ hardline
                ^^ separate_map hardline
                     (fun variant -> fun_and_reduc name variant)
                     variants
          | Quote quote -> print#quote quote
          | _ -> empty

        method! expr_let : lhs:pat -> rhs:expr -> expr fn =
          fun ~lhs ~rhs body ->
            string "let" ^^ space
            ^^ iblock Fn.id (print#pat_at Expr_Let_lhs lhs)
            ^^ space ^^ equals ^^ space
            ^^ iblock Fn.id (print#expr_at Expr_Let_rhs rhs)
            ^^ space ^^ string "in" ^^ hardline
            ^^ (print#expr_at Expr_Let_body body |> group)

        method! concrete_ident' ~(under_current_ns : bool) : concrete_ident fn =
          fun id ->
            if under_current_ns then print#name_of_concrete_ident id
            else
              let crate, path = print#namespace_of_concrete_ident id in
              let full_path = crate :: path in
              separate_map (underscore ^^ underscore) utf8string full_path
              ^^ underscore ^^ underscore
              ^^ print#name_of_concrete_ident id

        method! doc_construct_inductive
            : is_record:bool ->
              is_struct:bool ->
              constructor:concrete_ident ->
              base:document option ->
              (global_ident * document) list fn =
          fun ~is_record ~is_struct:_ ~constructor ~base:_ args ->
            if is_record then
              print#concrete_ident constructor
              ^^ iblock parens
                   (separate_map
                      (break 0 ^^ comma)
                      (fun (field, body) -> iblock Fn.id body |> group)
                      args)
            else
              print#concrete_ident constructor
              ^^ iblock parens (separate_map (comma ^^ break 1) snd args)

        method! generic_values : generic_value list fn =
          function
          | [] -> empty
          | values ->
              string "_of" ^^ underscore
              ^^ separate_map underscore print#generic_value values

        method! ty_app f args =
          print#concrete_ident f ^^ print#generic_values args

        method! ty_tuple _ _ = string "bitstring"

        method! local_ident e =
          match String.chop_prefix ~prefix:"impl " e.name with
          | Some name ->
              let name =
                "impl_"
                ^ String.tr ~target:'+' ~replacement:'_'
                    (String.tr ~target:' ' ~replacement:'_' name)
              in
              string name
          | _ -> super#local_ident e

        method! expr ctx e =
          match e.e with
          | App { f = { e = GlobalVar name; _ }; args }
            when Global_ident.eq_name Core__convert__Into__into name ->
              print#ty ctx e.typ ^^ string "_from_bitstring"
              ^^ iblock parens (print#expr ctx (List.hd_exn args))
          | App { f = { e = GlobalVar name; _ }; args }
            when Global_ident.eq_name Rust_primitives__hax__never_to_any name ->
              print#ty ctx e.typ ^^ string "_err()"
          | _ -> (
              match e.typ with
              | TApp { ident }
                when Global_ident.eq_name Core__result__Result ident -> (
                  match e.e with
                  | Construct { constructor; fields }
                    when Global_ident.eq_name Core__result__Result__Ok
                           constructor ->
                      let inner_expr =
                        snd (Option.value_exn (List.hd fields))
                      in
                      let inner_expr_doc = super#expr ctx inner_expr in
                      inner_expr_doc
                  | Construct { constructor; _ }
                    when Global_ident.eq_name Core__result__Result__Err
                           constructor ->
                      print#ty ctx e.typ ^^ string "_err()"
                  | _ -> super#expr ctx e (*This cannot happen*))
              | _ -> super#expr ctx e)

        method! ty : Generic_printer_base.par_state -> ty fn =
          fun ctx ty ->
            match ty with
            | TBool -> print#ty_bool
            | TParam i -> print#local_ident i
            | TInt kind -> print#ty_int kind
            (* Translate known types, no args at the moment *)
            | TApp { ident; args }
              when Global_ident.eq_name Alloc__vec__Vec ident ->
                string "bitstring"
            | TApp { ident; args }
              when Global_ident.eq_name Core__option__Option ident ->
                string "Option"
            | TApp { ident; args }
              when Global_ident.eq_name Core__result__Result ident -> (
                (* print first of args*)
                let result_ok_type = List.hd_exn args in
                match result_ok_type with
                | GType typ -> print#ty ctx typ
                | GConst e -> print#expr ctx e
                | _ -> empty (* Do not tranlsate lifetimes *))
            | TApp { ident; args } -> super#ty ctx ty
            (*(
                match translate_known_name ident ~dict:library_types with
                | Some (_, translation) -> translation
                | None -> super#ty ctx ty)*)
            | _ -> string "bitstring"
      end

    type proverif_aux_info = CrateFns of AST.item list | NoAuxInfo

    include Api (struct
      type aux_info = proverif_aux_info

      let new_print aux = (new print aux :> print_object)
    end)
  end

  let filter_crate_functions (items : AST.item list) =
    List.filter ~f:(fun item -> [%matches? Fn _] item.v) items

  let is_process_read : attrs -> bool =
    Attr_payloads.payloads
    >> List.exists ~f:(fst >> [%matches? Types.ProcessRead])

  let is_process_write : attrs -> bool =
    Attr_payloads.payloads
    >> List.exists ~f:(fst >> [%matches? Types.ProcessWrite])

  let is_process_init : attrs -> bool =
    Attr_payloads.payloads
    >> List.exists ~f:(fst >> [%matches? Types.ProcessInit])

  let is_process item =
    is_process_read item.attrs
    || is_process_write item.attrs
    || is_process_init item.attrs

  module type Subprinter = sig
    val print : AST.item list -> string
  end

  module MkSubprinter (Section : sig
    val banner : string
    val preamble : AST.item list -> string
    val contents : AST.item list -> string
  end) =
  struct
    let hline = "(*****************************************)\n"
    let banner = hline ^ "(* " ^ Section.banner ^ " *)\n" ^ hline ^ "\n"

    let print items =
      banner ^ Section.preamble items ^ Section.contents items ^ "\n\n"
  end

  module Preamble = MkSubprinter (struct
    let banner = "Preamble"

    let preamble items =
      "channel c.\n\n\
       fun construct_fail() : bitstring\n\
       reduc construct_fail() = fail.\n\n\
       type Option.\n\
       fun Some(bitstring): Option [data].\n\
       fun None(): Option [data].\n\
       letfun Option_err() = let x = construct_fail() in None().\n\n\
       const empty: bitstring.\n\
       letfun bitstring_default() = empty.\n\
       letfun bitstring_err() = let x = construct_fail() in \
       bitstring_default().\n\n\
       letfun nat_default() = 0.\n\
       fun nat_to_bitstring(nat): bitstring.\n\n\
       letfun bool_default() = false.\n"

    let contents items = ""
  end)

  module DataTypes = MkSubprinter (struct
    let banner = "Types and Constructors"
    let preamble items = ""

    let filter_data_types items =
      List.filter ~f:(fun item -> [%matches? Type _] item.v) items

    let contents items =
      let contents, _ = Print.items NoAuxInfo (filter_data_types items) in
      contents
  end)

  module Letfuns = MkSubprinter (struct
    let banner = "Functions"
    let preamble items = ""

    let contents items =
      let process_letfuns, pure_letfuns =
        List.partition_tf ~f:is_process (filter_crate_functions items)
      in
      let pure_letfuns_print, _ =
        Print.items (CrateFns (filter_crate_functions items)) pure_letfuns
      in
      let process_letfuns_print, _ =
        Print.items (CrateFns (filter_crate_functions items)) process_letfuns
      in
      pure_letfuns_print ^ process_letfuns_print
  end)

  module Processes = MkSubprinter (struct
    let banner = "Processes"
    let preamble items = ""
    let process_filter item = [%matches? Fn _] item.v && is_process item

    let contents items =
      let contents, _ =
        Print.items NoAuxInfo (List.filter ~f:process_filter items)
      in
      contents
  end)

  module Toplevel = MkSubprinter (struct
    let banner = "Top-level process"
    let preamble items = "process\n    0\n"
    let contents items = ""
  end)
end

let translate m (bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  let (module M : MAKE) =
    (module Make (struct
      let options = bo
    end))
  in
  let lib_contents =
    M.Preamble.print items ^ M.DataTypes.print items ^ M.Letfuns.print items
    ^ M.Processes.print items
  in
  let analysis_contents = M.Toplevel.print items in
  let lib_file =
    Types.{ path = "lib.pvl"; contents = lib_contents; sourcemap = None }
  in
  let analysis_file =
    Types.
      { path = "analysis.pv"; contents = analysis_contents; sourcemap = None }
  in
  [ lib_file; analysis_file ]

open Phase_utils
module DepGraph = Dependencies.Make (InputLanguage)
module DepGraphR = Dependencies.Make (Features.Rust)

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.Unsafe(Features.Rust)
  |> Phases.Reject.RawOrMutPointer
  |> Phases.Transform_hax_lib_inline
  |> Phases.Simplify_question_marks
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_for_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
  |> Phases.Drop_references
  |> Phases.Trivialize_assign_lhs
  |> Side_effect_utils.Hoist
  |> Phases.Simplify_match_return
  |> Phases.Drop_needless_returns
  |> Phases.Local_mutation
  |> Phases.Reject.Continue
  |> Phases.Reject.Dyn
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
