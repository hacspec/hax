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
        let construct_base = reject
        let monadic_action = reject
        let monadic_binding = reject
        let block = reject
        let metadata = Phase_reject.make_metadata (NotInBackendLang ProVerif)
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module BackendOptions = Backend.UnitBackendOptions
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

module Print = struct
  module GenericPrint =
    Generic_printer.Make (InputLanguage) (U.Concrete_ident_view)

  open Generic_printer_base.Make (InputLanguage)
  open PPrint

  let iblock f = group >> jump 2 0 >> terminate (break 0) >> f >> group

  (* TODO: Give definitions for core / known library functions, cf issues #447, #448 *)
  let library_functions :
      (Concrete_ident_generated.name * (AST.expr list -> document)) list =
    [
      (* Core dependencies *)
      (* core::clone::Clone_f_clone *)
      ( Core__clone__Clone__clone,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::cmp::PartialEq::eq *)
      ( Core__cmp__PartialEq__eq,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::cmp::PartialEq_f_ne *)
      ( Core__cmp__PartialEq__ne,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::cmp::PartialOrd::lt *)
      ( Core__cmp__PartialOrd__lt,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::ops::arith::Add::add *)
      ( Core__ops__arith__Add__add,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::ops::arith::Sub::sub *)
      ( Core__ops__arith__Sub__sub,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::option::Option_Option_None_c *)
      ( Core__option__Option__None,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::option::Option_Option_Some_c *)
      ( Core__option__Option__Some,
        fun args -> string "PLACEHOLDER_library_function" );
      (* core::result::impl__map_err *)
      ( Core__result__Impl__map_err,
        fun args -> string "PLACEHOLDER_library_function" );
      (* Crypto dependencies *)

      (* hax_lib_protocol::cal::hash *)
      ( Hax_lib_protocol__cal__hash,
          fun args -> string "PLACEHOLDER_library_function" );
      (* hax_lib_protocol::cal::hmac *)
      (Hax_lib_protocol__cal__hmac,
         fun args -> string "PLACEHOLDER_library_function" );
      (* hax_lib_protocol::cal::aead_decrypt *)
      (Hax_lib_protocol__cal__aead_decrypt,
         fun args -> string "PLACEHOLDER_library_function" );
        (* hax_lib_protocol::cal::aead_encrypt *)
      (Hax_lib_protocol__cal__aead_encrypt,
         fun args -> string "PLACEHOLDER_library_function" );

  (* hax_lib_protocol::cal::dh_scalar_multiply *)
      (Hax_lib_protocol__cal__dh_scalar_multiply,         fun args -> string "PLACEHOLDER_library_function" );

      (* hax_lib_protocol::cal::dh_scalar_multiply_base *)
      (Hax_lib_protocol__cal__dh_scalar_multiply_base,         fun args -> string "PLACEHOLDER_library_function" );

      (* hax_lib_protocol::cal::impl__DHScalar__from_bytes *)
      (Hax_lib_protocol__cal__Impl__from_bytes,         fun args -> string "PLACEHOLDER_library_function" );

      (* hax_lib_protocol::cal::impl__DHElement__from_bytes *)
      (Hax_lib_protocol__cal__Impl_1__from_bytes,         fun args -> string "PLACEHOLDER_library_function" );

      (* hax_lib_protocol::cal::impl__AEADKey__from_bytes *)
      (Hax_lib_protocol__cal__Impl_4__from_bytes,         fun args -> string "PLACEHOLDER_library_function" );

      (* hax_lib_protocol::cal::impl__AEADIV__from_bytes *)
      (Hax_lib_protocol__cal__Impl_5__from_bytes,         fun args -> string "PLACEHOLDER_library_function" );

(* hax_lib_protocol::cal::impl__AEADTag__from_bytes *)
(Hax_lib_protocol__cal__Impl_6__from_bytes,         fun args -> string "PLACEHOLDER_library_function" );

    ]

  let library_constructors :
      (Concrete_ident_generated.name
      * ((global_ident * AST.expr) list -> document))
      list =
    [
      ( Core__option__Option__Some,
        fun args -> string "PLACEHOLDER_library_constructor" );
      ( Core__option__Option__None,
        fun args -> string "PLACEHOLDER_library_constructor" );
      (Core__ops__range__Range, fun args -> string "PLACEHOLDER_library_constructor" );
      (* hax_lib_protocol::cal::(HashAlgorithm_HashAlgorithm_Sha256_c *)
      (Hax_lib_protocol__cal__HashAlgorithm__Sha256,        fun args -> string "PLACEHOLDER_library_constructor" );

      (* hax_lib_protocol::cal::DHGroup_DHGroup_X25519_c *)
      (Hax_lib_protocol__cal__DHGroup__X25519,        fun args -> string "PLACEHOLDER_library_constructor" );

        (* hax_lib_protocol::cal::AEADAlgorithm_AEADAlgorithm_Chacha20Poly1305_c *)
       (Hax_lib_protocol__cal__AEADAlgorithm__Chacha20Poly1305,        fun args -> string "PLACEHOLDER_library_constructor" );

      (* hax_lib_protocol::cal::HMACAlgorithm_HMACAlgorithm_Sha256_c *)
       (Hax_lib_protocol__cal__HMACAlgorithm__Sha256,        fun args -> string "PLACEHOLDER_library_constructor" );

    ]

  let library_types : (Concrete_ident_generated.name * document) list =
    [
      (* hax_lib_protocol::cal::(t_DHScalar *)
      (Hax_lib_protocol__cal__DHScalar,        string "PLACEHOLDER_library_type" );
      (Core__option__Option, string "PLACEHOLDER_library_type");
    ]

  let assoc_known_name name (known_name, _) =
    Global_ident.eq_name known_name name

  let translate_known_function fname args =
    (List.find_exn ~f:(assoc_known_name fname) library_functions |> snd) args

  let translate_known_constructor cname fields =
    (List.find_exn ~f:(assoc_known_name cname) library_constructors |> snd)
      fields

  let translate_known_type tname =
    List.find_exn ~f:(assoc_known_name tname) library_types |> snd

  let is_known_function fname =
    List.exists ~f:(assoc_known_name fname) library_functions

  let is_known_constructor cname =
    List.exists ~f:(assoc_known_name cname) library_constructors

  let is_known_type tname =
    List.exists ~f:(assoc_known_name tname) library_types

  class print aux =
    object (print)
      inherit GenericPrint.print as super
      method ty_bool = string "bool"
      method ty_int _ = string "bitstring"

      method! expr' : Generic_printer_base.par_state -> expr' fn =
        fun ctx e ->
          let wrap_parens =
            group
            >> match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock braces
          in
          match e with
          (* Translate known functions *)
          | App { f = { e = GlobalVar n; _ }; args } when is_known_function n ->
              translate_known_function n args
          (* Translate known constructors *)
          | Construct { constructor; fields }
            when is_known_constructor constructor ->
              translate_known_constructor constructor fields
          (* Desugared `?` operator *)
          | Match
              {
                scrutinee =
                  { e = App { f = { e = GlobalVar n; _ }; args = [ expr ] }; _ };
                arms = _;
              }
          (*[@ocamlformat "disable"]*)
            when Global_ident.eq_name Core__ops__try_trait__Try__branch n ->
              super#expr' ctx expr.e
          | Construct { constructor; fields; _ }
            when Global_ident.eq_name Core__result__Result__Ok constructor ->
              super#expr' ctx (snd (Option.value_exn (List.hd fields))).e
          | Construct { constructor; _ }
            when Global_ident.eq_name Core__result__Result__Err constructor ->
              string "fail"
          | _ -> super#expr' ctx e

      method! item' item =
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
                print#concrete_ident x ^^ string ": " ^^ print#ty_at Param_typ y)
              fun_args
          in
          let fun_args_names =
            separate_map
              (comma ^^ break 1)
              (fst3 >> fun x -> print#concrete_ident x)
              fun_args
          in
          let fun_args_types =
            separate_map
              (comma ^^ break 1)
              (snd3 >> print#ty_at Param_typ)
              fun_args
          in
          let constructor_name = print#concrete_ident constructor.name in

          let fun_line =
            string "fun" ^^ space ^^ constructor_name
            ^^ iblock parens fun_args_types
            ^^ string ": "
            ^^ print#concrete_ident base_name
            ^^ dot
          in
          let reduc_line =
            string "reduc forall " ^^ iblock Fn.id fun_args_full ^^ semi
          in
          let build_accessor (ident, ty, attr) =
            string "accessor" ^^ underscore ^^ print#concrete_ident ident
            ^^ iblock parens (constructor_name ^^ iblock parens fun_args_names)
            ^^ blank 1 ^^ equals ^^ blank 1 ^^ print#concrete_ident ident
          in
          let reduc_lines =
            separate_map (dot ^^ hardline)
              (fun arg -> reduc_line ^^ nest 4 (hardline ^^ build_accessor arg))
              fun_args
          in
          fun_line ^^ hardline ^^ reduc_lines
          ^^ if reduc_lines == empty then empty else dot
        in
        match item with
        (* `fn`s are transformed into `letfun` process macros. *)
        | Fn { name; generics; body; params } ->
            let params_string =
              iblock parens (separate_map (comma ^^ break 1) print#param params)
            in
            string "letfun" ^^ space
            ^^ align
                 (print#concrete_ident name ^^ params_string ^^ space ^^ equals
                ^^ hardline
                 ^^ print#expr_at Item_Fn_body body
                 ^^ dot)
        (* `struct` definitions are transformed into simple constructors and `reduc`s for accessing fields. *)
        | Type { name; generics; variants; is_struct } ->
            let type_line =
              string "type " ^^ print#concrete_ident name ^^ dot
            in
            let type_converter_line =
              string "fun " ^^ print#concrete_ident name
              ^^ string "_to_bitstring"
              ^^ iblock parens (print#concrete_ident name)
              ^^ string ": bitstring [typeConverter]."
            in
            if is_struct then
              let struct_constructor = List.hd variants in
              match struct_constructor with
              | None -> empty
              | Some constructor ->
                  type_line ^^ hardline ^^ type_converter_line ^^ hardline
                  ^^ fun_and_reduc name constructor
            else
              type_line ^^ hardline ^^ type_converter_line ^^ hardline
              ^^ separate_map (hardline ^^ hardline)
                   (fun variant -> fun_and_reduc name variant)
                   variants
        | _ -> empty

      method! expr_let : lhs:pat -> rhs:expr -> expr fn =
        fun ~lhs ~rhs body ->
          string "let" ^^ space
          ^^ iblock Fn.id (print#pat_at Expr_Let_lhs lhs)
          ^^ space ^^ equals ^^ space
          ^^ iblock Fn.id (print#expr_at Expr_Let_rhs rhs)
          ^^ space ^^ string "in" ^^ hardline
          ^^ (print#expr_at Expr_Let_body body |> group)

      method! doc_construct_inductive
          : is_record:bool ->
            is_struct:bool ->
            constructor:concrete_ident ->
            base:document option ->
            (global_ident * document) list fn =
        fun ~is_record ~is_struct:_ ~constructor ~base:_ args ->
          if is_record then
            string "t_"
            (* FIXME: How do I get at the ident from the struct definition instead? *)
            ^^ print#concrete_ident constructor
            ^^ iblock parens
                 (separate_map
                    (break 0 ^^ comma)
                    (fun (field, body) -> iblock Fn.id body |> group)
                    args)
          else
            print#concrete_ident constructor
            ^^ iblock parens (separate_map (comma ^^ break 1) snd args)



      method ty : Generic_printer_base.par_state -> ty fn =
        fun ctx ty ->
          match ty with
          | TBool -> print#ty_bool
          | TParam i -> print#local_ident i
          (* Translate known types, no args at the moment *)
          | TApp { ident } when is_known_type ident ->
              translate_known_type ident
          | TApp _ -> super#ty ctx ty
          | _ -> string "bitstring"

      method! literal : Generic_printer_base.literal_ctx -> literal fn =
        fun _ctx -> function
          | Int { value; negative; _ } ->
              string "int2bitstring"
              ^^ iblock parens
                   (string value |> precede (if negative then minus else empty))
          | Bool b -> OCaml.bool b
          | _ ->
              Error.raise
                {
                  kind =
                    ExplicitRejection
                      { reason = "Literal unsupported by ProVerif backend." };
                  span = current_span;
                }
    end

  type proverif_aux_info = AstItems of AST.item list | NoAuxInfo

  include Api (struct
    type aux_info = proverif_aux_info

    let new_print aux = (new print aux :> print_object)
  end)
end

let filter_crate_functions (items : AST.item list) =
  List.filter ~f:(fun item -> [%matches? Fn _] item.v) items

let is_process_read : attrs -> bool =
  Attr_payloads.payloads >> List.exists ~f:(fst >> [%matches? Types.ProcessRead])

let is_process_write : attrs -> bool =
  Attr_payloads.payloads
  >> List.exists ~f:(fst >> [%matches? Types.ProcessWrite])

let is_process_init : attrs -> bool =
  Attr_payloads.payloads >> List.exists ~f:(fst >> [%matches? Types.ProcessInit])

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
  let preamble items = "channel c.\nfun int2bitstring(nat): bitstring.\n"
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
    let pure_letfuns_print, _ = Print.items NoAuxInfo pure_letfuns in
    let process_letfuns_print, _ = Print.items NoAuxInfo process_letfuns in
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

let translate m (bo : BackendOptions.t) (items : AST.item list) :
    Types.file list =
  let contents =
    Preamble.print items ^ DataTypes.print items ^ Letfuns.print items
    ^ Processes.print items ^ Toplevel.print items
  in
  let file = Types.{ path = "output.pv"; contents } in
  [ file ]

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
  |> Side_effect_utils.Hoist
  |> Phases.Local_mutation
  |> Phases.Reject.Continue
  |> Phases.Reconstruct_question_marks
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
