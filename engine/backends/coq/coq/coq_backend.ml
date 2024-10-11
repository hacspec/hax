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
             and type while_loop = Features.Off.while_loop
             and type for_index_loop = Features.Off.for_index_loop
             and type quote = Features.Off.quote
             and type state_passing_loop = Features.Off.state_passing_loop
             and type fold_like_loop = Features.Off.fold_like_loop
             and type dyn = Features.Off.dyn
             and type match_guard = Features.Off.match_guard
             and type trait_item_default = Features.Off.trait_item_default
             and type unsafe = Features.Off.unsafe) =
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

module BackendOptions = Backend.UnitBackendOptions
module CoqNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (CoqNamePolicy)

module CoqLibrary : Library = struct
  module Notation = struct
    let int_repr (x : string) (i : string) : string =
      "(@repr" ^ " " ^ "WORDSIZE" ^ x ^ " " ^ i ^ ")"

    let type_str : string = "Type"
    let bool_str : string = "bool"
    let unit_str : string = "unit"
  end
end

module C = Coq (CoqLibrary)
open Ast

module Make
    (F : Features.T)
    (Default : sig
      val default : string -> string
    end) =
struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  module Base = Generic_printer.Make (F)
  open PPrint

  let default_string_for s = "TODO: please implement the method `" ^ s ^ "`"
  let default_document_for = default_string_for >> string
  let any_number_of x = parens x ^^ string "*"
  let option_of x = parens x ^^ string "?"
  let either_of x = parens (separate (space ^^ string "|" ^^ space) x)
  let symbol_of x = string "\"" ^^ x ^^ string "\""
  let symbol_str x = string "\"" ^^ string x ^^ string "\""
  let symbol_colon = symbol_of colon
  let symbol_semi = symbol_of semi
  let symbol_comma = symbol_of comma

  let symbol_parens x =
    string "\""
    ^^ parens (string "\"" ^^ space ^^ x ^^ space ^^ string "\"")
    ^^ string "\""

  let symbol_brackets x =
    string "\""
    ^^ brackets (string "\"" ^^ space ^^ x ^^ space ^^ string "\"")
    ^^ string "\""

  let symbol_braces x =
    string "\""
    ^^ braces (string "\"" ^^ space ^^ x ^^ space ^^ string "\"")
    ^^ string "\""

  let features l =
    parens
      (string "%features:" ^^ space
      ^^ separate_map (space ^^ comma ^^ space) (fun x -> string x) l)
    ^^ space

  (* let code_parens x = string "1;31m" ^ parens ( x ^^ string "\x1b[1;31m" ) ^^ string "\x1b[0m" *)

  class printer =
    object
      inherit Base.base

      (* BEGIN GENERATED *)
      method arm ~arm:_ ~span:_ = default_document_for "arm"

      method arm' ~super:_ ~arm_pat:_ ~body:_ ~guard:_ =
        default_document_for "arm'"

      method attrs _x1 = default_document_for "attrs"

      method binding_mode_ByRef _x1 _x2 =
        default_document_for "binding_mode_ByRef"

      method binding_mode_ByValue = default_document_for "binding_mode_ByValue"
      method borrow_kind_Mut _x1 = default_document_for "borrow_kind_Mut"
      method borrow_kind_Shared = default_document_for "borrow_kind_Shared"
      method borrow_kind_Unique = default_document_for "borrow_kind_Unique"

      method common_array x1 =
        either_of
          [
            symbol_brackets
              (any_number_of (string "expr" ^^ space ^^ symbol_comma));
            symbol_brackets
              (string "expr" ^^ space ^^ symbol_str ";" ^^ space ^^ string "int");
          ]

      method dyn_trait_goal ~trait:_ ~non_self_args:_ =
        default_document_for "dyn_trait_goal"

      method error_expr _x1 = default_document_for "error_expr"
      method error_item _x1 = default_document_for "error_item"
      method error_pat _x1 = default_document_for "error_pat"
      method expr ~e ~span:_ ~typ:_ = e#p

      method expr'_AddressOf ~super:_ ~mut ~e:_ ~witness:_ =
        match mut with
        | Immutable -> symbol_str "*" ^^ space ^^ string "expr"
        | Mutable _ ->
            features [ "mutable_pointer" ]
            ^^ symbol_str "*mut" ^^ space ^^ string "expr"

      method expr'_App_application ~super:_ ~f:_ ~args:_ ~generics:_ =
        default_document_for "expr'_App_application"

      method expr'_App_constant ~super:_ ~constant:_ ~generics:_ =
        default_document_for "expr'_App_constant"

      method expr'_App_field_projection ~super:_ ~field:_ ~e:_ =
        default_document_for "expr'_App_field_projection"

      method expr'_App_tuple_projection ~super:_ ~size:_ ~nth:_ ~e:_ =
        default_document_for "expr'_App_tuple_projection"

      method expr'_Ascription ~super:_ ~e:_ ~typ:_ =
        string "expr" ^^ space ^^ symbol_colon ^^ space ^^ string "ty"

      method expr'_Assign ~super:_ ~lhs:_ ~e:_ ~witness:_ =
        string "mut var" ^^ space ^^ symbol_str "=" ^^ space ^^ string "expr"

      method expr'_Block ~super:_ ~e:_ ~safety_mode:_ ~witness:_ =
        features [ "block" ] ^^ string "modifiers" ^^ space
        ^^ symbol_braces (string "expr")

      method expr'_Borrow ~super:_ ~kind:_ ~e:_ ~witness:_ =
        features [ "reference" ] ^^ symbol_str "&" ^^ space ^^ string "expr"

      method expr'_Break ~super:_ ~e:_ ~label:_ ~witness:_ =
        features [ "break"; "loop" ] ^^ symbol_str "break"

      method expr'_Closure ~super:_ ~params:_ ~body:_ ~captures:_ =
        symbol_str "|" ^^ space ^^ string "param" ^^ space ^^ symbol_str "|"
        ^^ space ^^ string "expr"

      method expr'_Construct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ ~base:_ =
        string "constructor" ^^ space ^^ any_number_of (string "expr")

      method expr'_Construct_tuple ~super:_ ~components:_ =
        default_document_for "expr'_Construct_tuple"

      method expr'_Continue ~super:_ ~e:_ ~label:_ ~witness:_ =
        features [ "continue"; "loop" ] ^^ symbol_str "continue"

      method expr'_EffectAction ~super:_ ~action:_ ~argument:_ =
        features [ "monadic_action" ]
        ^^ default_document_for "expr'_EffectAction"

      method expr'_GlobalVar ~super:_ _x2 = string "global_var"

      method expr'_If ~super:_ ~cond:_ ~then_:_ ~else_:_ =
        symbol_str "if" ^^ space ^^ string "expr" ^^ space
        ^^ symbol_braces (string "expr")
        ^^ space
        ^^ option_of
             (symbol_str "else" ^^ space ^^ symbol_braces (string "expr"))

      method expr'_Let ~super:_ ~monadic:_ ~lhs:_ ~rhs:_ ~body:_ =
        symbol_str "let" ^^ space ^^ string "pat" ^^ space
        ^^ option_of (symbol_colon ^^ space ^^ string "ty")
        ^^ space ^^ symbol_str ":=" ^^ space ^^ string "expr" ^^ space
        ^^ symbol_semi

      method expr'_Literal ~super:_ _x2 = string "literal"
      method expr'_LocalVar ~super:_ _x2 = string "local_var"

      method expr'_Loop ~super:_ ~body:_ ~kind:_ ~state:_ ~label:_ ~witness:_ =
        (* Type of loop *)
        features [ "loop" ] ^^ default_document_for "expr'_Loop"

      method expr'_MacroInvokation ~super:_ ~macro:_ ~args:_ ~witness:_ =
        string "macro_name" ^^ space ^^ symbol_str "!" ^^ space
        ^^ symbol_parens (string "macro_args")

      method expr'_Match ~super:_ ~scrutinee:_ ~arms:_ =
        symbol_str "match" ^^ space ^^ string "expr" ^^ space
        ^^ symbol_braces
             (any_number_of
                (any_number_of (symbol_str "|" ^^ space ^^ string "pat")
                ^^ space ^^ symbol_str "=>" ^^ space
                ^^ either_of
                     [
                       string "expr" ^^ space ^^ symbol_comma;
                       symbol_braces (string "<expr>");
                     ]))

      method expr'_QuestionMark ~super:_ ~e:_ ~return_typ:_ ~witness:_ =
        features [ "question_mark" ] ^^ string "expr" ^^ space ^^ symbol_str "?"

      method expr'_Quote ~super:_ _x2 = default_document_for "expr'_Quote"

      method expr'_Return ~super:_ ~e:_ ~witness:_ =
        features [ "early_exit" ] ^^ symbol_str "return" ^^ space
        ^^ string "expr"

      method field_pat ~field:_ ~pat:_ = default_document_for "field_pat"

      method generic_constraint_GCLifetime _x1 _x2 =
        default_document_for "generic_constraint_GCLifetime"

      method generic_constraint_GCProjection _x1 =
        default_document_for "generic_constraint_GCProjection"

      method generic_constraint_GCType _x1 =
        default_document_for "generic_constraint_GCType"

      method generic_param ~ident:_ ~span:_ ~attrs:_ ~kind:_ =
        default_document_for "generic_param"

      method generic_param_kind_GPConst ~typ:_ =
        default_document_for "generic_param_kind_GPConst"

      method generic_param_kind_GPLifetime ~witness:_ =
        default_document_for "generic_param_kind_GPLifetime"

      method generic_param_kind_GPType ~default:_ =
        default_document_for "generic_param_kind_GPType"

      method generic_value_GConst _x1 =
        default_document_for "generic_value_GConst"

      method generic_value_GLifetime ~lt:_ ~witness:_ =
        default_document_for "generic_value_GLifetime"

      method generic_value_GType _x1 =
        default_document_for "generic_value_GType"

      method generics ~params:_ ~constraints:_ = default_document_for "generics"
      method guard ~guard:_ ~span:_ = default_document_for "guard"

      method guard'_IfLet ~super:_ ~lhs:_ ~rhs:_ ~witness:_ =
        default_document_for "guard'_IfLet"

      method impl_expr ~kind:_ ~goal:_ = default_document_for "impl_expr"

      method impl_expr_kind_Builtin _x1 =
        default_document_for "impl_expr_kind_Builtin"

      method impl_expr_kind_Concrete _x1 =
        default_document_for "impl_expr_kind_Concrete"

      method impl_expr_kind_Dyn = default_document_for "impl_expr_kind_Dyn"

      method impl_expr_kind_ImplApp ~impl:_ ~args:_ =
        default_document_for "impl_expr_kind_ImplApp"

      method impl_expr_kind_LocalBound ~id:_ =
        default_document_for "impl_expr_kind_LocalBound"

      method impl_expr_kind_Parent ~impl:_ ~ident:_ =
        default_document_for "impl_expr_kind_Parent"

      method impl_expr_kind_Projection ~impl:_ ~item:_ ~ident:_ =
        default_document_for "impl_expr_kind_Projection"

      method impl_expr_kind_Self = default_document_for "impl_expr_kind_Self"
      method impl_ident ~goal:_ ~name:_ = default_document_for "impl_ident"

      method impl_item ~ii_span:_ ~ii_generics:_ ~ii_v:_ ~ii_ident:_ ~ii_attrs:_
          =
        default_document_for "impl_item"

      method impl_item'_IIFn ~body:_ ~params:_ =
        default_document_for "impl_item'_IIFn"

      method impl_item'_IIType ~typ:_ ~parent_bounds:_ =
        default_document_for "impl_item'_IIType"

      method item ~v ~span:_ ~ident:_ ~attrs:_ =
        v#p (* default_document_for "item" *)

      method item'_Alias ~super:_ ~name:_ ~item:_ =
        default_document_for "item'_Alias"

      method item'_Fn ~super:_ ~name:_ ~generics:_ ~body:_ ~params:_ ~safety:_ =
        (* TODOD: safe, pub, const, pub(crate) *)
        string "modifiers" ^^ space ^^ symbol_str "fn" ^^ space
        ^^ string "ident" ^^ space
        ^^ symbol_parens
             (any_number_of
                (string "pat" ^^ space ^^ symbol_colon ^^ string "ty" ^^ space
               ^^ symbol_comma))
        ^^ space
        ^^ option_of (symbol_colon ^^ string "ty")
        ^^ space
        ^^ symbol_braces (string "expr")

      method item'_HaxError ~super:_ _x2 = default_document_for "item'_HaxError"

      method item'_IMacroInvokation ~super:_ ~macro:_ ~argument:_ ~span:_
          ~witness:_ =
        features [ "macro" ]
        ^^ either_of
             [
               string "public_nat_mod";
               string "bytes";
               string "public_bytes";
               string "array";
               string "unsigned_public_integer";
             ]

      method item'_Impl ~super:_ ~generics:_ ~self_ty:_ ~of_trait:_ ~items:_
          ~parent_bounds:_ ~safety:_ =
        symbol_str "impl" ^^ space
        ^^ option_of
             (symbol_str "<" ^^ space
             ^^ any_number_of (string "generics" ^^ space ^^ symbol_comma)
             ^^ space ^^ symbol_str ">")
        ^^ space ^^ string "ident" ^^ space ^^ symbol_str "for" ^^ space
        ^^ string "ty" ^^ space
        ^^ symbol_braces (any_number_of (string "impl_item"))

      method item'_NotImplementedYet =
        default_document_for "item'_NotImplementedYet"

      method item'_Quote ~super:_ _x2 =
        features [ "quote" ] ^^ default_document_for "item'_Quote"

      method item'_Trait ~super:_ ~name:_ ~generics:_ ~items:_ ~safety:_ =
        symbol_str "trait" ^^ space ^^ string "ident" ^^ space
        ^^ symbol_braces (any_number_of (string "trait_item"))

      method item'_TyAlias ~super:_ ~name:_ ~generics:_ ~ty:_ =
        symbol_str "type" ^^ space ^^ string "ident" ^^ space ^^ symbol_str "="
        ^^ space ^^ string "ty"

      method item'_Type ~super:_ ~name:_ ~generics:_ ~variants:_ ~is_struct =
        (* TODO globality *)
        if is_struct then
          symbol_str "struct" ^^ space ^^ string "ident" ^^ space
          ^^ symbol_str "=" ^^ space
          ^^ symbol_braces
               (any_number_of
                  (string "ident" ^^ space ^^ symbol_colon ^^ space
                 ^^ string "ty" ^^ space ^^ symbol_comma))
        else
          symbol_str "enum" ^^ space ^^ string "ident" ^^ space
          ^^ symbol_str "=" ^^ space
          ^^ symbol_braces
               (any_number_of
                  (string "ident" ^^ space
                  ^^ option_of (symbol_parens (any_number_of (string "ty")))
                  ^^ space ^^ symbol_comma))

      method item'_Use ~super:_ ~path:_ ~is_external:_ ~rename:_ =
        symbol_str "use" ^^ space ^^ string "path" ^^ space ^^ symbol_semi

      method lhs_LhsArbitraryExpr ~e:_ ~witness:_ =
        default_document_for "lhs_LhsArbitraryExpr"

      method lhs_LhsArrayAccessor ~e:_ ~typ:_ ~index:_ ~witness:_ =
        default_document_for "lhs_LhsArrayAccessor"

      method lhs_LhsFieldAccessor_field ~e:_ ~typ:_ ~field:_ ~witness:_ =
        default_document_for "lhs_LhsFieldAccessor_field"

      method lhs_LhsFieldAccessor_tuple ~e:_ ~typ:_ ~nth:_ ~size:_ ~witness:_ =
        default_document_for "lhs_LhsFieldAccessor_tuple"

      method lhs_LhsLocalVar ~var:_ ~typ:_ =
        default_document_for "lhs_LhsLocalVar"

      method literal_Bool _x1 =
        either_of [ symbol_str "true"; symbol_str "false" ]

      method literal_Char _x1 =
        symbol_str "'" ^^ space ^^ string "char" ^^ space ^^ symbol_str "'"

      method literal_Float ~value:_ ~negative:_ ~kind:_ = string "float"
      method literal_Int ~value:_ ~negative:_ ~kind:_ = string "int"

      method literal_String _x1 =
        symbol_str "\"" ^^ space ^^ string "string" ^^ space ^^ symbol_str "\""

      method loop_kind_ForIndexLoop ~start:_ ~end_:_ ~var:_ ~var_typ:_
          ~witness:_ =
        default_document_for "loop_kind_ForIndexLoop"

      method loop_kind_ForLoop ~pat:_ ~it:_ ~witness:_ =
        default_document_for "loop_kind_ForLoop"

      method loop_kind_UnconditionalLoop =
        default_document_for "loop_kind_UnconditionalLoop"

      method loop_kind_WhileLoop ~condition:_ ~witness:_ =
        default_document_for "loop_kind_WhileLoop"

      method loop_state ~init:_ ~bpat:_ ~witness:_ =
        default_document_for "loop_state"

      method modul _x1 = default_document_for "modul"

      method param ~pat:_ ~typ:_ ~typ_span:_ ~attrs:_ =
        default_document_for "param"

      method pat ~p ~span:_ ~typ:_ = p#p

      method pat'_PAscription ~super:_ ~typ:_ ~typ_span:_ ~pat:_ =
        string "pat" ^^ space ^^ symbol_colon

      method pat'_PBinding ~super:_ ~mut:_ ~mode:_ ~var:_ ~typ:_ ~subpat:_ =
        default_document_for "pat'_PBinding"

      method pat'_PConstant ~super:_ ~lit:_ = string "literal"

      method pat'_PConstruct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ =
        string "constructor" ^^ space ^^ string "pat"

      method pat'_PConstruct_tuple ~super:_ ~components:_ =
        default_document_for "pat'_PConstruct_tuple"

      method pat'_PDeref ~super:_ ~subpat:_ ~witness:_ =
        default_document_for "pat'_PDeref"

      method pat'_PWild = symbol_str "_"

      method pat'_POr ~super:_ ~subpats:_ =
        any_number_of (symbol_str "pat" ^^ space ^^ symbol_str "|")
        ^^ space ^^ symbol_str "pat"

      method printer_name = default_string_for "printer_name"

      method projection_predicate ~impl:_ ~assoc_item:_ ~typ:_ =
        default_document_for "projection_predicate"

      method safety_kind_Safe = default_document_for "safety_kind_Safe"
      method safety_kind_Unsafe _x1 = default_document_for "safety_kind_Unsafe"

      method supported_monads_MException _x1 =
        default_document_for "supported_monads_MException"

      method supported_monads_MOption =
        default_document_for "supported_monads_MOption"

      method supported_monads_MResult _x1 =
        default_document_for "supported_monads_MResult"

      method trait_goal ~trait:_ ~args:_ = default_document_for "trait_goal"

      method trait_item ~ti_span:_ ~ti_generics:_ ~ti_v:_ ~ti_ident:_
          ~ti_attrs:_ =
        default_document_for "trait_item"

      method trait_item'_TIDefault ~params:_ ~body:_ ~witness:_ =
        default_document_for "trait_item'_TIDefault"

      method trait_item'_TIFn _x1 = default_document_for "trait_item'_TIFn"
      method trait_item'_TIType _x1 = default_document_for "trait_item'_TIType"

      method ty_TApp_application ~typ:_ ~generics:_ =
        default_document_for "ty_TApp_application"

      method ty_TApp_tuple ~types:_ = default_document_for "ty_TApp_tuple"

      method ty_TArray ~typ:_ ~length:_ =
        symbol_brackets
          (string "ty" ^^ space ^^ symbol_semi ^^ space ^^ string "int")

      method ty_TArrow _x1 _x2 =
        any_number_of (string "ty" ^^ space ^^ symbol_str "->")
        ^^ space ^^ string "ty"

      method ty_TAssociatedType ~impl:_ ~item:_ =
        default_document_for "ty_TAssociatedType"

      method ty_TBool = symbol_str "bool"
      method ty_TChar = symbol_str "char"
      method ty_TDyn ~witness:_ ~goals:_ = default_document_for "ty_TDyn"

      method ty_TFloat _x1 =
        either_of [ symbol_str "f16"; symbol_str "f32"; symbol_str "f64" ]

      method ty_TInt _x1 =
        either_of
          [
            symbol_str "u8";
            symbol_str "u16";
            symbol_str "u32";
            symbol_str "u64";
            symbol_str "u128";
            symbol_str "usize";
          ]

      method ty_TOpaque _x1 = default_document_for "ty_TOpaque"
      method ty_TParam _x1 = default_document_for "ty_TParam"

      method ty_TRawPointer ~witness:_ =
        either_of
          [
            features [ "raw_pointer" ] ^^ symbol_str "*const" ^^ space
            ^^ string "ty";
            features [ "raw_pointer" ] ^^ symbol_str "*mut" ^^ space
            ^^ string "ty";
          ]

      method ty_TRef ~witness:_ ~region:_ ~typ:_ ~mut =
        match mut with
        | Immutable ->
            features [ "reference" ] ^^ string "*" ^^ space ^^ string "expr"
        | Mutable _ ->
            features [ "reference"; "mutable_reference" ]
            ^^ string "*mut" ^^ space ^^ string "expr"

      method ty_TSlice ~witness:_ ~ty:_ =
        features [ "slice" ] ^^ symbol_brackets (string "ty")

      method ty_TStr = symbol_str "str"

      method variant ~name:_ ~arguments:_ ~is_record:_ ~attrs:_ =
        default_document_for "variant"
      (* END GENERATED *)
    end
end

(* TODO: Write quoted expression shallowly, to get a generator for full AST *)
(* ppx_deriving_random, metaquote *)
(* [%expr 1 + [%e some_expr_node]] *)

module HaxCFG = struct
  module MyPrinter =
    Make
      (Features.Full)
      (struct
        let default x = x
      end)

  module AST = Ast.Make (Features.Full)
  open AST

  let print_ast (_ : unit) =
    let my_printer = new MyPrinter.printer in

    let dummy_ident : concrete_ident =
      Concrete_ident.of_name Value Hax_lib__RefineAs__into_checked
    in

    let dummy_literal = String "dummy" in

    let dummy_ty = TBool in

    let dummy_expr : expr =
      { e = Literal dummy_literal; span = Span.dummy (); typ = dummy_ty }
    in
    let dummy_generics : generics = { params = []; constraints = [] } in
    let dummy_global_ident : global_ident = `Concrete dummy_ident in
    let dummy_pat = { p = PWild; span = Span.dummy (); typ = dummy_ty } in
    let dummy_local_ident : local_ident =
      { name = "dummy"; id = Local_ident.mk_id Typ 0 }
    in

    (* print#_do_not_override_lazy_of_item' ~super AstPos_item__v v *)
    let my_literals =
      [
        String "dummy";
        Char 'a';
        Int
          {
            value = "dummy";
            kind = { size = S8; signedness = Unsigned };
            negative = false;
          };
        Float { value = "dummy"; kind = F16; negative = false };
        Bool false;
      ]
    in
    let literal_string =
      "\n\n```ebnf\nliteral ::=\n"
      ^ String.concat ~sep:"\n"
          (List.map
             ~f:(fun literal ->
               let buf = Buffer.create 0 in
               PPrint.ToBuffer.pretty 1.0 80 buf
                 (my_printer#entrypoint_literal literal);
               "| " ^ Buffer.contents buf)
             my_literals)
      ^ "\n```"
    in

    let my_items' : item' list =
      [
        Fn
          {
            name = dummy_ident;
            generics = dummy_generics;
            body = dummy_expr;
            params = [];
            safety = Safe;
          };
        TyAlias { name = dummy_ident; generics = dummy_generics; ty = dummy_ty };
        (* struct *)
        Type
          {
            name = dummy_ident;
            generics = dummy_generics;
            variants = [];
            is_struct = false;
          };
        (* enum *)
        Type
          {
            name = dummy_ident;
            generics = dummy_generics;
            variants = [];
            is_struct = true;
          };
        IMacroInvokation
          {
            macro = dummy_ident;
            argument = "TODO";
            span = Span.dummy ();
            witness = Features.On.macro;
          };
        Trait
          {
            name = dummy_ident;
            generics = dummy_generics;
            items = [];
            safety = Safe;
          };
        Impl
          {
            generics = dummy_generics;
            self_ty = dummy_ty;
            of_trait = (dummy_global_ident, []);
            items = [];
            parent_bounds = [];
            safety = Safe;
          };
        Alias { name = dummy_ident; item = dummy_ident };
        Use { path = []; is_external = false; rename = None };
        Quote { contents = []; witness = Features.On.quote };
        HaxError "dummy";
        NotImplementedYet;
      ]
    in
    let my_items : item list =
      List.map
        ~f:(fun x ->
          { v = x; span = Span.dummy (); ident = dummy_ident; attrs = [] })
        my_items'
    in
    let item_string =
      "\n\n```ebnf\nitem ::=\n"
      ^ String.concat ~sep:"\n"
          (List.map
             ~f:(fun item ->
               let buf = Buffer.create 0 in
               PPrint.ToBuffer.pretty 1.0 80 buf
                 (my_printer#entrypoint_item item);
               "| " ^ Buffer.contents buf)
             my_items)
      ^ "\n```"
    in

    let my_exprs' =
      [
        If { cond = dummy_expr; then_ = dummy_expr; else_ = None };
        (* App { f = dummy_expr; args = []; generic_args = []; bounds_impls = []; trait = None; }; *)
        Literal (String "dummy");
        Array [];
        Construct
          {
            constructor = dummy_global_ident;
            is_record = false;
            is_struct = false;
            fields = [];
            base = None;
          };
        Match { scrutinee = dummy_expr; arms = [] };
        Let
          {
            monadic = None;
            lhs = dummy_pat;
            rhs = dummy_expr;
            body = dummy_expr;
          };
        Block
          { e = dummy_expr; safety_mode = Safe; witness = Features.On.block };
        LocalVar dummy_local_ident;
        GlobalVar dummy_global_ident;
        Ascription { e = dummy_expr; typ = dummy_ty };
        MacroInvokation
          {
            macro = dummy_global_ident;
            args = "dummy";
            witness = Features.On.macro;
          };
        Assign
          {
            lhs = LhsLocalVar { var = dummy_local_ident; typ = dummy_ty };
            e = dummy_expr;
            witness = Features.On.mutable_variable;
          };
        Loop
          {
            body = dummy_expr;
            kind = UnconditionalLoop;
            state = None;
            label = None;
            witness = Features.On.loop;
          };
        Break
          {
            e = dummy_expr;
            label = None;
            witness = (Features.On.break, Features.On.loop);
          };
        Return { e = dummy_expr; witness = Features.On.early_exit };
        QuestionMark
          {
            e = dummy_expr;
            return_typ = dummy_ty;
            witness = Features.On.question_mark;
          };
        Continue
          {
            e = None;
            label = None;
            witness = (Features.On.continue, Features.On.loop);
          };
        Borrow
          { kind = Shared; e = dummy_expr; witness = Features.On.reference };
        AddressOf
          { mut = Immutable; e = dummy_expr; witness = Features.On.raw_pointer };
        AddressOf
          {
            mut = Mutable Features.On.mutable_pointer;
            e = dummy_expr;
            witness = Features.On.raw_pointer;
          };
        Closure { params = []; body = dummy_expr; captures = [] };
        EffectAction
          { action = Features.On.monadic_action; argument = dummy_expr };
        Quote { contents = []; witness = Features.On.quote };
      ]
    in
    let my_exprs =
      List.map
        ~f:(fun x -> { e = x; span = Span.dummy (); typ = dummy_ty })
        my_exprs'
    in
    let expr_string =
      "\n\n```ebnf\nexpr ::=\n"
      ^ String.concat ~sep:"\n"
          (List.map
             ~f:(fun expr ->
               let buf = Buffer.create 0 in
               PPrint.ToBuffer.pretty 1.0 80 buf
                 (my_printer#entrypoint_expr expr);
               "| " ^ Buffer.contents buf)
             my_exprs)
      ^ "\n```"
    in

    let my_tys =
      [
        TBool;
        TChar;
        TInt { size = S8; signedness = Signed };
        TFloat F16;
        TStr;
        (* TApp of { ident : global_ident; args : generic_value list }; *)
        TArray { typ = dummy_ty; length = dummy_expr (* const *) };
        TSlice { witness = Features.On.slice; ty = dummy_ty };
        TRawPointer { witness = Features.On.raw_pointer };
        TRef
          {
            witness = Features.On.reference;
            region = "todo";
            typ = dummy_ty;
            mut = Immutable;
          };
        TRef
          {
            witness = Features.On.reference;
            region = "todo";
            typ = dummy_ty;
            mut = Mutable Features.On.mutable_reference;
          };
        TParam dummy_local_ident;
        TArrow ([], dummy_ty);
        (* TAssociatedType { impl = impl_expr; item : concrete_ident }; *)
        TOpaque dummy_ident;
        TDyn { witness = Features.On.dyn; goals = [] };
      ]
    in
    let ty_string =
      "\n\n```ebnf\nty ::=\n"
      ^ String.concat ~sep:"\n"
          (List.map
             ~f:(fun ty ->
               let buf = Buffer.create 0 in
               PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_ty ty);
               "| " ^ Buffer.contents buf)
             my_tys)
      ^ "\n```"
    in

    let my_pats' =
      [
        PWild;
        PAscription
          { typ = dummy_ty; typ_span = Span.dummy (); pat = dummy_pat };
        PConstruct
          {
            constructor = dummy_global_ident;
            is_record = false;
            is_struct = false;
            fields = [];
          };
        POr { subpats = [ dummy_pat; dummy_pat ] };
        (* Does not render *)
        PArray { args = [] };
        PDeref { subpat = dummy_pat; witness = Features.On.reference };
        PConstant { lit = dummy_literal };
        PBinding
          {
            mut = Mutable Features.On.mutable_variable;
            mode = ByValue;
            var = dummy_local_ident;
            typ = dummy_ty;
            subpat = None;
          };
      ]
    in
    let my_pats =
      List.map
        ~f:(fun x -> { p = x; span = Span.dummy (); typ = dummy_ty })
        my_pats'
    in
    let pat_string =
      "\n\n```ebnf\npat ::=\n"
      ^ String.concat ~sep:"\n"
          (List.map
             ~f:(fun pat ->
               let buf = Buffer.create 0 in
               PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_pat pat);
               "| " ^ Buffer.contents buf)
             my_pats)
      ^ "\n```"
    in

    [
      Types.
        {
          path = "ast_spec.md";
          contents =
            "# Hax CFG" ^ literal_string ^ expr_string ^ ty_string ^ pat_string
            ^ item_string;
          sourcemap = None;
        };
    ]
end

let translate _ _bo _ = HaxCFG.print_ast ()

open Phase_utils

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.Unsafe(Features.Rust)
  |> Phases.Reject.RawOrMutPointer
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_asserts
  |> Phases.Reconstruct_for_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
  |> Phases.Drop_match_guards
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
  |> Phases.Reject.As_pattern
  |> Phases.Reject.Dyn
  |> Phases.Reject.Trait_item_default
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (_bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
