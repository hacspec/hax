open Hax_engine
open Utils
open Base
open Coq_ast

open Ast

include
  Backend.Make
    (Features.Full)
    (struct
      let backend = Diagnostics.Backend.Coq
    end)

module BackendOptions = Backend.UnitBackendOptions

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

  let default_string_for s = "/*" ^ "TODO: please implement the method `" ^ s ^ "`" ^ "*/"
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
    string "/*" ^^ space
    ^^ string "features:" ^^ space
    ^^ separate_map (space ^^ comma ^^ space) (fun x -> string x) l
    ^^ space ^^ string "*/"
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
        either_of [
          symbol_str "&" ^^ space ^^ string "expr" ^^ space ^^ symbol_str "as" ^^ space ^^ symbol_str "&const _";
          features [ "mutable_pointer" ] ^^ symbol_str "&mut" ^^ space ^^ string "expr" ^^ symbol_str "as" ^^ space ^^ symbol_str "&mut _";
        ]

      method _do_not_override_expr'_App ~super ~f ~args ~generic_args ~bounds_impls ~trait =
        string "expr" ^^ space ^^ symbol_parens ( any_number_of (string "expr" ^^ space ^^ symbol_comma) )

      method expr'_App_application ~super:_ ~f:_ ~args:_ ~generics:_ =
        default_document_for "expr'_App_application"

      method expr'_App_constant ~super:_ ~constant:_ ~generics:_ =
        default_document_for "expr'_App_constant"

      method expr'_App_field_projection ~super:_ ~field:_ ~e:_ =
        default_document_for "expr'_App_field_projection"

      method expr'_App_tuple_projection ~super:_ ~size:_ ~nth:_ ~e:_ =
        default_document_for "expr'_App_tuple_projection"

      method expr'_Ascription ~super:_ ~e:_ ~typ:_ =
        string "expr" ^^ space ^^ symbol_str "as" ^^ space ^^ string "ty"

      method expr'_Assign ~super:_ ~lhs:_ ~e:_ ~witness:_ =
        string "lhs" ^^ space ^^ symbol_str "=" ^^ space ^^ string "expr"

      method expr'_Block ~super:_ ~e:_ ~safety_mode:_ ~witness:_ =
        features [ "block" ] ^^ string "modifiers" ^^ space
        ^^ symbol_braces (string "expr")

      method expr'_Borrow ~super:_ ~kind:_ ~e:_ ~witness:_ =
        features [ "reference" ] ^^ symbol_str "&" ^^ space ^^ option_of ( symbol_str "mut" ) ^^ space ^^ string "expr"

      method expr'_Break ~super:_ ~e:_ ~label:_ ~witness:_ =
        features [ "break"; "loop" ] ^^ symbol_str "break" ^^ space ^^ string "expr"

      method expr'_Closure ~super:_ ~params:_ ~body:_ ~captures:_ =
        symbol_str "|" ^^ space ^^ string "param" ^^ space ^^ symbol_str "|"
        ^^ space ^^ string "expr"

      method expr'_Construct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ ~base:_ =
        either_of [
          string "ident" ^^ symbol_parens ( any_number_of ( string "expr" ^^ space ^^ symbol_comma ) );
          string "ident" ^^ symbol_braces ( any_number_of ( string "ident" ^^ space ^^ symbol_colon ^^ string "expr" ^^ space ^^ symbol_semi ) );
          features ["construct_base"] ^^ string "ident" ^^ symbol_braces ( any_number_of ( string "ident" ^^ space ^^ symbol_colon ^^ string "expr" ^^ space ^^ symbol_semi ) ^^ space ^^ symbol_str ".." ^^ space ^^ string "base" );
        ]
        (* string "constructor" ^^ space ^^ any_number_of (string "expr") *)

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
        either_of [
          symbol_str "let" ^^ space ^^ string "pat" ^^ space
          ^^ option_of ( symbol_colon ^^ space ^^ string "ty" )
          ^^ space ^^ symbol_str ":=" ^^ space ^^ string "expr" ^^ space
          ^^ symbol_semi ^^ space ^^ string "expr";
          features ["monadic_binding"] ^^ string "monadic_binding" ^^ space ^^ symbol_str "<" ^^ space ^^ string "monad" ^^ space ^^ symbol_str ">" ^^ space ^^ symbol_parens (
            symbol_str "|" ^^ space ^^ string "pat" ^^ space ^^ symbol_str "|" ^^ space ^^ string "expr"
            ^^ symbol_comma
            ^^ string "expr";
          )
        ]

      method expr'_Literal ~super:_ _x2 = string "literal"
      method expr'_LocalVar ~super:_ _x2 = string "local_var"

      method expr'_Loop ~super:_ ~body:_ ~kind:_ ~state:_ ~label:_ ~witness:_ =
        (* Type of loop *)
        either_of [
          features [ "loop" ] ^^ symbol_str "loop" ^^ space ^^ symbol_braces( string "expr" );
          features [ "loop"; "while_loop" ] ^^ symbol_str "while" ^^ space ^^ symbol_parens( string "expr" ) ^^ space ^^ symbol_braces( string "expr" );
          features [ "loop"; "for_loop" ] ^^ symbol_str "for" ^^ space ^^ symbol_parens( string "pat" ^^ space ^^ symbol_str "in" ^^ space ^^ string "expr" ) ^^ space ^^ symbol_braces ( string "expr" );
          features [ "loop"; "for_index_loop" ] ^^ symbol_str "for" ^^ space ^^ symbol_parens( symbol_str "let" ^^ space ^^ string "ident" ^^ space ^^ symbol_str "in" ^^ space ^^ string "expr" ^^ space ^^ symbol_str ".." ^^ space ^^ string "expr" ) ^^ space ^^ symbol_braces ( string "expr" );
        ]

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
                       symbol_braces (string "expr");
                     ]))

      method expr'_QuestionMark ~super:_ ~e:_ ~return_typ:_ ~witness:_ =
        features [ "question_mark" ] ^^ string "expr" ^^ space ^^ symbol_str "?"

      method expr'_Quote ~super:_ _x2 = default_document_for "expr'_Quote"

      method expr'_Return ~super:_ ~e:_ ~witness:_ =
        features [ "early_exit" ] ^^ symbol_str "return" ^^ space ^^ string "expr"

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
        features ["reference"] ^^ symbol_str "&" ^^ space ^^ string "pat"

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
        any_number_of (string "ty" ^^ space ^^ symbol_comma) (* TODO uses top level implementation ? *)

      method ty_TApp_tuple ~types:_ = default_document_for "ty_TApp_tuple"

      method ty_TArray ~typ:_ ~length:_ =
        symbol_brackets
          (string "ty" ^^ space ^^ symbol_semi ^^ space ^^ string "int")

      method ty_TArrow _x1 _x2 =
        any_number_of (string "ty" ^^ space ^^ symbol_str "->")
        ^^ space ^^ string "ty"

      method ty_TAssociatedType ~impl:_ ~item:_ =
        string "impl" ^^ space ^^ symbol_str "::" ^^ space ^^ string "item"

      method ty_TBool = symbol_str "bool"
      method ty_TChar = symbol_str "char"
      method ty_TDyn ~witness:_ ~goals:_ = features ["dyn"] ^^ any_number_of (string "goal")

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

      method ty_TOpaque _x1 = symbol_str "impl" ^^ space ^^ string "ty"
      method ty_TParam _x1 = string "ident"

      method ty_TRawPointer ~witness:_ =
        either_of
          [
            features [ "raw_pointer" ] ^^ symbol_str "*const" ^^ space
            ^^ string "ty";
            features [ "raw_pointer" ] ^^ symbol_str "*mut" ^^ space
            ^^ string "ty";
          ]

      method ty_TRef ~witness:_ ~region:_ ~typ:_ ~mut:_ =
        either_of [
            features [ "reference" ] ^^ symbol_str "*" ^^ space ^^ string "expr";
            features [ "reference"; "mutable_reference" ] ^^ symbol_str "*mut" ^^ space ^^ string "expr";
          ]

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

module ASTGenerator = struct
  module AST = Ast.Make (Features.Full)
  open AST

  type ast_types =
    | CONCRETE_IDENT
    | LITERAL
    | TY
    | EXPR
    | GENERICS
    | GLOBAL_IDENT
    | PAT
    | LOCAL_IDENT
    | IMPL_EXPR
    | ITEM

  let rec generate_helper (t : ast_types) (indexes : int list) : Yojson.Safe.t * int list =
    let i, indexes = List.hd_exn indexes, Option.value ~default:[] (List.tl indexes) in
    let cases: (unit -> Yojson.Safe.t * int list) list =
      (match t with
       | CONCRETE_IDENT ->
         [
           (fun () -> ([%yojson_of: concrete_ident] (Concrete_ident.of_name Value Hax_lib__RefineAs__into_checked), indexes))
         ]

       | LITERAL ->
         [
           (fun () -> ([%yojson_of: literal] (String "dummy"), indexes));
           (fun () -> ([%yojson_of: literal] (Char 'a'), indexes));
           (fun () -> ([%yojson_of: literal] (Int {value = "dummy"; negative = false; kind = { size = S8; signedness = Unsigned }}), indexes));
           (fun () -> ([%yojson_of: literal] (Float {value = "dummy"; negative = false; kind = F16}), indexes));
           (fun () -> ([%yojson_of: literal] (Bool false), indexes));
         ]

       | TY ->
         [
           (fun () -> ([%yojson_of: ty] TBool, indexes));
           (fun () -> ([%yojson_of: ty] TChar, indexes));
           (fun () -> ([%yojson_of: ty] (TInt { size = S8 ; signedness = Unsigned}), indexes));
           (fun () -> ([%yojson_of: ty] (TFloat F16), indexes));
           (fun () -> ([%yojson_of: ty] TStr, indexes));
           (fun () ->
              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in
              ([%yojson_of: ty] (TApp { ident = g_ident ; args = [] }), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              let length, indexes = generate_helper EXPR indexes in (* Should be const expr ! *)
              let length = [%of_yojson: expr] length in
              ([%yojson_of: ty] (TArray {typ; length;}), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: ty] (TSlice {witness = Features.On.slice; ty = typ;}), indexes));
           (fun () ->
              ([%yojson_of: ty] (TRawPointer {witness = Features.On.raw_pointer;}), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: ty] (TRef {
                   witness = Features.On.reference;
                   region = "todo";
                   typ = typ;
                   mut = Immutable;
                 }), indexes));
           (fun () ->
              let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
              let l_ident = [%of_yojson : local_ident] l_ident in
              ([%yojson_of: ty] (TParam l_ident), indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson : ty] typ in
              ([%yojson_of: ty] (TArrow ([] ,typ)), indexes));
           (fun () ->
              let impl_expr, indexes = generate_helper IMPL_EXPR indexes in
              let impl_expr = [%of_yojson: impl_expr] impl_expr in

              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: ty] (TAssociatedType {impl = impl_expr; item = c_ident}), indexes));
           (fun () ->
              let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
              let c_ident = [%of_yojson: concrete_ident] c_ident in
              ([%yojson_of: ty] (TOpaque c_ident), indexes));
           (fun () ->
              ([%yojson_of: ty] (TDyn { witness = Features.On.dyn; goals= []}), indexes));
         ]

       | EXPR ->
         let expr_shell e indexes =
           let typ, indexes = generate_helper TY indexes in
           (`Assoc [
               ("e" , e ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("typ" , typ)
             ], indexes)
         in
         List.map ~f:(fun expr_f -> (fun () ->
             let (expr', indexes) = expr_f () in
             expr_shell expr' indexes))
           [
             (fun () ->
                let cond, indexes = generate_helper EXPR indexes in
                let cond = [%of_yojson: expr] cond in

                let then_, indexes = generate_helper EXPR indexes in
                let then_ = [%of_yojson: expr] then_ in

                ([%yojson_of: expr'] (If {
                     cond = cond;
                     then_ = then_;
                     else_ = None
                   }), indexes));
             (fun () ->
                let f, indexes = generate_helper EXPR indexes in
                let f = [%of_yojson: expr] f in

                let args, indexes = generate_helper EXPR indexes in
                let args = [%of_yojson: expr] args in

                ([%yojson_of: expr'] (App { f; args = [ args (* must have 1+ items *) ]; generic_args = []; bounds_impls = []; trait = None; }), indexes));
             (fun () ->
                let lit, indexes = generate_helper LITERAL indexes in
                let lit = [%of_yojson: literal] lit in
                ([%yojson_of: expr'] (Literal lit), indexes));
             (fun () -> ([%yojson_of: expr'] (Array []), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson: global_ident] g_ident in

                ([%yojson_of: expr'] (Construct {
                     constructor = g_ident;
                     is_record = false;
                     is_struct = false;
                     fields = [];
                     base = None;
                   }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                ([%yojson_of: expr'] (Match { scrutinee = expr; arms = [] }), indexes));
             (fun () ->
                let lhs, indexes = generate_helper PAT indexes in
                let lhs = [%of_yojson: pat] lhs in

                let rhs, indexes = generate_helper EXPR indexes in
                let rhs = [%of_yojson: expr] rhs in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                ([%yojson_of: expr'] (Let { monadic = None; lhs; rhs; body; }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                ([%yojson_of: expr'] (Block { e = expr; safety_mode = Safe; witness = Features.On.block }), indexes));
             (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson : local_ident] l_ident in
                ([%yojson_of: expr'] (LocalVar l_ident), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson : global_ident] g_ident in
                ([%yojson_of: expr'] (GlobalVar g_ident), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (Ascription { e = expr; typ; }), indexes));
             (fun () ->
                let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
                let g_ident = [%of_yojson : global_ident] g_ident in
                ([%yojson_of: expr'] (MacroInvokation {
                  macro = g_ident;
                  args = "dummy";
                  witness = Features.On.macro;
                }), indexes));
             (fun () ->
                let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
                let l_ident = [%of_yojson : local_ident] l_ident in

                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (Assign {
                     lhs = LhsLocalVar { var = l_ident; typ; };
                     e = expr;
                     witness = Features.On.mutable_variable;
                   }), indexes));
             (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in

                ([%yojson_of: expr'] (Loop {
                 body = body;
                 kind = UnconditionalLoop;
                 state = None;
                 label = None;
                 witness = Features.On.loop;
               }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Break {
                 e = expr;
                 label = None;
                 witness = (Features.On.break, Features.On.loop);
               }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Return { e = expr; witness = Features.On.early_exit }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in

                let typ, indexes = generate_helper TY indexes in
                let typ = [%of_yojson: ty] typ in
                ([%yojson_of: expr'] (QuestionMark {
                     e = expr;
                     return_typ = typ;
                     witness = Features.On.question_mark;
                   }), indexes));
             (fun () -> ([%yojson_of: expr'] (Continue {
                  e = None;
                  label = None;
                  witness = (Features.On.continue, Features.On.loop);
                }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (Borrow {
                  kind = Shared;
                  e = expr;
                  witness = Features.On.reference
                }), indexes));
             (fun () ->
                let expr, indexes = generate_helper EXPR indexes in
                let expr = [%of_yojson: expr] expr in
                ([%yojson_of: expr'] (AddressOf
               { mut = Immutable; e = expr; witness = Features.On.raw_pointer }), indexes));
             (fun () ->
                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ([%yojson_of: expr'] (Closure { params = []; body; captures = [] }), indexes));
             (* TODO: The two remaing ast elements! *)
             (* EffectAction *)
             (*   { action = Features.On.monadic_action; argument = dummy_expr }; *)
             (* Quote { contents = []; witness = Features.On.quote }; *)
           ]

       | GENERICS ->
         [
           (fun () -> ([%yojson_of: generics] { params = []; constraints = [] }, indexes));
         ]

       | GLOBAL_IDENT ->
         [fun () ->
            let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
            (`List [ `String "Concrete" ; c_ident ], indexes)
         ]

       | PAT ->

         let pat_shell v indexes =
           let typ, indexes = generate_helper TY indexes in
           (`Assoc [
               ("p" , v ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("typ" , typ) ;
             ], indexes)
         in
         List.map ~f:(fun pat_f -> (fun () ->
             let (pat', indexes) = pat_f () in
             pat_shell pat' indexes))
         [
           (fun () -> ([%yojson_of: pat'] PWild, indexes));
           (fun () ->
              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in

              let pat, indexes = generate_helper PAT indexes in
              let pat = [%of_yojson: pat] pat in
              ([%yojson_of: pat'] (PAscription {
                   typ;
                   typ_span = Span.dummy ();
                   pat;
                 }), indexes));
           (fun () ->
              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in
              ([%yojson_of: pat'] (PConstruct
             {
               constructor = g_ident;
               is_record = false;
               is_struct = false;
               fields = [];
             }), indexes));
           (fun () ->
              let lhs_pat, indexes = generate_helper PAT indexes in
              let lhs_pat = [%of_yojson: pat] lhs_pat in

              let rhs_pat, indexes = generate_helper PAT indexes in
              let rhs_pat = [%of_yojson: pat] rhs_pat in
              ([%yojson_of: pat'] (POr {
                   subpats = [ lhs_pat; rhs_pat ]
                 }), indexes));
           (fun () -> ([%yojson_of: pat'] (PArray { args = [] }), indexes));
           (fun () ->
              let pat, indexes = generate_helper PAT indexes in
              let pat = [%of_yojson: pat] pat in
              ([%yojson_of: pat'] (PDeref {
                   subpat = pat;
                   witness = Features.On.reference
                 }), indexes));
           (fun () ->
              let lit, indexes = generate_helper LITERAL indexes in
              let lit = [%of_yojson: literal] lit in
              ([%yojson_of: pat'] (PConstant { lit }), indexes));
           (fun () ->
              let l_ident, indexes = generate_helper LOCAL_IDENT indexes in
              let l_ident = [%of_yojson: local_ident] l_ident in

              let typ, indexes = generate_helper TY indexes in
              let typ = [%of_yojson: ty] typ in
              ([%yojson_of: pat'] (PBinding
             {
               mut = Mutable Features.On.mutable_variable;
               mode = ByValue;
               var = l_ident;
               typ;
               subpat = None;
             }), indexes));
         ]

       | LOCAL_IDENT ->
         [fun () ->
            (`Assoc [("name" , `String "dummy") ; ("id" , `List [`List [`String "Typ"] ; `Int 0])], indexes)
         ]

       | IMPL_EXPR ->
         [fun () ->
            let c_ident, indexes = generate_helper CONCRETE_IDENT indexes in
            (`Assoc [
                ("kind" , `List [`String "Self"]) ;
                ("goal" , `Assoc [
                    ("trait" , c_ident) ;
                    ("args" , `List [])])
              ], indexes)
         ]

       | ITEM ->
         let item_shell v indexes =
           let ident, indexes = generate_helper CONCRETE_IDENT indexes in
           (`Assoc [
               ("v" , v ) ;
               ("span" , `Assoc [("id" , `Int 79902) ; ("data" , `List [])]) ;
               ("ident" , ident) ;
               ("attrs" , `List [])
             ], indexes)
         in
         List.map ~f:(fun item_f -> (fun () ->
             let (item', indexes) = item_f () in
             item_shell item' indexes))
           [
             (fun () ->
                let name, indexes = generate_helper CONCRETE_IDENT indexes in
                let name = [%of_yojson: concrete_ident] name in

                let generics, indexes = generate_helper GENERICS indexes in
                let generics = [%of_yojson: generics] generics in

                let body, indexes = generate_helper EXPR indexes in
                let body = [%of_yojson: expr] body in
                ([%yojson_of: item'] (Fn {name; generics; body; params = []; safety = Safe}), indexes));
            (fun () ->
               let name, indexes = generate_helper CONCRETE_IDENT indexes in
               let name = [%of_yojson: concrete_ident] name in

               let generics, indexes = generate_helper GENERICS indexes in
               let generics = [%of_yojson: generics] generics in

               let typ, indexes = generate_helper TY indexes in
               let typ = [%of_yojson: ty] typ in
               ([%yojson_of: item'] (TyAlias {name; generics; ty = typ;}), indexes));
            (* enum *)
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Type {name; generics; variants = []; is_struct = false}), indexes));
            (* struct *)
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Type {name; generics; variants = []; is_struct = true}), indexes));
            (fun () ->
               let macro, indexes = generate_helper CONCRETE_IDENT indexes in
               let macro = [%of_yojson: concrete_ident] macro in
               ([%yojson_of: item'] (IMacroInvokation {macro; argument = "TODO"; span = Span.dummy(); witness = Features.On.macro}), indexes));
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in
              ([%yojson_of: item'] (Trait {
                   name ;
                   generics ;
                   items = [];
                   safety = Safe;
                 }), indexes));
            (fun () ->
              let generics, indexes = generate_helper GENERICS indexes in
              let generics = [%of_yojson: generics] generics in

              let ty, indexes = generate_helper TY indexes in
              let ty = [%of_yojson: ty] ty in

              let g_ident, indexes = generate_helper GLOBAL_IDENT indexes in
              let g_ident = [%of_yojson: global_ident] g_ident in
              ([%yojson_of: item'] (Impl {
                   generics;
                   self_ty = ty;
                   of_trait = (g_ident, []) ;
                   items = [] ;
                   parent_bounds = [] ;
                   safety = Safe
                 }), indexes));
            (fun () ->
              let name, indexes = generate_helper CONCRETE_IDENT indexes in
              let name = [%of_yojson: concrete_ident] name in

              let item, indexes = generate_helper CONCRETE_IDENT indexes in
              let item = [%of_yojson: concrete_ident] item in
               ([%yojson_of: item'] (Alias { name;  item }), indexes));
            (fun () ->
              ([%yojson_of: item'] (Use {
                  path = [];
                  is_external = false;
                  rename = None
                }), indexes));
            (* Quote { contents = []; witness = Features.On.quote }; *)
            (* HaxError "dummy"; *)
            (* NotImplementedYet; *)
           ]
      )  in
    List.nth_exn cases i ()

  let generate (t : ast_types) (indexes : int list) : Yojson.Safe.t =
    fst (generate_helper t indexes)

  let generate_literals =
    let literal_args = [
      (* String *)
      [0];
      (* Char *)
      [1];
      (* Int *)
      [2];
      (* Float *)
      [3];
      (* Bool *)
      [4]
    ] in
    List.map ~f:(fun x -> [%of_yojson: literal] (generate LITERAL x)) literal_args

  let generate_tys ~ty ~expr : ty list =
    let concrete_ident_args = [0] in
    let global_ident_args = [0] @ concrete_ident_args in
    let local_ident_args = [0] in
    let impl_expr_args = [0;0] in

    (* TODO: BFS generator *)
    let ty_args = [
      (* TBool *)
      [0];
      (* TChar *)
      [1];
      (* TInt *)
      [2];
      (* TFloat *)
      [3];
      (* TStr *)
      [4];
      (* TApp *)
      [5] @ global_ident_args;
      (* TArray *)
      [6] @ ty @ expr;
      (* TSlice *)
      [7] @ ty;
      (* TRawPointer *)
      [8];
      (* TRef *)
      [9] @ ty;
      (* TParam *)
      [10] @ local_ident_args;
      (* TArrow *)
      [11] @ ty;
      (* TAssociatedType *)
      [12] @ impl_expr_args @ concrete_ident_args ;
      (* TOpaque *)
      [13] @ concrete_ident_args;
      (* TDyn *)
      [14];
    ] in

    List.map ~f:(fun x -> [%of_yojson: ty] (generate TY x)) ty_args

  let generate_pats ~ty ~ty1 ~literal ~pat1 ~pat2 =
    let concrete_ident_args = [0] in
    let global_ident_args = [0] @ concrete_ident_args in
    let local_ident_args = [0] in

    let pat_args = List.map ~f:(fun x -> x @ ty) [
        (* PWild *)
        [0];
        (* PAscription *)
        [1] @ ty1 @ pat1;
        (* PConstruct *)
        [2] @ global_ident_args;
        (* POr *)
        [3] @ pat1 @ pat2;
        (* PArray *)
        [4];
        (* PDeref *)
        [5] @ pat1;
        (* PConstant *)
        [6] @ literal;
        (* PBinding *)
        [7] @ local_ident_args @ ty1;
      ] in
    List.map ~f:(fun x -> [%of_yojson: pat] (generate PAT x)) pat_args

  let generate_expr ~expr_ty ~literal ~ty ~expr0 ~expr1 ~expr2 ~pat =
    let concrete_ident_args = [0] in
    let global_ident_args = [0] @ concrete_ident_args in
    let local_ident_args = [0] in

    let expr_args =
      List.map ~f:(fun x -> x @ expr_ty)
        [
          (* If *)
          [0] @ expr1 @ expr2 (* @ expr3 *) ;
          (* App *)
          [1] @ expr1 @ expr2;
          (* Literal *)
          [2] @ literal;
          (* Array *)
          [3];
          (* Construct *)
          [4] @ global_ident_args;
          (* Match *)
          [5] @ expr1;
          (* Let *)
          [6] @ pat @ expr1 @ expr2;
          (* Block *)
          [7] @ expr1;
          (* LocalVar *)
          [8] @ local_ident_args;
          (* GlobalVar *)
          [9] @ global_ident_args;
          (* Ascription *)
          [10] @ expr1 @ ty;
          (* MacroInvokation *)
          [11] @ global_ident_args;
          (* Assign *)
          [12] @ local_ident_args @ expr1 @ ty;
          (* Loop *)
          [13] @ expr1;
          (* Break *)
          [14] @ expr1;
          (* Return *)
          [15] @ expr1;
          (* QuestionMark *)
          [16] @ expr1 @ ty;
          (* Continue *)
          [17];
          (* Borrow *)
          [18] @ expr1;
          (* AddressOf *)
          [19] @ expr1;
          (* Closure *)
          [20] @ expr1;
        ]
    in
    List.map ~f:(fun x -> [%of_yojson: expr] (generate EXPR x)) expr_args

  let generate_items ~expr ~ty =
    let concrete_ident_args = [0] in
    let global_ident_args = [0] @ concrete_ident_args in
    let generics_args = [0] in

    let item_args = List.map ~f:(fun x -> x @ concrete_ident_args) [
        (* Fn *)
        [0] @ concrete_ident_args @ generics_args @ expr;
        (* TyAlias *)
        [1] @ concrete_ident_args @ generics_args @ ty;
        (* Type *)
        [2] @ concrete_ident_args @ generics_args;
        (* Type *)
        [3] @ concrete_ident_args @ generics_args;
        (* IMacroInvokation *)
        [4] @ concrete_ident_args;
        (* Trait *)
        [5] @ concrete_ident_args @ generics_args;
        (* Impl *)
        [6] @ generics_args @ ty @ global_ident_args;
        (* Alias *)
        [7] @ concrete_ident_args @ concrete_ident_args;
        (* Use *)
        [8];
      ]
    in
    List.map ~f:(fun x -> [%of_yojson: item] (generate ITEM x)) item_args

  let generate_full_ast : (literal list * ty list * pat list * expr list * item list) =
    (** Can use rendering tools for EBNF e.g. https://rr.red-dove.com/ui **)
    (** bfs with no recursion, elements seen before are replaced with 0 depth (constant) elements **)

    let concrete_ident_args = [0] in
    let global_ident_args = [0] @ concrete_ident_args in
    let local_ident_args = [0] in
    let generics_args = [0] in
    let impl_expr_args = [0;0] in

    let my_literals = generate_literals in
     (* TODO: generate random / dummy elements for ty, literal, pat and expr arguments *)
    let my_tys   = generate_tys ~ty:[0] ~expr:[2;0;0] in
    let my_pats  = generate_pats ~ty:[0] ~ty1:[0] ~literal:[0] ~pat1:[0;0] ~pat2:[0;0] in
    let my_exprs = generate_expr ~expr_ty:[0] ~literal:[0] ~ty:[0] ~expr0:[2;0;0] ~expr1:[2;0;0] ~expr2:[2;0;0] ~pat:[0;0] in
    let my_items = generate_items ~expr:[2;0;0] ~ty:[0] in
    (my_literals, my_tys, my_pats, my_exprs, my_items)
end

module HaxCFG = struct
  module MyPrinter =
    Make
      (Features.Full)
      (struct
        let default x = x
      end)

  module MyAstGenerator = ASTGenerator

  module AST = Ast.Make (Features.Full)
  open AST

  let print_ast (_ : unit) =
    let my_printer = new MyPrinter.printer in

    (** Can use rendering tools for EBNF e.g. https://rr.red-dove.com/ui **)

    let (my_literals, my_tys, my_pats, my_exprs, my_items) : (literal list * ty list * pat list * expr list * item list) = MyAstGenerator.generate_full_ast in

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

    [
      Types.
        {
          path = "ast_spec.md";
          contents =
            "# Hax CFG" ^ literal_string ^ expr_string ^ ty_string ^ pat_string ^ item_string;
          sourcemap = None;
        };
    ]
end

let translate _ _bo _ = HaxCFG.print_ast ()

open Phase_utils

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.Unsafe(Features.Rust)
  ]
  [@ocamlformat "disable"]

let apply_phases (_bo : BackendOptions.t) (items : Ast.Rust.item list) : _ list =
  []
