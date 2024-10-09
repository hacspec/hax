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
    (F : Features.T) (Default : sig
      val default : string -> string
    end) =
struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  module Base = Generic_printer.Make (F)
  open PPrint

  let default_string_for s = "TODO: please implement the method `" ^ s ^ "`"
  let default_document_for = default_string_for >> string

  let any_number_of x = brackets ( x ) ^^ string "*"
  let option_of x = brackets ( x ) ^^ string "?"

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
      method common_array _x1 = default_document_for "common_array"

      method dyn_trait_goal ~trait:_ ~non_self_args:_ =
        default_document_for "dyn_trait_goal"

      method error_expr _x1 = default_document_for "error_expr"
      method error_item _x1 = default_document_for "error_item"
      method error_pat _x1 = default_document_for "error_pat"
      method expr ~e:_ ~span:_ ~typ:_ = default_document_for "expr"

      method expr'_AddressOf ~super:_ ~mut:_ ~e:_ ~witness:_ =
        default_document_for "expr'_AddressOf"

      method expr'_App_application ~super:_ ~f:_ ~args:_ ~generics:_ =
        default_document_for "expr'_App_application"

      method expr'_App_constant ~super:_ ~constant:_ ~generics:_ =
        default_document_for "expr'_App_constant"

      method expr'_App_field_projection ~super:_ ~field:_ ~e:_ =
        default_document_for "expr'_App_field_projection"

      method expr'_App_tuple_projection ~super:_ ~size:_ ~nth:_ ~e:_ =
        default_document_for "expr'_App_tuple_projection"

      method expr'_Ascription ~super:_ ~e:_ ~typ:_ =
        default_document_for "expr'_Ascription"

      method expr'_Assign ~super:_ ~lhs:_ ~e:_ ~witness:_ =
        default_document_for "expr'_Assign"

      method expr'_Block ~super:_ ~e:_ ~safety_mode:_ ~witness:_ =
        default_document_for "expr'_Block"

      method expr'_Borrow ~super:_ ~kind:_ ~e:_ ~witness:_ =
        default_document_for "expr'_Borrow"

      method expr'_Break ~super:_ ~e:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Break"

      method expr'_Closure ~super:_ ~params:_ ~body:_ ~captures:_ =
        default_document_for "expr'_Closure"

      method expr'_Construct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ ~base:_ =
        default_document_for "expr'_Construct_inductive"

      method expr'_Construct_tuple ~super:_ ~components:_ =
        default_document_for "expr'_Construct_tuple"

      method expr'_Continue ~super:_ ~e:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Continue"

      method expr'_EffectAction ~super:_ ~action:_ ~argument:_ =
        default_document_for "expr'_EffectAction"

      method expr'_GlobalVar ~super:_ _x2 =
        default_document_for "expr'_GlobalVar"

      method expr'_If ~super:_ ~cond:_ ~then_:_ ~else_:_ =
        default_document_for "expr'_If"

      method expr'_Let ~super:_ ~monadic:_ ~lhs:_ ~rhs:_ ~body:_ =
        default_document_for "expr'_Let"

      method expr'_Literal ~super:_ _x2 = default_document_for "expr'_Literal"
      method expr'_LocalVar ~super:_ _x2 = default_document_for "expr'_LocalVar"

      method expr'_Loop ~super:_ ~body:_ ~kind:_ ~state:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Loop"

      method expr'_MacroInvokation ~super:_ ~macro:_ ~args:_ ~witness:_ =
        default_document_for "expr'_MacroInvokation"

      method expr'_Match ~super:_ ~scrutinee:_ ~arms:_ =
        default_document_for "expr'_Match"

      method expr'_QuestionMark ~super:_ ~e:_ ~return_typ:_ ~witness:_ =
        default_document_for "expr'_QuestionMark"

      method expr'_Quote ~super:_ _x2 = default_document_for "expr'_Quote"

      method expr'_Return ~super:_ ~e:_ ~witness:_ =
        default_document_for "expr'_Return"

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

      method item ~v ~span:_ ~ident:_ ~attrs:_ = v#p (* default_document_for "item" *)

      method item'_Alias ~super:_ ~name:_ ~item:_ =
        default_document_for "item'_Alias"

      method item'_Fn ~super:_ ~name:_ ~generics:_ ~body:_ ~params:_ ~safety:_ =
        (* TODOD: pub, const, pub(crate) *)
        string "<safety>" ^^ space ^^ string "fn" ^^ space ^^ string "<ident>" ^^ parens ( any_number_of (string "<pat>" ^^ space ^^ colon ^^ string "<ty>") ) ^^ braces ( string "<expr>" )


      method item'_HaxError ~super:_ _x2 = default_document_for "item'_HaxError"

      method item'_IMacroInvokation ~super:_ ~macro:_ ~argument:_ ~span:_
          ~witness:_ =
        default_document_for "item'_IMacroInvokation"

      method item'_Impl ~super:_ ~generics:_ ~self_ty:_ ~of_trait:_ ~items:_
          ~parent_bounds:_ ~safety:_ =
        default_document_for "item'_Impl"

      method item'_NotImplementedYet =
        default_document_for "item'_NotImplementedYet"

      method item'_Quote ~super:_ _x2 = default_document_for "item'_Quote"

      method item'_Trait ~super:_ ~name:_ ~generics:_ ~items:_ ~safety:_ =
        string "trait" ^^ space ^^ string "<ident>" ^^ braces ( any_number_of (string "<trait_item>") )

      method item'_TyAlias ~super:_ ~name:_ ~generics:_ ~ty:_ =
        string "type" ^^ space ^^ string "<ident>" ^^ space ^^ string "=" ^^ space ^^ string "<ty>"

      method item'_Type ~super:_ ~name:_ ~generics:_ ~variants:_ ~is_struct =
        (* TODO globality *)
        if is_struct
        then string "struct" ^^ space ^^ string "<ident>" ^^ space ^^ string "=" ^^ space ^^ braces ( any_number_of ( string "<name>" ^^ colon ^^ space ^^ string "<ty>" ^^ comma ) )
        else string "enum" ^^ space ^^ string "<ident>" ^^ space ^^ string "=" ^^ space ^^ braces ( any_number_of (string "<ident>" ^^ option_of (parens (any_number_of (string "<ty>"))) ^^ comma ) )

      method item'_Use ~super:_ ~path:_ ~is_external:_ ~rename:_ =
        default_document_for "item'_Use"

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

      method literal_Bool _x1 = default_document_for "literal_Bool"
      method literal_Char _x1 = default_document_for "literal_Char"

      method literal_Float ~value:_ ~negative:_ ~kind:_ =
        default_document_for "literal_Float"

      method literal_Int ~value:_ ~negative:_ ~kind:_ =
        default_document_for "literal_Int"

      method literal_String _x1 = default_document_for "literal_String"

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

      method pat ~p:_ ~span:_ ~typ:_ = default_document_for "pat"

      method pat'_PAscription ~super:_ ~typ:_ ~typ_span:_ ~pat:_ =
        default_document_for "pat'_PAscription"

      method pat'_PBinding ~super:_ ~mut:_ ~mode:_ ~var:_ ~typ:_ ~subpat:_ =
        default_document_for "pat'_PBinding"

      method pat'_PConstant ~super:_ ~lit:_ =
        default_document_for "pat'_PConstant"

      method pat'_PConstruct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ =
        default_document_for "pat'_PConstruct_inductive"

      method pat'_PConstruct_tuple ~super:_ ~components:_ =
        default_document_for "pat'_PConstruct_tuple"

      method pat'_PDeref ~super:_ ~subpat:_ ~witness:_ =
        default_document_for "pat'_PDeref"

      method pat'_PWild = default_document_for "pat'_PWild"
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
      method ty_TArray ~typ:_ ~length:_ = default_document_for "ty_TArray"
      method ty_TArrow _x1 _x2 = default_document_for "ty_TArrow"

      method ty_TAssociatedType ~impl:_ ~item:_ =
        default_document_for "ty_TAssociatedType"

      method ty_TBool = default_document_for "ty_TBool"
      method ty_TChar = default_document_for "ty_TChar"
      method ty_TDyn ~witness:_ ~goals:_ = default_document_for "ty_TDyn"
      method ty_TFloat _x1 = default_document_for "ty_TFloat"
      method ty_TInt _x1 = default_document_for "ty_TInt"
      method ty_TOpaque _x1 = default_document_for "ty_TOpaque"
      method ty_TParam _x1 = default_document_for "ty_TParam"
      method ty_TRawPointer ~witness:_ = default_document_for "ty_TRawPointer"

      method ty_TRef ~witness:_ ~region:_ ~typ:_ ~mut:_ =
        default_document_for "ty_TRef"

      method ty_TSlice ~witness:_ ~ty:_ = default_document_for "ty_TSlice"
      method ty_TStr = default_document_for "ty_TStr"

      method variant ~name:_ ~arguments:_ ~is_record:_ ~attrs:_ =
        default_document_for "variant"
      (* END GENERATED *)
    end
end

module HaxCFG = struct
  module MyPrinter = Make (Features.Full) (struct let default x = x end)

  module AST = Ast.Make (Features.Full)
  open AST

  let print_ast (_ : unit) =
    let my_printer = new MyPrinter.printer in

    let dummy_ident : concrete_ident =
      Concrete_ident.of_name Value Hax_lib__RefineAs__into_checked
    in
    let dummy_ty : ty = TStr in
    let dummy_expr : expr = { e = Literal (String "dummy"); span = Span.dummy (); typ = dummy_ty } in
    let dummy_generics : generics = { params = []; constraints = [] } in
    let dummy_global_ident : global_ident =
      `Concrete (dummy_ident)
    in
    let dummy_pat = { p = PWild; span = Span.dummy(); typ = dummy_ty } in
    let dummy_local_ident : local_ident = { name = "dummy"; id = Local_ident.mk_id Typ 0 } in

    (* print#_do_not_override_lazy_of_item' ~super AstPos_item__v v *)

    let my_items' : item' list =
      [
        Fn {
          name = dummy_ident;
          generics = dummy_generics;
          body = dummy_expr;
          params = [];
          safety = Safe};
        TyAlias {
          name = dummy_ident;
          generics = dummy_generics;
          ty = dummy_ty};
        (* struct *)
        Type {
          name = dummy_ident;
          generics = dummy_generics;
          variants = [];
          is_struct = false;
        } ;
        (* enum *)
        Type {
          name = dummy_ident;
          generics = dummy_generics;
          variants = [];
          is_struct = true;
        } ;
      ]
      (* @ List.map ~f:(fun x -> IMacroInvokation { *)
      (*     macro = x; *)
      (*     argument = "TODO"; *)
      (*     span = Span.dummy(); *)
      (*     witness : Features.On.macro; (\* TODO: Check feature enabled in target langauge *\) *)
      (*   }) ["public_nat_mod"; *)
      (*       "bytes"; *)
      (*       "public_bytes"; *)
      (*       "array"; *)
      (* "unsigned_public_integer"] *)
      @ [
        Trait {
          name = dummy_ident;
          generics = dummy_generics;
          items = [];
          safety = Safe;
        } ;
        Impl {
          generics = dummy_generics;
          self_ty = dummy_ty;
          of_trait = (dummy_global_ident , []);
          items = [];
          parent_bounds = [];
          safety = Safe;
        };
        Alias { name = dummy_ident; item = dummy_ident };
        Use { path = []; is_external = false; rename = None; };
        Quote { contents = []; witness = Features.On.quote (* TODO: Check if feature enabled *); };
        HaxError "dummy";
        NotImplementedYet
      ]
    in
    let my_items : item list = List.map ~f:(fun x -> { v = x; span = Span.dummy(); ident = dummy_ident; attrs = [] }) my_items' in
    let item_string =
      "<item> ::=\n" ^
      String.concat ~sep:"\n" (
        List.map
          ~f:(fun item ->
              let buf = Buffer.create 0 in
              PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_item item);
              "| " ^ Buffer.contents buf
            )
          my_items)
    in

    let my_exprs' = [
      If { cond = dummy_expr; then_ = dummy_expr; else_ = None };
      App { f = dummy_expr; args = []; generic_args = []; bounds_impls = []; trait = None; };
      Literal (String "dummy");
      Array [];
      (* Construct { *)
      (*   constructor = dummy_global_ident; *)
      (*   is_record = false; *)
      (*   is_struct = false; *)
      (*   fields = []; *)
      (*   base = None; *)
      (* }; *)
      (* Match { scrutinee = dummy_expr; arms = [] }; *)
      (* Let { monadic = None; lhs = dummy_pat; rhs = dummy_expr; body = dummy_expr; }; *)
      (* Block { e = dummy_expr; safety_mode = Safe; witness = Features.On.block _ _ }; *)
      (* LocalVar dummy_local_ident; *)
      (* GlobalVar dummy_global_ident; *)
      (* Ascription { e = dummy_expr; typ = dummy_ty }; *)
      (* MacroInvokation { macro = dummy_global_ident; args = "dummy"; witness = Features.On.macro; } *)
      (* Assign { lhs = LhsLocalVar { var = dummy_local_ident; typ = dummy_ty }; e = dummy_expr; witness = _ } *)
      (* Loop { body = dummy_expr; kind = UnconditionalLoop; state = None; label = None; witness = Features.On.loop; }; *)
      (* Break { e = dummy_expr; label = None; witness = (Features.On.break , Features.On.loop) }; *)
      (* Return { e = dummy_expr; witness = Features.On.early_exit }; *)
      (* QuestionMark { e = dummy_expr; return_typ = dummy_ty; witness = Features.On.question_mark }; *)
      (* Continue { *)
      (*   e = None; *)
      (*   label = None; *)
      (*   witness = (Features.On.continue , Features.On.loop); *)
      (* }; *)
      (* (\* Mem *\) *)
      (* | Borrow of { kind : borrow_kind; e : expr; witness : Features.On.reference } *)
      (* (\* Raw borrow *\) *)
      (* | AddressOf of { *)
      (*   mut : Features.On.mutable_pointer mutability; *)
      (*   e : expr; *)
      (*   witness : Features.On.raw_pointer; *)
      (* } *)
      (* | Closure of { params : pat list; body : expr; captures : expr list } *)
      (* | EffectAction of { action : Features.On.monadic_action; argument : expr } *)
      (* | Quote of quote *)
      (* (\** A quotation is an inlined piece of backend code *)
      (*     interleaved with Rust code *\) *)
    ] in
    let my_exprs = List.map ~f:(fun x -> { e = x; span = Span.dummy(); typ = dummy_ty }) my_exprs' in
    let expr_string =
      "<expr> ::=\n" ^
      String.concat ~sep:"\n" (
        List.map
          ~f:(fun expr ->
              let buf = Buffer.create 0 in
              PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_expr expr);
              "| " ^ Buffer.contents buf
            )
          my_exprs)
    in

    let my_tys = [
      TBool;
      TChar;
      TInt ({ size = S8; signedness = Signed });
      (* TFloat of float_kind; *)
      TStr;
      (* TApp of { ident : global_ident; args : generic_value list }; *)
      (* TArray of { typ : ty; length : expr }; *)
      (* TSlice of { witness : F.slice; ty : ty }; *)
      (* TRawPointer of { witness : F.raw_pointer } (\* todo *\); *)
      (* TRef of { *)
      (*     witness : F.reference; *)
      (*     region : todo; *)
      (*     typ : ty; *)
      (*     mut : F.mutable_reference mutability; *)
      (*   }; *)
      (* TParam of local_ident; *)
      (* TArrow of ty list * ty; *)
      (* TAssociatedType of { impl : impl_expr; item : concrete_ident }; *)
      (* TOpaque of concrete_ident; *)
      (* TDyn of { witness : F.dyn; goals : dyn_trait_goal list }; *)
    ] in
    let ty_string =
      "<ty> ::=\n" ^
      String.concat ~sep:"\n" (
        List.map
          ~f:(fun ty ->
              let buf = Buffer.create 0 in
              PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_ty ty);
              "| " ^ Buffer.contents buf
            )
          my_tys)
    in

    let my_pats' = [
      PWild;
      (* PAscription of { typ : ty; typ_span : span; pat : pat }; *)
      (* PConstruct of { constructor : global_ident; is_record : bool; (\* are fields named? *\) is_struct : bool; (\* a struct has one constructor *\) fields : field_pat list; }; *)
      (* POr of { subpats : pat list }; *)
      (* PArray of { args : pat list }; *)
      (* PDeref of { subpat : pat; witness : F.reference }; *)
      (* PConstant of { lit : literal }; *)
      (* PBinding of { mut : F.mutable_variable mutability; mode : binding_mode; var : local_ident; typ : ty; subpat : (pat * F.as_pattern) option; }; *)
    ] in
    let my_pats = List.map ~f:(fun x -> { p = x; span = Span.dummy(); typ = dummy_ty }) my_pats' in
    let pat_string =
      "<pat> ::=\n" ^
      String.concat ~sep:"\n" (
        List.map
          ~f:(fun pat ->
              let buf = Buffer.create 0 in
              PPrint.ToBuffer.pretty 1.0 80 buf (my_printer#entrypoint_pat pat);
              "| " ^ Buffer.contents buf
            )
          my_pats)
    in

    [Types.
       {
         path = "ast_spec.txt";
         contents =
           "Hax CFG"
           ^ "\n"
           ^ "======="
           ^ "\n"
           ^ expr_string
           ^ "\n\n"
           ^ ty_string
           ^ "\n\n"
           ^ pat_string
           ^ "\n\n"
           ^ item_string;
         sourcemap = None;
       }]
end

let translate _ (_bo) _ = HaxCFG.print_ast ()

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
