open Hax_engine
open Utils
open Base

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
      let backend = Diagnostics.Backend.Ocaml
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
             and type block = Features.Off.block
             and type quote = Features.Off.quote
             and type dyn = Features.Off.dyn
             and type match_guard = Features.Off.match_guard
             and type trait_item_default = Features.Off.trait_item_default
             and type unsafe = Features.Off.unsafe
             and type loop = Features.Off.loop
             and type for_loop = Features.Off.for_loop
             and type while_loop = Features.Off.while_loop
             and type for_index_loop = Features.Off.for_index_loop
             and type state_passing_loop = Features.Off.state_passing_loop
             and type fold_like_loop = Features.Off.fold_like_loop) =
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

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast
module OCamlNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.Make (InputLanguage)
module RenderId = Concrete_ident.MakeRenderAPI (OCamlNamePolicy)
open AST

module BasePrinter = Generic_printer.Make (InputLanguage)

module Make
    (Default : sig
      val default : string -> string
    end)
    (Attrs : Attrs.WITH_ITEMS) =
struct
  open PPrint

  let default_string_for s = "TODO: please implement the method `" ^ s ^ "`"
  let default_document_for = default_string_for >> string

  type ('get_span_data, 'a) object_type =
    ('get_span_data, 'a) BasePrinter.Gen.object_type

  class printer =
    object (self)
      inherit BasePrinter.base

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
      method cf_kind_BreakOnly = default_document_for "cf_kind_BreakOnly"

      method cf_kind_BreakOrReturn =
        default_document_for "cf_kind_BreakOrReturn"

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

      method expr'_Break ~super:_ ~e:_ ~acc:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Break"

      method expr'_Closure ~super:_ ~params:_ ~body:_ ~captures:_ =
        default_document_for "expr'_Closure"

      method expr'_Construct_inductive ~super:_ ~constructor:_ ~is_record:_
          ~is_struct:_ ~fields:_ ~base:_ =
        default_document_for "expr'_Construct_inductive"

      method expr'_Construct_tuple ~super:_ ~components:_ =
        default_document_for "expr'_Construct_tuple"

      method expr'_Continue ~super:_ ~acc:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Continue"

      method expr'_EffectAction ~super:_ ~action:_ ~argument:_ =
        default_document_for "expr'_EffectAction"

      method expr'_GlobalVar_concrete ~super:_ _x2 =
        default_document_for "expr'_GlobalVar_concrete"

      method expr'_GlobalVar_primitive ~super:_ _x2 =
        default_document_for "expr'_GlobalVar_primitive"

      method expr'_If ~super:_ ~cond:_ ~then_:_ ~else_:_ =
        default_document_for "expr'_If"

      method expr'_Let ~super:_ ~monadic:_ ~lhs:_ ~rhs:_ ~body:_ =
        default_document_for "expr'_Let"

      method expr'_Literal ~super:_ _x2 = default_document_for "expr'_Literal"
      method expr'_LocalVar ~super:_ _x2 = default_document_for "expr'_LocalVar"

      method expr'_Loop ~super:_ ~body:_ ~kind:_ ~state:_ ~control_flow:_
          ~label:_ ~witness:_ =
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

      method generic_param_kind_GPType =
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

      method item ~v:_ ~span:_ ~ident:_ ~attrs:_ = default_document_for "item"

      method item'_Alias ~super:_ ~name:_ ~item:_ =
        default_document_for "item'_Alias"

      method item'_Enum_Variant ~name:_ ~arguments:_ ~is_record:_ ~attrs:_ =
        default_document_for "item'_Enum_Variant"

      method item'_Fn ~super:_ ~name:_ ~generics:_ ~body:_ ~params:_ ~safety:_ =
        default_document_for "item'_Fn"

      method item'_HaxError ~super:_ _x2 = default_document_for "item'_HaxError"

      method item'_IMacroInvokation ~super:_ ~macro:_ ~argument:_ ~span:_
          ~witness:_ =
        default_document_for "item'_IMacroInvokation"

      method item'_Impl ~super:_ ~generics:_ ~self_ty:_ ~of_trait:_ ~items:_
          ~parent_bounds:_ ~safety:_ =
        default_document_for "item'_Impl"

      method item'_NotImplementedYet =
        default_document_for "item'_NotImplementedYet"

      method item'_Quote ~super:_ ~quote:_ ~origin:_ =
        default_document_for "item'_Quote"

      method item'_Trait ~super:_ ~name:_ ~generics:_ ~items:_ ~safety:_ =
        default_document_for "item'_Trait"

      method item'_TyAlias ~super:_ ~name:_ ~generics:_ ~ty:_ =
        default_document_for "item'_TyAlias"

      method item'_Type_enum ~super:_ ~name:_ ~generics:_ ~variants:_ =
        default_document_for "item'_Type_enum"

      method item'_Type_struct ~super:_ ~name:_ ~generics:_ ~tuple_struct:_
          ~arguments:_ =
        default_document_for "item'_Type_struct"

      method item'_Use ~super:_ ~path:_ ~is_external:_ ~rename:_ =
        default_document_for "item'_Use"

      method item_quote_origin ~item_kind:_ ~item_ident:_ ~position:_ =
        default_document_for "item_quote_origin"

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

      method modul x1 = separate_map (string "\n") (fun x -> x#p) x1

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
      (* END GENERATED *)
    end

  let new_printer : BasePrinter.finalized_printer =
    BasePrinter.finalize (fun () -> (new printer :> BasePrinter.printer))
end

module type S = sig
  val new_printer : BasePrinter.finalized_printer
end

let make (module M : Attrs.WITH_ITEMS) =
  let open (
    Make
      (struct
        let default x = x
      end)
      (M) :
      S) in
  new_printer

let translate m _ ~bundles:_ (items : AST.item list) : Types.file list =
  let my_printer = make m in
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.filter_map ~f:(fun (_, items) ->
         let* first_item = List.hd items in
         Some ((RenderId.render first_item.ident).path, items))
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"_"
             (List.map ~f:(map_first_letter String.uppercase) ns)
         in
         let sourcemap, contents =
           let annotated = my_printer#entrypoint_modul items in
           let open Generic_printer.AnnotatedString in
           (to_sourcemap annotated, to_string annotated)
         in
         let sourcemap = Some sourcemap in
         let path = mod_name ^ ".ml" in
         Types.{ path; contents; sourcemap })

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
  |> Phases.Bundle_cycles
  |> Phases.Sort_items
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (_bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
