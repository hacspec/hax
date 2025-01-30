open Hax_engine
open Utils
open Base

include
  Backend.Make
    (struct
      open Features
      include Off
      include On.Monadic_binding
      include On.Slice
      include On.Macro
      include On.Construct_base
      include On.Quote
      include On.Dyn
      include On.Unsafe
    end)
    (struct
      let backend = Diagnostics.Backend.Smtlib
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
             and type state_passing_loop = Features.Off.state_passing_loop
             and type fold_like_loop = Features.Off.fold_like_loop
             and type match_guard = Features.Off.match_guard
             and type trait_item_default = Features.Off.trait_item_default) =
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
        include Features.SUBTYPE.On.Quote
        include Features.SUBTYPE.On.Dyn
        include Features.SUBTYPE.On.Unsafe
      end)

  let metadata = Phase_utils.Metadata.make (Reject (NotInBackendLang backend))
end

module AST = Ast.Make (InputLanguage)
module BackendOptions = Backend.UnitBackendOptions
open Ast

module SmtlibNamePolicy = struct include Concrete_ident.DefaultNamePolicy 
  let field_name_transform ~struct_name s = struct_name ^ "/" ^ s
end

module U = Ast_utils.Make (InputLanguage)
module RenderId = Concrete_ident.MakeRenderAPI (SmtlibNamePolicy)
open AST

let hardcoded_smtlib_headers = {|
(set-logic ALL)

;; The core::result::Result enum
(declare-datatype core/result/t_Result
  (par (T E)
    ( (core/result/Result_Ok (evd/Result/Ok T))
      (core/result/Result_Err (evd/Result/Err E)))) )

(declare-sort Tuple0 0)
(declare-fun mk-tuple0 () Tuple0)

(declare-datatypes ((Tuple1 1))
 ( (par (T1)
        ((mk-tuple1 (el1-1 T1))))))

(declare-datatypes ((Tuple2 2))
 ( (par (T1 T2)
        ((mk-tuple2 (el2-1 T1) (el2-2 T2))))))

|}

module BasePrinter = Generic_printer.Make (InputLanguage)

module Make
    (Default : sig
      val default : string -> string
    end)
    (Attrs : Attrs.WITH_ITEMS) =
struct
  open PPrint

  let slashpath lst = separate (string "/") lst
  let slashpathview path definition = slashpath ((List.map ~f:string path) @ [string definition])
  let sexprlist lst = parens (separate space lst)
  let p x = x#p
  let ps = List.map ~f:p
  let tuple_constructor_name tuple = utf8format "mk-tuple%i" (List.length tuple)

  let destructor_name field_name = concat [string "get/"; field_name]

  let default_string_for s = "(TODO please-implement-the-method \"" ^ s ^ "\")"
  let default_document_for = default_string_for >> string

  let pat_sorted_term pat = "todo"

  type ('get_span_data, 'a) object_type =
    ('get_span_data, 'a) BasePrinter.Gen.object_type

  class printer =
    object (self)
      inherit BasePrinter.base

      method expr'_If ~super:_ ~cond ~then_ ~else_ =
        let else_ = match else_ with
          | None -> string "(todo match else in if)"
          | Some tree -> tree#p
        in sexprlist [ string "ite" ; cond#p ; then_#p ; else_]

      method modul _x1 = separate_map (break 1) p _x1

      method item ~v ~span:_ ~ident:_ ~attrs:_ = v#p

      method item'_Fn ~super ~name ~generics:_ ~body ~params ~safety:_ = if
          Attrs.is_erased super.attrs
      then
        let type_doc_of_fn_param param = self#print_ty AstPos_item'_Fn_params param#v.typ in
        sexprlist
          [ string "declare-fun"
          ; name#p
          ; sexprlist (List.map ~f:type_doc_of_fn_param params)
          ; self#print_ty AstPos_item'_Fn_body body#v.typ 
        ]
      else sexprlist
        [ string "define-fun"
        ; name#p
        ; sexprlist (ps params)
          ; self#print_ty AstPos_item'_Fn_body body#v.typ 
        ; body#p ]

      method param ~pat ~typ ~typ_span:_ ~attrs:_ = sexprlist [pat#p ; typ#p]

      method pat ~p ~span:_ ~typ:_ = p#p

      method pat'_PBinding ~super:_ ~mut:_ ~mode:_ ~var ~typ:_ ~subpat:_ =
        var#p

      method item'_Type_enum ~super:_ ~name ~generics:_ ~variants =
        sexprlist [
          string "declare-datatype";
          name#p;
          sexprlist (ps variants) ]

      method item'_Enum_Variant ~name ~arguments ~is_record:_ ~attrs:_ =
            let constructor_name =  name#p in
            let fields = List.map
              ~f:(fun (field_name, field_ty, attr) -> sexprlist [field_name#p;field_ty#p ])
              arguments in

        sexprlist ( constructor_name :: fields )

      method item'_Type_struct ~super ~name ~generics:_ ~tuple_struct:_
          ~arguments =
            match super.v with
              | Type { variants = [{name = constructor_name;_}]; _ } ->
                let constructor_name = Concrete_ident.DefaultViewAPI.render constructor_name in
                let constructor_name = self#concrete_ident false constructor_name in
                let fields = List.map
                  ~f:(fun (field_name, field_ty, attr) -> sexprlist [(destructor_name field_name#p); field_ty#p ])
                  arguments in

                sexprlist [
                  string "declare-datatype";
                  name#p;
                  sexprlist [ sexprlist(constructor_name :: fields)]
                ]
              | _ -> failwith "expected a type here"

      method item'_Use ~super:_ ~path ~is_external:_ ~rename:_ =
        string ";; skipping use of path " ^^ separate (string "::") (List.map ~f:string path) ^^ string "\n"

      method item'_NotImplementedYet =
        string ";; skipping unimplemented item emitted by hax-engine\n"

      method impl_item ~ii_span:_ ~ii_generics:_ ~ii_v:_ ~ii_ident ~ii_attrs:_
          = concat [ string ";; skipping impl item with name \""; ii_ident#p; string "\"\n"]

      method ty_TApp_application ~typ ~generics =
        if (List.is_empty generics)
          then typ#p
          else sexprlist (typ#p :: (ps generics))

      method ty_TInt _x1 = string "Int"
      method ty_TBool = string "Bool"

      method item'_Impl ~super:_ ~generics:_ ~self_ty:_ ~of_trait:_ ~items
          ~parent_bounds:_ ~safety:_ =
        separate_map (break 1) p items

      method expr ~e ~span:_ ~typ:_ = e#p

      method expr'_App_application ~super:_ ~f ~args ~generics:_ =
        if (List.is_empty args)
          then f#p
          else sexprlist (f#p :: (ps args))

      (* This will need a phase for maing deep matches shallow *)
      method expr'_Match ~super:_ ~scrutinee ~arms =
        sexprlist [
          string "match";
          scrutinee#p;
          sexprlist (ps arms)
          ]

      method expr'_GlobalVar_concrete ~super:_ _x2 =
        _x2#p

      method concrete_ident ~local:_ id : document =
          (match id.name with
          | "f_not" -> string  "not"
          | "f_eq" -> string  "="
          | "f_lt" -> string  "<"
          | "f_gt" -> string  ">"
          | "f_le" -> string  "<="
          | "f_ge" -> string  ">="
          | "f_add" -> string  "+"
          | "f_mul" -> string  "*"
          | "f_div" -> string  "/"
          | def -> slashpathview id.path def)

      method expr'_LocalVar ~super:_ _x2 = _x2#p


      method expr'_App_field_projection ~super:_ ~field ~e =
        sexprlist [(destructor_name field#p); e#p ]

      method expr'_Construct_inductive ~super ~constructor ~is_record:_
          ~is_struct ~fields ~base:_ =
        let constructor = if is_struct
          then constructor#p
          else constructor#p in
        let constructor = sexprlist [string "as" ; constructor; self#print_ty AstPos_expr__e super.typ] in
        if (List.is_empty fields)
          then constructor
          else sexprlist (constructor :: ps (List.map ~f:(fun (name, expr) -> expr ) fields))

      method expr'_Construct_tuple ~super:_ ~components =
        if ((List.length components) = 1)
          then (tuple_constructor_name components)
          else sexprlist ((tuple_constructor_name components) :: (ps components))

      method arm ~arm ~span:_ = arm#p

      method arm' ~super:_ ~arm_pat ~body ~guard:_ =
        sexprlist [ arm_pat#p ; body#p ]

      method pat'_PConstruct_inductive ~super:_ ~constructor ~is_record:_
          ~is_struct:_ ~fields =
        sexprlist (constructor#p :: ps (List.map ~f:(fun (name, expr) -> expr ) fields))

      method expr'_Let ~super:_ ~monadic:_ ~lhs ~rhs ~body =
        sexprlist [string "let"; sexprlist [ sexprlist [ lhs#p ; rhs#p ]]; body#p]

      method expr'_Literal ~super:_ _x2 = _x2#p

      method literal_Int ~value ~negative:_ ~kind:_ =
        string value

      method literal_Bool _x1 = string (if _x1 then "true" else "false")

      method pat'_PWild = string "_"

      method expr'_GlobalVar_primitive ~super _x2 = (match _x2 with
        | Deref -> string "(todo globalvar primitive deref)"
        | Cast -> string "(todo globalvar primitive cast)"
        | LogicalOp And -> string "and"
        | LogicalOp Or -> string "or")

      method generic_value_GType _x1 =
        _x1#p

      method ty_TApp_tuple ~types = if List.is_empty types
        then string "Tuple0"
        else sexprlist ((utf8format "Tuple%i" (List.length types) ) :: List.map ~f:(self#print_ty AstPos_expr__e) types)

      (*
       *
       *
       *
       *
       *
       * ###############
       * BEGIN GENERATED
       * ###############
       *
       *
       *
       *
       *
       *
       *)

      method impl_expr ~kind:_ ~goal:_ = default_document_for "impl_expr"

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

      method expr'_App_constant ~super:_ ~constant:_ ~generics:_ =
        default_document_for "expr'_App_constant"

      method expr'_App_tuple_projection ~super:_ ~size:_ ~nth:_ ~e:_ =
        default_document_for "expr'_App_tuple_projection"

      method expr'_Ascription ~super:_ ~e:_ ~typ:_ =
        default_document_for "expr'_Ascription"

      method expr'_Block ~super:_ ~e:_ ~safety_mode:_ ~witness:_ =
        default_document_for "expr'_Block"

      method expr'_Borrow ~super:_ ~kind:_ ~e:_ ~witness:_ =
        default_document_for "expr'_Borrow"

      method expr'_AddressOf ~super:_ ~mut:_ ~e:_ ~witness:_ =
        default_document_for "expr'_AddressOf"

      method expr'_Assign ~super:_ ~lhs:_ ~e:_ ~witness:_ =
        default_document_for "expr'_Assign"

      method expr'_Break ~super:_ ~e:_ ~acc:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Break"

      method expr'_Closure ~super:_ ~params:_ ~body:_ ~captures:_ =
        default_document_for "expr'_Closure"

      method expr'_Continue ~super:_ ~acc:_ ~label:_ ~witness:_ =
        default_document_for "expr'_Continue"

      method expr'_EffectAction ~super:_ ~action:_ ~argument:_ =
        default_document_for "expr'_EffectAction"

      method expr'_Loop ~super:_ ~body:_ ~kind:_ ~state:_ ~control_flow:_
          ~label:_ ~witness:_ =
        default_document_for "expr'_Loop"

      method expr'_MacroInvokation ~super:_ ~macro:_ ~args:_ ~witness:_ =
        default_document_for "expr'_MacroInvokation"


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

      method generics ~params:_ ~constraints:_ = default_document_for "generics"
      method guard ~guard:_ ~span:_ = default_document_for "guard"

      method guard'_IfLet ~super:_ ~lhs:_ ~rhs:_ ~witness:_ =
        default_document_for "guard'_IfLet"

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

      method impl_item'_IIFn ~body:_ ~params:_ =
        default_document_for "impl_item'_IIFn"

      method impl_item'_IIType ~typ:_ ~parent_bounds:_ =
        default_document_for "impl_item'_IIType"


      method item'_Alias ~super:_ ~name:_ ~item:_ =
        default_document_for "item'_Alias"

      method item'_HaxError ~super:_ _x2 = default_document_for "item'_HaxError"

      method item'_IMacroInvokation ~super:_ ~macro:_ ~argument:_ ~span:_
          ~witness:_ =
        default_document_for "item'_IMacroInvokation"

      method item'_Quote ~super:_ ~quote:_ ~origin:_ =
        default_document_for "item'_Quote"

      method item'_Trait ~super:_ ~name:_ ~generics:_ ~items:_ ~safety:_ =
        default_document_for "item'_Trait"

      method item'_TyAlias ~super:_ ~name:_ ~generics:_ ~ty:_ =
        default_document_for "item'_TyAlias"

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

      method literal_Char _x1 = default_document_for "literal_Char"

      method literal_Float ~value:_ ~negative:_ ~kind:_ =
        default_document_for "literal_Float"

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

      method pat'_PAscription ~super:_ ~typ:_ ~typ_span:_ ~pat:_ =
        default_document_for "pat'_PAscription"

      method pat'_PConstant ~super:_ ~lit:_ =
        default_document_for "pat'_PConstant"


      method pat'_PConstruct_tuple ~super:_ ~components:_ =
        default_document_for "pat'_PConstruct_tuple"

      method pat'_PDeref ~super:_ ~subpat:_ ~witness:_ =
        default_document_for "pat'_PDeref"

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

      method ty_TArray ~typ:_ ~length:_ = default_document_for "ty_TArray"
      method ty_TArrow _x1 _x2 = default_document_for "ty_TArrow"

      method ty_TAssociatedType ~impl:_ ~item:_ =
        default_document_for "ty_TAssociatedType"

      method ty_TChar = default_document_for "ty_TChar"
      method ty_TDyn ~witness:_ ~goals:_ = default_document_for "ty_TDyn"
      method ty_TFloat _x1 = default_document_for "ty_TFloat"
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
           let header = pure (hardcoded_smtlib_headers ^ "\n") in
           let annotated = concat header annotated in
           (to_sourcemap annotated, to_string annotated)
         in
         let sourcemap = Some sourcemap in
         let path = mod_name ^ ".smt2" in
         Types.{ path; contents; sourcemap })

open Phase_utils

module TransformToInputLanguage =
  [%functor_application
    Phases.Reject.RawOrMutPointer(Features.Rust)
  |> Phases.Transform_hax_lib_inline
  |> Phases.Specialize
  |> Phases.Drop_sized_trait
  |> Phases.Simplify_question_marks
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_asserts
  |> Phases.Reconstruct_for_loops
  |> Phases.Reconstruct_while_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
  |> Phases.Drop_match_guards
  |> Phases.Drop_references
  |> Phases.Trivialize_assign_lhs
  |> Side_effect_utils.Hoist
  |> Phases.Hoist_disjunctive_patterns
  |> Phases.Simplify_match_return
  |> Phases.Local_mutation
  |> Phases.Rewrite_control_flow
  |> Phases.Drop_return_break_continue
  |> Phases.Functionalize_loops
  |> Phases.Reject.Question_mark
  |> Phases.Reject.As_pattern
  |> Phases.Traits_specs
  |> Phases.Simplify_hoisting
  |> Phases.Newtype_as_refinement
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
