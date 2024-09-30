[@@@warning "-37-34-27"]

open! Prelude
open! Ast
open PPrint

module Types = struct
  (** Generic printer for the {!module:Ast} ASTs. It uses the [PPrint]
library, and additionaly computes {!Annotation.t}.  *)

  (** Identifies a position in the AST. This is useful for figuring out
wether we should wrap a chunk of AST in parenthesis. or not *)
  type ast_position =
    | GenericValue_GType
    | GenericValue_GConst
    | Lhs_LhsArbitraryExpr
    | Lhs_LhsArrayAccessor
    | Ty_TArrow
    | Ty_TRef
    | Ty_Tuple
    | Ty_TSlice
    | Ty_TArray_typ
    | Ty_TArray_length
    | Expr_If_cond
    | Expr_If_then
    | Expr_If_else
    | Expr_Array
    | Expr_Assign
    | Expr_Closure_param
    | Expr_Closure_body
    | Expr_Ascription_e
    | Expr_Ascription_typ
    | Expr_Let_lhs
    | Expr_Let_rhs
    | Expr_Let_body
    | Expr_Match_scrutinee
    | Expr_QuestionMark
    | Expr_Borrow
    | Expr_TupleProjection
    | Expr_ConstructTuple
    | Expr_FieldProjection
    | Expr_App_f
    | Expr_App_arg
    | Expr_ConcreteInductive_base
    | Expr_ConcreteInductive_field
    | Pat_PBinding_subpat
    | Pat_PDeref
    | Pat_PArray
    | Pat_ConstructTuple
    | Pat_ConcreteInductive
    | Pat_Ascription_pat
    | Pat_Ascription_typ
    | Pat_Or
    | Param_pat
    | Param_typ
    | GenericParam_GPType
    | GenericParam_GPConst
    | Arm_pat
    | Arm_body
    | Item_Fn_body
  [@@warning "-37"]

  module Annotation = struct
    type loc = { line : int; col : int } [@@deriving show, yojson, eq]
    type t = loc * span [@@deriving show, yojson, eq]

    let compare ((a, _) : t) ((b, _) : t) : int =
      let line = Int.compare a.line b.line in
      if Int.equal line 0 then Int.compare a.col b.col else line

    (** Converts a list of annotation and a string to a list of annotated string *)
    let split_with_string (s : string) (annots : t list) =
      let lines_position =
        String.to_list s
        |> List.filter_mapi ~f:(fun i ch ->
               match ch with '\n' -> Some i | _ -> None)
        |> List.to_array |> Array.get
      in
      let annots = List.sort ~compare annots in
      let init = ({ line = 0; col = 0 }, None) in
      let slices =
        List.folding_map
          ~f:(fun (start, start_span) (end_, end_span) ->
            let span = Option.value ~default:end_span start_span in
            ((end_, Some end_span), (span, start, end_)))
          ~init annots
      in
      List.map slices ~f:(fun (span, start, end_) ->
          let pos = lines_position start.line + start.col in
          let len = lines_position end_.line + end_.col - pos in
          (span, String.sub s ~pos ~len))

    let to_mapping ((loc, span) : t) : Sourcemaps.Source_maps.mapping option =
      let real_path (x : Types.file_name) =
        match x with
        | Real (LocalPath p) | Real (Remapped { local_path = Some p; _ }) ->
            Some p
        | _ -> None
      in
      let loc_to_loc ({ line; col } : loc) : Sourcemaps.Location.t =
        { line; col }
      in
      let to_loc ({ col; line } : Types.loc) : loc =
        { col = Int.of_string col; line = Int.of_string line - 1 }
      in
      let* span =
        Span.to_thir span
        |> List.find ~f:(fun (s : Types.span) ->
               real_path s.filename |> Option.is_some)
      in
      let* src_filename = real_path span.filename in
      let src_start = to_loc span.lo |> loc_to_loc in
      let src_end = to_loc span.hi |> loc_to_loc in
      let dst_start = loc_to_loc loc in
      Some
        Sourcemaps.Source_maps.
          {
            src = { start = src_start; end_ = Some src_end };
            gen = { start = dst_start; end_ = None };
            source = src_filename;
            name = None;
          }
  end

  type annot_str = string * Annotation.t list [@@deriving show, yojson, eq]

  (** When printing a chunk of AST, should we wrap parenthesis
({!NeedsPar}) or not ({!AlreadyPar})? *)
  type par_state = NeedsPar | AlreadyPar

  type 't fn = 't -> document
end

open Types

module Make
    (F : Features.T) (SecretTypes : sig
      type 't no_override
      type 'location no_direct_call
    end) =
struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  open SecretTypes

  (** Raw generic printers base class. Those are useful for building a
  printer, not for consuming printers. Consumers should use
  the {!module:Api} functor. *)
  class type virtual print_base_type =
    object

      (** {1 Span handling} *)

      (** Every piece of string rendered is contextualized with span information automatically. *)

      method get_span_data : unit -> Annotation.t list
      (** Retreive the mapping between locations in the rendered
      string and Rust locations. *)

      method with_span : span:span -> (unit -> document) -> document
      (** [with_span ~span f] runs `f` in the context of [span]. *)

      method spanned_doc : document -> custom
      (** [spanned_doc doc] constructs a custom wrapping document for
      [doc]. Rendering this document in [pretty] mode has a
      side-effect: we push a [Annotation.t] to internal state. An
      annotation maps a location within the rendered string to a Rust
      span (that is, a location in the original Rust source code). *)

      (** {1 [*_at] methods} *)

      (** Always use [<name>_at] methods rather than [<name>]
      ones. The former takes an [ast_position], that contextualizes
      from where we are printing something. Printing the body of a
      [let .. = ..;] expression (position [Expr_Let_body]) and
      printing a function argument (position [Expr_App_arg]) will
      probably require different parenthesizing: [ast_position] gives
      contextual information upon which such parenthesizing decisions
      can be taken. *)

      method expr_at : ast_position -> expr fn
      (** Renders an [expr] at some [ast_position]. *)

      method ty_at : ast_position -> ty fn
      (** Renders a [ty] at some [ast_position]. *)

      method pat_at : ast_position -> pat fn
      (** Renders a [pat] at some [ast_position]. *)

      (** {1 Driver methods} *)

      (** The methods in this section are defined in two flavors:
          `<name>` and `<name>_`. `<name>` methods are not
          overridable. Indeed, they take care of various things for
          you:
          
          {ul {- catch exceptions and translate them as
          pretty-printed errors with the original Rust AST;}
              {- set contextual span information in a systematic way;}
              {- disambiguate certain variant of the AST (see {!section-"specialized-printers"}).}}

         Your can override `<name>_` methods.
      *)

      (** {2 Expressions} *)
      method expr : (par_state -> expr fn) no_override
      (** Prints an expression. Pre-handles the variants [App] and
      [Construct]: see {!section-"specialize-expr"}. *)

      method virtual expr_ : [ `Expr ] no_direct_call -> par_state -> expr fn
      (** Overridable printer for expressions. Please mark the cases
      [App] and [Construct] as unreachable. *)

      (** {2 Types} *)
      method ty : (par_state -> ty fn) no_override
      (** Prints a type. Pre-handles [TApp]. *)

      method virtual ty_ : [ `Ty ] no_direct_call -> par_state -> ty fn
      (** Overridable printer for types. Please mark the case [TApp]
      as unreachable. *)

      (** {2 Patterns} *)
      method pat : (par_state -> pat fn) no_override
      (** Prints a pattern. *)

      method virtual pat_ : [ `Pat ] no_direct_call -> par_state -> pat fn
      (** Overridable printer for patterns. *)

      (** {2 Items} *)
      method item : item fn no_override
      (** Prints a item. *)

      method virtual item_ : [ `Item ] no_direct_call -> item fn
      (** Overridable printer for items. *)

      (** {2 Arms} *)
      method arm : arm fn no_override
      (** Prints an arm (in a match). *)

      method virtual arm_ : [ `Arm ] no_direct_call -> arm fn
      (** Overridable printer for arms (in matches).*)

      (** {2 Generic parameters} *)
      method generic_param : generic_param fn no_override
      (** Prints a generic parameter. *)

      method virtual generic_param_ : [ `GP ] no_direct_call -> generic_param fn
      (** Overridable printer for generic parameters. *)

      (** {2 Parameters} *)
      method param_ty : param fn no_override
      (** Prints the type of a parameter. This is special because of `typ_span`. *)

      method virtual param_ty_ : [ `Param ] no_direct_call -> param fn
      (** Overridable printer for parameter types. *)

      (** {2 Impl items} *)
      method impl_item : impl_item fn no_override
      (** Prints an impl item. *)

      method virtual impl_item_ : [ `II ] no_direct_call -> impl_item fn
      (** Overridable printer for impl items. *)

      (** {2 Trait items} *)
      method trait_item : trait_item fn no_override
      (** Prints an trait item. *)

      method virtual trait_item_ : [ `TI ] no_direct_call -> trait_item fn
      (** Overridable printer for trait items. *)

      (** {2 Attributes} *)

      method attr : attr fn no_override
      (** Prints an attribute. *)

      method virtual attr_ : [ `Attr ] no_direct_call -> attr fn
      (** Overridable printer for attributes. *)

      (** {2 Concrete idents} *)

      method concrete_ident : concrete_ident fn no_override
      (** Prints a concrete ident. *)

      method virtual concrete_ident_ :
        [ `CIdent ] no_direct_call -> under_current_ns:bool -> concrete_ident fn
      (** Overridable printer for concrete idents. *)

      (** {1:specialized-printers Specialized printers} *)

      (** Some nodes in the AST are ambiguous as they encode multiple
      language constructs: the `App` constructor of `expr` for
      instance encodes (1) function applications, (2) fields
      projectors, (3) constants... This is the same for `Construct`,
      `TApp`, and some other.

      This section defines specialized methods for those language
      constructs. When the variant `<Variant>` of a type `<type>` in
      the AST is encoding various language constructs, we defined
      various methods named `<type>_<Variant>_<name>`. *)

      (** {2:specialize-expr Specialized printers for [expr]} *)

      method virtual expr_App_constant :
        full:expr -> concrete_ident -> generic_value list fn
      (** [expr_App_constant ~full e generics] prints the constant
      [e] with generics [generics]. [full] is the unspecialized [expr]. *)

      method virtual expr_App_application :
        full:expr -> expr -> expr list -> generic_value list fn
      (** [expr_App_application ~full e args generics] prints the
      function application [e<...generics>(...args)]. [full] is the unspecialized [expr]. *)

      method virtual expr_App_tuple_projection :
        full:expr -> size:int -> nth:int -> expr fn
      (** [expr_App_tuple_projection ~full ~size ~nth expr] prints
      the projection of the [nth] component of the tuple [expr] of
      size [size]. [full] is the unspecialized [expr]. *)

      method virtual expr_App_field_projection :
        full:expr -> concrete_ident -> expr fn
      (** [expr_App_field_projection ~full field expr] prints the
      projection of the field [field] in the expression [expr]. [full]
      is the unspecialized [expr]. *)

      method virtual expr_Construct_inductive :
        full:expr ->
        is_record:bool ->
        is_struct:bool ->
        constructor:concrete_ident ->
        base:(expr * F.construct_base) option ->
        (global_ident * expr) list fn
      (** [expr_Construct_inductive ~full ~is_record ~is_struct
      ~constructor ~base fields] prints the construction of an
      inductive with base [base] and fields [fields]. [full] is the
      unspecialized [expr]. TODO doc is_record is_struct *)

      method virtual expr_Construct_tuple : full:expr -> expr list fn

      (** {2:specialize-expr Specialized printers for [ty]} *)

      method virtual ty_TApp_tuple : full:ty -> ty list fn
      (** [ty_TApp_tuple ~full types] prints a tuple type with
      compounds types [types]. [full] is the unspecialized [ty]. *)

      method virtual ty_TApp_application :
        full:ty -> concrete_ident -> generic_value list fn
      (** [ty_TApp_application ~full typ generic_args] prints the type
      [typ<...generic_args>]. [full] is the unspecialized [ty]. *)

      method items : item list fn

      (** {1 Misc methods} *)

      (** {1 Convenience methods} *)

      method attrs : attrs fn

      method assertion_failure : 'any. string -> 'any
      (** Helper that throws and reports an [Types.AssertionFailure] error. *)

      method set_current_namespace : (string * string list) option -> unit
      method get_current_namespace : unit -> (string * string list) option

      method virtual namespace_of_concrete_ident :
        concrete_ident -> string * string list

      method virtual printer_name : string
      method virtual par_state : ast_position -> par_state

      method unreachable : 'any. unit -> 'any
      (** Mark an unreachable place in the printer. *)
    end
end
