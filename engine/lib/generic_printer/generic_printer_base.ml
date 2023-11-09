open! Prelude
open! Ast
open PPrint

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
end

type annot_str = string * Annotation.t list [@@deriving show, yojson, eq]

(** When printing a chunk of AST, should we wrap parenthesis
({!NeedsPar}) or not ({!AlreadyPar})? *)
type par_state = NeedsPar | AlreadyPar

type literal_ctx = Pat | Expr

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  module U = Ast_utils.Make (F)
  open Ast.Make (F)

  type 't fn = 't -> document

  (** Raw generic printers base class. Those are useful for building a
  printer, not for consuming printers. Consumers should use
  the {!module:Api} functor. *)
  class virtual print_base =
    object (print)
      val mutable current_span = Span.default
      val mutable span_data : Annotation.t list = []
      val mutable current_namespace : (string * string list) option = None
      method get_span_data () = span_data

      method with_span ~span f =
        let prev_span = current_span in
        current_span <- span;
        let doc = f () |> print#spanned_doc |> custom in
        current_span <- prev_span;
        doc

      method spanned_doc (doc : document) : custom =
        let span = current_span in
        object
          method requirement : requirement = requirement doc

          method pretty : output -> state -> int -> bool -> unit =
            fun o s i b ->
              span_data <-
                ({ line = s.line; col = s.column }, span) :: span_data;
              pretty o s i b doc

          method compact : output -> unit = fun o -> compact o doc
        end

      method concrete_ident : concrete_ident fn =
        fun id ->
          let current_ns = print#get_current_namespace () in
          let id_ns = print#namespace_of_concrete_ident id in
          print#concrete_ident'
            ~under_current_ns:
              ([%equal: (string * string list) option] current_ns (Some id_ns))
            id

      method assertion_failure : 'any. string -> 'any =
        fun details ->
          let span = Span.to_thir current_span in
          let kind = Types.AssertionFailure { details } in
          let ctx = Diagnostics.Context.GenericPrinter print#printer_name in
          Diagnostics.SpanFreeError.raise ~span ctx kind

      method set_current_namespace ns = current_namespace <- ns
      method get_current_namespace () = current_namespace

      (* `*_at` variants *)
      method expr_at : ast_position -> expr fn = print#par_state >> print#expr
      method ty_at : ast_position -> ty fn = print#par_state >> print#ty
      method pat_at : ast_position -> pat fn = print#par_state >> print#pat

      method pat : par_state -> pat fn =
        fun ctx { p; span; _ } ->
          print#with_span ~span (fun _ -> print#pat' ctx p)

      method item_unwrapped : item fn = fun { v; _ } -> print#item' v

      method generic_param : generic_param fn =
        fun ({ span; _ } as p) ->
          print#with_span ~span (fun _ -> print#generic_param' p)

      method arm : arm fn =
        fun { arm; span } -> print#with_span ~span (fun _ -> print#arm' arm)

      method ty : par_state -> ty fn =
        fun _ctx ty ->
          match ty with
          | TApp { ident = `Concrete ident; args } ->
              print#ty_app ident args |> group
          | TApp
              {
                ident =
                  `Primitive _ | `TupleCons _ | `TupleField _ | `Projector _;
                _;
              } ->
              print#assertion_failure "TApp not concrete"
          | TApp { ident = `TupleType n; args } ->
              let args =
                List.filter_map
                  ~f:(function GType t -> Some t | _ -> None)
                  args
              in
              if [%equal: int] (List.length args) n |> not then
                print#assertion_failure "malformed ty app tuple";
              print#ty_tuple n args
          | TApp _ -> .
          | _ ->
              print#assertion_failure "default ty is only implemented for TApp"

      method expr' : par_state -> expr' fn =
        fun _ctx e ->
          match e with
          | App { f = { e = GlobalVar i; _ } as f; args; generic_args } -> (
              let expect_one_arg where =
                match args with
                | [ arg ] -> arg
                | _ -> print#assertion_failure @@ "Expected one arg at " ^ where
              in
              match i with
              | `Concrete _ | `Primitive _ -> print#expr_app f args generic_args
              | `TupleType _ | `TupleCons _ | `TupleField _ ->
                  print#assertion_failure "App: unexpected tuple"
              | `Projector (`TupleField (nth, size)) ->
                  let arg = expect_one_arg "projector tuple field" in
                  print#tuple_projection ~size ~nth arg
              | `Projector (`Concrete i) ->
                  let arg = expect_one_arg "projector concrete" in
                  print#field_projection i arg)
          | App { f; args; generic_args } -> print#expr_app f args generic_args
          | Construct { constructor; fields; base; is_record; is_struct } -> (
              match constructor with
              | `Concrete constructor ->
                  print#expr_construct_inductive ~is_record ~is_struct
                    ~constructor ~base fields
              | `TupleCons _ ->
                  List.map ~f:snd fields |> print#expr_construct_tuple
              | `Primitive _ | `TupleType _ | `TupleField _ | `Projector _ ->
                  print#assertion_failure "Construct unexpected constructors")
          | App _ | Construct _ -> .
          | _ ->
              print#assertion_failure
                "default expr' is only implemented for App and Construct"

      method pat' : par_state -> pat' fn =
        fun _ -> function
          | PConstant { lit } -> print#literal Pat lit
          | PConstruct { name; args; is_record; is_struct } -> (
              match name with
              | `Concrete constructor ->
                  print#doc_construct_inductive ~is_record ~is_struct
                    ~constructor ~base:None
                    (List.map
                       ~f:(fun fp ->
                         (fp.field, print#pat_at Pat_ConcreteInductive fp.pat))
                       args)
              | `TupleCons _ ->
                  List.map ~f:(fun fp -> fp.pat) args
                  |> print#pat_construct_tuple
              | `Primitive _ | `TupleType _ | `TupleField _ | `Projector _ ->
                  print#assertion_failure "todo err")
          | _ ->
              print#assertion_failure
                "default pat' is only implemented for PConstant and PConstruct"

      method expr : par_state -> expr fn =
        fun ctx e ->
          let span = e.span in
          print#with_span ~span (fun _ ->
              try print#expr_unwrapped ctx e
              with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
                U.hax_failure_expr span e.typ (context, kind)
                  (U.LiftToFullAst.expr e)
                (* TODO: if the printer is extremely broken, this results in a stack overflow *)
                |> print#expr ctx)

      method item : item fn =
        fun i ->
          print#set_current_namespace
            (print#namespace_of_concrete_ident i.ident |> Option.some);
          try print#item_unwrapped i
          with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
            let error = Diagnostics.pretty_print_context_kind context kind in
            let cast_item : item -> Ast.Full.item = Stdlib.Obj.magic in
            let ast = cast_item i |> Print_rust.pitem_str in
            let msg = error ^ "\nLast available AST for this item:\n\n" ^ ast in
            (* TODO: if the printer is extremely broken, this results in a stack overflow *)
            make_hax_error_item i.span i.ident msg |> print#item

      method items : item list fn = separate_map (twice hardline) print#item
      method attrs : attrs fn = separate_map hardline print#attr
    end

  type print_object =
    < printer_name : string
    ; get_span_data : unit -> Annotation.t list
    ; ty : par_state -> ty fn
    ; pat : par_state -> pat fn
    ; arm : arm fn
    ; expr : par_state -> expr fn
    ; item : item fn
    ; items : item list fn >
  (** In the end, an printer *object* should be of the type {!print_object}. *)

  class type print_class =
    object
      inherit print_base
      method printer_name : string
      method get_span_data : unit -> Annotation.t list

      method namespace_of_concrete_ident :
        concrete_ident -> string * string list

      method par_state : ast_position -> par_state
      method concrete_ident' : under_current_ns:bool -> concrete_ident fn
      method concrete_ident : concrete_ident fn
      method name_of_concrete_ident : concrete_ident fn
      method mutability : 'a. 'a mutability fn
      method primitive_ident : primitive_ident fn
      method local_ident : local_ident fn
      method literal : literal_ctx -> literal fn
      method generic_value : generic_value fn
      method lhs : lhs fn
      method ty_bool : document
      method ty_char : document
      method ty_str : document
      method ty_int : int_kind fn
      method ty_float : float_kind fn
      method generic_values : generic_value list fn
      method ty_app : concrete_ident -> generic_value list fn
      method ty_tuple : int -> ty list fn
      method ty : par_state -> ty fn
      method expr' : par_state -> expr' fn

      method expr_monadic_let :
        monad:supported_monads * F.monadic_binding ->
        lhs:pat ->
        rhs:expr ->
        expr fn

      method expr_let : lhs:pat -> rhs:expr -> expr fn
      method tuple_projection : size:int -> nth:int -> expr fn
      method field_projection : concrete_ident -> expr fn
      method expr_app : expr -> expr list -> generic_value list fn
      method doc_construct_tuple : document list fn
      method expr_construct_tuple : expr list fn
      method pat_construct_tuple : pat list fn
      method global_ident_projector : global_ident fn

      method doc_construct_inductive :
        is_record:bool ->
        is_struct:bool ->
        constructor:concrete_ident ->
        base:document option ->
        (global_ident * document) list fn

      method expr_construct_inductive :
        is_record:bool ->
        is_struct:bool ->
        constructor:concrete_ident ->
        base:(expr * F.construct_base) option ->
        (global_ident * expr) list fn

      method attr : attr fn
      method attrs : attrs fn
      method pat' : par_state -> pat' fn
      method pat_ascription : typ:ty -> typ_span:span -> pat fn
      method pat : par_state -> pat fn
      method expr_unwrapped : par_state -> expr fn
      method param : param fn
      method item' : item' fn
      method item_unwrapped : item fn
      method generic_param' : generic_param fn
      method generic_param : generic_param fn
      method generic_params : generic_param list fn
      method arm' : arm' fn
      method arm : arm fn
      method expr : par_state -> expr fn
      method item : item fn
      method items : item list fn
    end

  module type API = sig
    val items : item list -> annot_str
    val item : item -> annot_str
    val expr : expr -> annot_str
    val pat : pat -> annot_str
    val ty : ty -> annot_str
  end

  module Api (NewPrint : sig
    val new_print : unit -> print_object
  end) =
  struct
    open NewPrint

    let mk (f : print_object -> 'a -> PPrint.document) (x : 'a) : annot_str =
      let printer = new_print () in
      let doc = f printer x in
      let buf = Buffer.create 0 in
      PPrint.ToBuffer.pretty 1.0 80 buf doc;
      (Buffer.contents buf, printer#get_span_data ())

    let items : item list -> annot_str = mk (fun p -> p#items)
    let item : item -> annot_str = mk (fun p -> p#item)
    let expr : expr -> annot_str = mk (fun p -> p#expr AlreadyPar)
    let pat : pat -> annot_str = mk (fun p -> p#pat AlreadyPar)
    let ty : ty -> annot_str = mk (fun p -> p#ty AlreadyPar)
  end
end
