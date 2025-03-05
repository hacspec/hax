open! Prelude
open! Ast

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open AST

  open struct
    module Gen = Ast_builder_generated.Make (F)
  end

  module type SPAN = Gen.SPAN

  include Gen.Explicit

  module NoSpan = struct
    let ty_tuple (types : ty list) : ty =
      let ident = `TupleType (List.length types) in
      let args = List.map ~f:(fun typ -> GType typ) types in
      TApp { ident; args }

    let ty_tuple_or_id : ty list -> ty = function
      | [ ty ] -> ty
      | types -> ty_tuple types

    (** This gives the type of a value in the `ControlFlow` enum *)
    let ty_cf ~(continue_type : ty) ~(break_type : ty) : ty =
      TApp
        {
          ident =
            Global_ident.of_name ~value:false
              Core__ops__control_flow__ControlFlow;
          args = [ GType break_type; GType continue_type ];
        }

    (** This gives the type of a value encoded in the `ControlFlow` enum.
       In case a `return_type` is provided the encoding is nested:
       `return v` is `Break (Break v)` 
       `break v` is `Break (Continue (v, acc))` *)
    let ty_cf_return ~(acc_type : ty) ~(break_type : ty)
        ~(return_type : ty option) : ty =
      let break_type = ty_tuple [ break_type; acc_type ] in
      match return_type with
      | Some ret_ty ->
          let break_type = ty_cf ~break_type:ret_ty ~continue_type:break_type in
          ty_cf ~break_type ~continue_type:acc_type
      | None -> ty_cf ~break_type ~continue_type:acc_type
  end

  include NoSpan

  module Explicit = struct
    let ty_unit : ty = TApp { ident = `TupleType 0; args = [] }
    let expr_unit = expr_GlobalVar (`TupleCons 0) ~typ:ty_unit

    let expr_tuple ~(span : span) (tuple : expr list) =
      let len = List.length tuple in
      let fields = List.mapi ~f:(fun i x -> (`TupleField (i, len), x)) tuple in
      let typ = NoSpan.ty_tuple @@ List.map ~f:(fun { typ; _ } -> typ) tuple in
      expr_Construct ~span ~typ ~constructor:(`TupleCons len) ~is_record:false
        ~is_struct:true ~fields ~base:None

    let pat_PBinding ~typ = pat_PBinding ~inner_typ:typ ~typ

    let arm ~span arm_pat ?(guard = None) body =
      { arm = { arm_pat; body; guard }; span }

    let pat_Constructor_CF ~(span : span) ~(typ : ty)
        (cf : [ `Break | `Continue ]) (pat : pat) =
      match cf with
      | `Break ->
          {
            p =
              PConstruct
                {
                  constructor =
                    Global_ident.of_name ~value:true
                      Core__ops__control_flow__ControlFlow__Break;
                  fields =
                    [
                      {
                        field =
                          Global_ident.of_name ~value:true
                            Core__ops__control_flow__ControlFlow__Break__0;
                        pat;
                      };
                    ];
                  is_record = false;
                  is_struct = false;
                };
            typ;
            span;
          }
      | `Continue ->
          {
            p =
              PConstruct
                {
                  constructor =
                    Global_ident.of_name ~value:true
                      Core__ops__control_flow__ControlFlow__Continue;
                  fields =
                    [
                      {
                        field =
                          Global_ident.of_name ~value:true
                            Core__ops__control_flow__ControlFlow__Continue__0;
                        pat;
                      };
                    ];
                  is_record = false;
                  is_struct = false;
                };
            typ;
            span;
          }

    let call_Constructor' (constructor : global_ident) is_struct
        (args : expr list) span ret_typ =
      let mk_field =
        let len = List.length args in
        fun n -> `TupleField (len, n)
      in
      let fields = List.mapi ~f:(fun i arg -> (mk_field i, arg)) args in
      {
        e =
          Construct
            { constructor; is_record = false; is_struct; fields; base = None };
        typ = ret_typ;
        span;
      }

    let call_Constructor (constructor_name : Concrete_ident.name)
        (is_struct : bool) (args : expr list) span ret_typ =
      call_Constructor'
        (`Concrete (Concrete_ident.of_name ~value:true constructor_name))
        is_struct args span ret_typ

    let expr'_Constructor_CF ~(span : span) ~(break_type : ty)
        ?(continue_type : ty = ty_unit) (cf : [ `Break | `Continue ]) (e : expr)
        =
      let typ = NoSpan.ty_cf ~continue_type ~break_type in
      match cf with
      | `Break ->
          call_Constructor Core__ops__control_flow__ControlFlow__Break false
            [ e ] span typ
      | `Continue ->
          call_Constructor Core__ops__control_flow__ControlFlow__Continue false
            [ e ] span typ

    (** We use the following encoding of return, break and continue in the `ControlFlow` enum:
       Return e -> Break (Break e)
       Break e -> Break ((Continue(e, acc)))
       Continue -> Continue(acc)

       In case there is no return we simplify to:
        Break e -> (Break (e, acc))
        Continue -> (continue (acc))
    *)
    let expr_Constructor_CF ~(span : span) ~(break_type : ty option)
        ~(return_type : ty option) ~(acc : expr) ?(e : expr = expr_unit ~span)
        (cf : [ `Return | `Break | `Continue ]) =
      let break_type = Option.value ~default:ty_unit break_type in
      match cf with
      | `Return ->
          let continue_type = NoSpan.ty_tuple [ break_type; acc.typ ] in
          let inner =
            expr'_Constructor_CF ~break_type:e.typ ~continue_type ~span `Break e
          in
          expr'_Constructor_CF ~span ~break_type:inner.typ
            ~continue_type:acc.typ `Break inner
      | `Break ->
          let tuple = expr_tuple ~span [ e; acc ] in
          let inner =
            match return_type with
            | Some ret_typ ->
                expr'_Constructor_CF ~span ~break_type:ret_typ
                  ~continue_type:tuple.typ `Continue tuple
            | None -> tuple
          in
          expr'_Constructor_CF ~span ~break_type:inner.typ
            ~continue_type:acc.typ `Break inner
      | `Continue ->
          let break_type =
            let tuple_type = NoSpan.ty_tuple [ break_type; acc.typ ] in
            match return_type with
            | Some ret_typ ->
                NoSpan.ty_cf ~break_type:ret_typ ~continue_type:tuple_type
            | None -> tuple_type
          in
          expr'_Constructor_CF ~span ~break_type ~continue_type:acc.typ
            `Continue acc
  end

  include Explicit

  module Make0 (Span : Gen.SPAN) = struct
    open! Span
    include Gen.Make (Span)
    include NoSpan

    let pat_PBinding = Explicit.pat_PBinding ~span
    let expr_unit = expr_unit ~span
    let expr_tuple = expr_tuple ~span
    let pat_Constructor_CF = pat_Constructor_CF ~span
    let expr'_Constructor_CF = expr'_Constructor_CF ~span
    let expr_Constructor_CF = expr_Constructor_CF ~span
    let arm ?(guard = None) = arm ~span ?guard
  end

  module type S = module type of Make0 (struct
    (* This [failwith] is OK: this module is never actually used for computation. It is useful only for typing. *)
    let span = failwith "type only module: this will never be computed"
  end)

  module Make (Span : sig
    val span : span
  end) : S =
    Make0 (Span)

  let make : span -> (module S) =
   fun span : (module S) ->
    (module Make0 (struct
      let span = span
    end))
end
