open! Prelude
open! Ast
open PPrint

module SecretTypes = struct
  type 't no_override = 't
  type 'location no_direct_call = unit
end

let ( !: ) (type a) (f : a SecretTypes.no_override) : a = f

include Generic_printer_base_sig.Types

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  open Generic_printer_base_sig.Make (F) (SecretTypes)

  class virtual base : print_base_type =
    object (print)
      val mutable current_span = Span.default
      val mutable span_data : Annotation.t list = []
      val mutable current_namespace : (string * string list) option = None
      method get_span_data () = span_data

      method with_span ~(span : span) (f : unit -> document) : document =
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

      method expr_at = print#par_state >> print#expr
      method ty_at = print#par_state >> print#ty
      method pat_at = print#par_state >> print#pat

      method expr ctx (e : expr) =
        let span = e.span in
        print#with_span ~span (fun _ ->
            try print#__expr ctx e
            with Diagnostics.SpanFreeError.Exn (Data (_context, _kind)) ->
              failwith "todo")

      method ty ctx full =
        match full with
        | TApp { ident = `Concrete ident; args } ->
            print#ty_TApp_application ~full ident args |> group
        | TApp
            {
              ident = `Primitive _ | `TupleCons _ | `TupleField _ | `Projector _;
              _;
            } ->
            print#assertion_failure "TApp not concrete"
        | TApp { ident = `TupleType size; args } ->
            let args =
              List.filter_map ~f:(function GType t -> Some t | _ -> None) args
            in
            if [%equal: int] (List.length args) size |> not then
              print#assertion_failure "malformed [ty.TApp] tuple";
            print#ty_TApp_tuple ~full args
        | TApp _ -> .
        | _ -> print#ty_ () ctx full

      method pat ctx (full : pat) =
        print#with_span ~span:full.span (fun _ -> print#pat_ () ctx full)

      method item i =
        print#set_current_namespace
          (print#namespace_of_concrete_ident i.ident |> Option.some);
        print#with_span ~span:i.span (fun _ ->
            try print#item_ () i
            with Diagnostics.SpanFreeError.Exn (Data (context, kind)) ->
              let error = Diagnostics.pretty_print_context_kind context kind in
              (* let cast_item : item -> Ast.Full.item = Stdlib.Obj.magic in *)
              (* let ast = cast_item i |> Print_rust.pitem_str in *)
              let msg =
                error ^ "\nLast available AST for this item:\n\n" ^ "ast"
              in
              (* TODO: if the printer is extremely broken, this results in a stack overflow *)
              make_hax_error_item i.span i.ident msg |> print#item)

      method private __expr ctx full =
        match full.e with
        | App { f = { e = GlobalVar i; _ } as f; args; generic_args; _ } -> (
            let expect_one_arg where =
              match args with
              | [ arg ] -> arg
              | _ -> print#assertion_failure @@ "Expected one arg at " ^ where
            in
            match i with
            | `Concrete _ | `Primitive _ -> (
                match (args, i) with
                | [], `Concrete i ->
                    print#expr_App_constant ~full i generic_args
                | [], _ -> print#assertion_failure "Primitive app of arity 0"
                | _ -> print#expr_App_application ~full f args generic_args)
            | `TupleType _ | `TupleCons _ | `TupleField _ ->
                print#assertion_failure "App: unexpected tuple"
            | `Projector (`TupleField (nth, size)) ->
                let arg = expect_one_arg "projector tuple field" in
                print#expr_App_tuple_projection ~full ~size ~nth arg
            | `Projector (`Concrete i) ->
                let arg = expect_one_arg "projector concrete" in
                print#expr_App_field_projection ~full i arg)
        | App { f; args; generic_args; _ } ->
            print#expr_App_application ~full f args generic_args
        | Construct { constructor; fields; base; is_record; is_struct } -> (
            match constructor with
            | `Concrete constructor ->
                print#expr_Construct_inductive ~full ~is_record ~is_struct
                  ~constructor ~base fields
            | `TupleCons _ ->
                List.map ~f:snd fields |> print#expr_Construct_tuple ~full
            | `Primitive _ | `TupleType _ | `TupleField _ | `Projector _ ->
                print#assertion_failure "Construct unexpected constructors")
        | App _ | Construct _ -> .
        | _ -> print#expr_ () ctx full

      method arm (full : arm) =
        print#with_span ~span:full.span (fun _ -> print#arm_ () full)

      method generic_param (full : generic_param) =
        print#with_span ~span:full.span (fun _ -> print#generic_param_ () full)

      method param_ty (full : param) =
        match full.typ_span with
        | Some span -> print#with_span ~span (fun _ -> print#param_ty_ () full)
        | None -> print#param_ty_ () full

      method impl_item (full : impl_item) =
        print#with_span ~span:full.ii_span (fun _ -> print#impl_item_ () full)

      method trait_item (full : trait_item) =
        print#with_span ~span:full.ti_span (fun _ -> print#trait_item_ () full)

      method attr (full : attr) =
        print#with_span ~span:full.span (fun _ -> print#attr_ () full)

      method concrete_ident id =
        let current_ns = print#get_current_namespace () in
        let id_ns = print#namespace_of_concrete_ident id in
        print#concrete_ident_ ()
          ~under_current_ns:
            ([%equal: (string * string list) option] current_ns (Some id_ns))
          id

      method items = separate_map (twice hardline) print#item
      method attrs = separate_map hardline print#attr

      method assertion_failure : 'any. string -> 'any =
        fun details ->
          let span = Span.to_thir current_span in
          let kind = Types.AssertionFailure { details } in
          let ctx = Diagnostics.Context.GenericPrinter print#printer_name in
          Diagnostics.SpanFreeError.raise ~span ctx kind

      method set_current_namespace ns = current_namespace <- ns
      method get_current_namespace () = current_namespace
      method unreachable : 'any. unit -> 'any = failwith "Unreachable!"
    end
end
