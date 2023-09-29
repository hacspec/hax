open Hax_engine
open Utils
open Base
open Semantics_ast

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
      let backend = Diagnostics.Backend.Semantics
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
             and type for_index_loop = Features.Off.for_index_loop
             and type state_passing_loop = Features.Off.state_passing_loop) =
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
module SemanticsNamePolicy = Concrete_ident.DefaultNamePolicy
module U = Ast_utils.MakeWithNamePolicy (InputLanguage) (SemanticsNamePolicy)
open AST
module C = Semantics

module Context = struct
  type t = { current_namespace : string * string list }
end

let primitive_to_string (id : primitive_ident) : string =
  match id with
  | Deref -> "(TODO: Deref)" (* failwith "Deref" *)
  | Cast -> "cast" (* failwith "Cast" *)
  | LogicalOp op -> ( match op with And -> "andb" | Or -> "orb")

module Make (Ctx : sig
  val ctx : Context.t
end) =
struct
  open Ctx

  let pconcrete_ident (id : concrete_ident) : string =
    let id = U.Concrete_ident_view.to_view id in
    let crate, path = ctx.current_namespace in
    if String.(crate = id.crate) && [%eq: string list] id.path path then
      id.definition
    else
      (* id.crate ^ "_" ^ *)
      (* List.fold_left ~init:"" ~f:(fun x y -> x ^ "_" ^ y) *)
      id.definition

  let pglobal_ident (id : global_ident) : string =
    match id with
    | `Projector (`Concrete cid) | `Concrete cid -> pconcrete_ident cid
    | `Primitive p_id -> primitive_to_string p_id
    | `TupleType i -> "TODO (global ident) tuple type"
    | `TupleCons i -> "TODO (global ident) tuple cons"
    | `Projector (`TupleField (i, j)) | `TupleField (i, j) ->
        "TODO (global ident) tuple field"
    | _ -> .

  (* let rec pliteral span (e : literal) = *)
  (*   match e with *)
  (*   | String s -> C.AST.Unimplemented "string" *)
  (*   | Char c -> C.AST.Unimplemented "char" *)
  (*   | Int { value; kind } -> C.AST.Int *)
  (*   | Float _ -> C.AST.Unimplemented "float" *)
  (*   | Bool b -> C.AST.Const_bool b *)

  let rec pty (t : ty) : C.AST.ty =
    match t with
    | TBool -> C.AST.Bool
    | TChar -> C.AST.Unimplemented "Char"
    | TInt k -> C.AST.Int
    | TStr -> C.AST.Unimplemented "Str"
    | TApp { ident = `TupleType 0 as ident; args = [] } -> C.AST.Unit
    | TApp { ident = `TupleType 1; args = [ GType ty ] } -> pty ty
    | TApp { ident = `TupleType n; args } when n >= 2 ->
        C.AST.Product [] (* TODO: (args) *)
    | TApp { ident; args } ->
        C.AST.Name (* AppTy *) (pglobal_ident ident ^ "_t")
        (* TODO: args_ty args *)
    | TArrow (inputs, output) ->
        List.fold_right ~init:(pty output)
          ~f:(fun x y -> C.AST.Arrow (x, y))
          (List.map ~f:pty inputs)
    | TFloat _ -> C.AST.Unimplemented "float"
    | TArray { typ; length } ->
        C.AST.Product [ C.AST.List (pty typ); C.AST.Name "of size (*TODO*)" ]
    | TSlice { ty; _ } -> C.AST.List (pty ty)
    | TParam i -> C.AST.Name i.name
    | TProjectedAssociatedType s -> C.AST.Wild
    | _ -> .

  let rec ppat (p : pat) : C.AST.pat =
    match p.p with
    | PWild -> C.AST.WildPat
    | PAscription { typ; pat } -> C.AST.TypedPat (ppat pat, pty typ)
    | PBinding
        {
          mut = Immutable;
          mode = _;
          subpat = None;
          var;
          typ = _ (* we skip type annot here *);
        } ->
        C.AST.Ident var.name
    | PArray { args } -> C.AST.Unimplemented "Parray?"
    | PConstruct { name = `TupleCons 0; args = [] } -> C.AST.UnitPat
    | PConstruct { name = `TupleCons 1; args = [ { pat } ] } ->
        C.AST.Unimplemented "tuple 1"
    | PConstruct { name = `TupleCons n; args } ->
        C.AST.ProductPat (List.map ~f:(fun { pat } -> ppat pat) args)
    | PConstruct { name; args; is_record = true } ->
        C.AST.RecordPat (pglobal_ident name, pfield_pats args)
    | PConstruct { name; args; is_record = false } ->
        C.AST.EnumPat
          (pglobal_ident name, List.map ~f:(fun p -> ppat p.pat) args)
    | PConstant { lit } -> C.AST.Unimplemented "lit"
    (* | PDeref { subpat } -> C.AST.Unimplemented "deref" *)
    | _ -> .

  and pfield_pats (args : field_pat list) : (string * C.AST.pat) list =
    match args with
    | { field; pat } :: xs -> (pglobal_ident field, ppat pat) :: pfield_pats xs
    | _ -> []

  let rec pexpr (e : expr) : C.AST.term =
    let span = e.span in
    match e.e with
    | Literal l -> (
        match l with
        | String s -> C.AST.Unimplemented "string"
        | Char c -> C.AST.Unimplemented "char"
        | Int { value; kind } -> C.AST.IntTerm (Int.of_string value)
        | Float _ -> C.AST.Unimplemented "float"
        | Bool b -> C.AST.BoolTerm b)
    | LocalVar local_ident -> C.AST.Ident local_ident.name
    | GlobalVar (`TupleCons 0)
    | Construct { constructor = `TupleCons 0; fields = [] } ->
        C.AST.Unimplemented "Unit"
    | GlobalVar global_ident -> C.AST.Ident (pglobal_ident global_ident)
    | App
        {
          f = { e = GlobalVar (`Projector (`TupleField (n, len))) };
          args = [ arg ];
        } ->
        C.AST.Unimplemented "App Projector"
    | App { f; args } ->
        List.fold_left ~init:(pexpr f)
          ~f:(fun y a -> C.AST.App (y, a))
          (List.map ~f:pexpr args)
    | If { cond; then_; else_ } -> C.AST.Unimplemented "If"
    | Array l -> C.AST.Array (List.map ~f:pexpr l)
    | Let { lhs; rhs; body; monadic = Some monad } ->
        C.AST.Let
          {
            pattern = ppat lhs;
            value = pexpr rhs;
            body = pexpr body;
            value_typ = pty lhs.typ;
          }
    | Let { lhs; rhs; body; monadic = None } ->
        C.AST.Let
          {
            pattern = ppat lhs;
            value = pexpr rhs;
            body = pexpr body;
            value_typ = pty lhs.typ;
          }
    | EffectAction _ -> C.AST.Unimplemented "EffectAction"
    | Match { scrutinee; arms } -> C.AST.Unimplemented "Match"
    | Ascription { e; typ } -> C.AST.Unimplemented "Ascription"
    | Construct { constructor = `TupleCons 1; fields = [ (_, e) ]; base } ->
        pexpr e
    | Construct { constructor = `TupleCons n; fields; base } ->
        C.AST.Unimplemented "Construct n"
    | Construct { is_record = true; constructor; fields; base } ->
        List.fold_left
          ~init:(C.AST.Ident (pglobal_ident constructor))
          ~f:(fun y (f, e) -> C.AST.Set (y, (pglobal_ident f, pexpr e)))
          fields
    | Construct { is_record = false; constructor; fields = [ (f, e) ]; base } ->
        C.AST.App (C.AST.Ident (pglobal_ident constructor), pexpr e)
    | Construct { constructor; fields; base } ->
        C.AST.Unimplemented "Construct default"
    | Closure { params; body } ->
        C.AST.Lambda (List.map ~f:ppat params, pexpr body)
    | MacroInvokation { macro; args; witness } ->
        C.AST.Unimplemented "MacroInvokation"
    | _ -> .

  let rec pitem (e : item) : C.AST.decl list =
    try pitem_unwrapped e
    with Diagnostics.SpanFreeError.Exn _ ->
      [ C.AST.Unimplemented "item error backend" ]

  and pgeneric_param span : generic_param -> _ = function
    | { ident; kind = GPType _; _ } -> ident.name
    | _ -> Error.unimplemented ~details:"Coq: TODO: generic_params" span

  and pitem_unwrapped (e : item) : C.AST.decl list =
    let span = e.span in
    match e.v with
    | Fn { name; generics; body; params } ->
        [
          C.AST.Definition
            ( pconcrete_ident name,
              C.AST.Lambda
                ( List.map
                    ~f:(fun { pat; typ; typ_span; attrs } ->
                      C.AST.TypedPat (ppat pat, pty typ))
                    params,
                  pexpr body ) );
        ]
    | TyAlias { name; generics; ty } -> [ C.AST.Unimplemented "TyAlias" ]
    | Type { name; generics; variants = [ v ]; is_struct = true } ->
        [ C.AST.Unimplemented " Type" ]
    (* enum *)
    | Type { name; generics; variants } -> [ C.AST.Unimplemented "Type" ]
    | IMacroInvokation { macro; argument; span } ->
        [ C.AST.Unimplemented "IMacroInvokation" ]
    | Use { path; is_external; rename } -> [ C.AST.Unimplemented "Use" ]
    | HaxError s -> [ C.AST.Unimplemented "HaxError" ]
    | NotImplementedYet -> [ C.AST.Unimplemented "NotImplementedYet" ]
    | Trait { name; generics; items } -> [ C.AST.Unimplemented "Trait" ]
    | Impl { generics; self_ty; of_trait = name, gen_vals; items } ->
        [
          C.AST.Section
            ( pglobal_ident name,
              List.map
                ~f:(fun x ->
                  match x.ii_v with
                  | IIFn { body; params } ->
                      C.AST.Definition
                        ( x.ii_name,
                          C.AST.Lambda
                            ( List.map
                                ~f:(fun { pat; typ; typ_span } -> ppat pat)
                                params,
                              pexpr body ) )
                  | _ -> C.AST.Unimplemented "impl not function")
                items );
        ]
end

module type S = sig
  val pitem : item -> C.AST.decl list
end

let make ctx =
  (module Make (struct
    let ctx = ctx
  end) : S)

let string_of_item (item : item) : string =
  let (module Print) =
    make { current_namespace = U.Concrete_ident_view.to_namespace item.ident }
  in
  List.map ~f:C.decl_to_string @@ Print.pitem item |> String.concat ~sep:"\n"

let string_of_items =
  List.map ~f:string_of_item >> List.map ~f:String.strip
  >> List.filter ~f:(String.is_empty >> not)
  >> String.concat ~sep:"\n\n"

let hardcoded_headers = "(* Automatically Generated Functional Semantics *)"

let translate (bo : BackendOptions.t) (items : AST.item list) : Types.file list
    =
  U.group_items_by_namespace items
  |> Map.to_alist
  |> List.map ~f:(fun (ns, items) ->
         let mod_name =
           String.concat ~sep:"."
             (List.map
                ~f:(map_first_letter String.uppercase)
                (fst ns :: snd ns))
         in

         Types.
           {
             path = mod_name ^ ".semantics";
             contents = hardcoded_headers ^ "\n" ^ string_of_items items ^ "\n";
           })

open Phase_utils

module TransformToInputLanguage =
  [%functor_application
  Phases.Reject.RawOrMutPointer(Features.Rust)
  |> Phases.And_mut_defsite
  |> Phases.Reconstruct_for_loops
  |> Phases.Direct_and_mut
  |> Phases.Reject.Arbitrary_lhs
  |> Phases.Drop_blocks
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
  |> SubtypeToInputLanguage
  |> Identity
  ]
  [@ocamlformat "disable"]

let apply_phases (bo : BackendOptions.t) (items : Ast.Rust.item list) :
    AST.item list =
  TransformToInputLanguage.ditems items
