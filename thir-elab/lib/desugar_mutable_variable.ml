open Base
open Utils

module MakePatCollector (F: Features.T): sig
  val local_idents_of_pat: Ast.Make(F).pat -> Ast.local_ident list
end = struct
  open Ast
  open Ast.Make(F)
  module S = Set.M (LocalIdent)

  class ['s] set_monoid =
    object
      inherit ['s] VisitorsRuntime.monoid
      method private zero = Set.empty (module LocalIdent)
      method private plus = Set.union
    end

  let local_idents_of_pat (p : pat) : local_ident list =
    (object
       inherit [_] pat_reduce as super
       inherit [_] set_monoid as m

       method visit_reference _ _ = m#zero
       method visit_slice _ _ = m#zero
       method visit_as_pattern _ _ = m#zero
       method visit_raw_pointer _ _ = m#zero
       method visit_lifetime _ _ = m#zero
       method visit_literal _ _ = m#zero
       method visit_span _ _ = m#zero
       method visit_spanned f x s = f x s.v
       method visit_mutable_borrow _ _ = m#zero
       
       method! visit_PBinding _ _ _ var _ subpat =
         m#plus
           (Set.singleton (module LocalIdent) var)
           (Option.value_map subpat ~default:m#zero
              ~f:(fst >> super#visit_pat ()))
     end)
      #visit_pat
      () p
    |> Set.to_list
end

module UniqueList(T: sig
  type t [@@deriving eq, show, yojson]
  type comparator_witness
end): sig
  type t [@@deriving eq, show, yojson]
  val without: T.t -> t -> t
  val cons: T.t -> t -> t
  val to_list: t -> T.t list
  val from_set: (T.t, T.comparator_witness) Set.t -> t
  val empty: t
end = struct
  type t = T.t list [@@deriving eq, show, yojson]
  let without x = List.filter ~f:([%eq: T.t] x >> not)
  let cons hd tl = hd::tl
  let to_list = Fn.id
  let from_set s = Set.to_list s
  let empty = []
end

module TypedLocalIdent(Ty: sig type ty [@@deriving show, yojson] end) = struct
  module T = struct
    type t = Ast.LocalIdent.t * Ty.ty [@@deriving show, yojson]
    let sexp_of_t: t -> _ = fst >> Ast.LocalIdent.sexp_of_t
    let compare (a: t) (b: t) = [%compare: Ast.LocalIdent.t] (fst a) (fst b)
    let equal (a: t) (b: t) = [%eq: Ast.LocalIdent.t] (fst a) (fst b)
  end

  include Base.Comparator.Make (T)
  include T
end

module MakeExprCollector (F: Features.T) = struct
  open Ast
  module F_Ast = Ast.Make(F)
  open F_Ast
  module TypedLocalIdent = TypedLocalIdent(F_Ast)
  module S = Set.M (TypedLocalIdent)

  class ['s] set_monoid =
    object
      inherit ['s] VisitorsRuntime.monoid
      method private zero = Set.empty (module TypedLocalIdent)
      method private plus = Set.union
    end

  let mut_fvars_expr = object
      inherit [_] expr_reduce as super
      inherit [_] set_monoid as m

      method visit_loop
          (_: unit) (_: F.loop             ) = m#zero
      method visit_continue
          (_: unit) (_: F.continue         ) = m#zero
      method visit_mutable_variable
          (_: unit) (_: F.mutable_variable ) = m#zero
      method visit_mutable_reference
          (_: unit) (_: F.mutable_reference) = m#zero
      method visit_mutable_pointer
          (_: unit) (_: F.mutable_pointer  ) = m#zero
      method visit_mutable_borrow
          (_: unit) (_: F.mutable_borrow   ) = m#zero
      method visit_reference
          (_: unit) (_: F.reference        ) = m#zero
      method visit_slice
          (_: unit) (_: F.slice            ) = m#zero
      method visit_raw_pointer
          (_: unit) (_: F.raw_pointer      ) = m#zero
      method visit_early_exit
          (_: unit) (_: F.early_exit       ) = m#zero
      method visit_macro
          (_: unit) (_: F.macro            ) = m#zero
      method visit_as_pattern
          (_: unit) (_: F.as_pattern       ) = m#zero
      method visit_lifetime
          (_: unit) (_: F.lifetime         ) = m#zero
      method visit_monadic
          (_: unit) (_: F.monadic          ) = m#zero
      
      method visit_t _ _ = m#zero
      method visit_mutability f () _ = m#zero
      
      method visit_literal _ _ = m#zero
      method visit_span _ _ = m#zero
      (* method visit_spanned f x s = f x s.v *)

      method visit_Assign m lhs e wit =
        match lhs with
        | LhsLocalVar v -> Set.singleton (module TypedLocalIdent) (v, e.typ)
        | _ -> failwith "???"
        
      method visit_Match m scrut arms =
        List.fold_left
          ~init:(super#visit_expr m scrut)
          ~f:Set.union
        @@ List.map ~f:(fun arm -> super#visit_arm m arm) arms
      
      method visit_Let m pat expr body =
        Set.union
          (super#visit_expr m expr)
        @@ Set.diff
             (super#visit_expr m body)
             (super#visit_pat m pat)

      method visit_arm' m {pat; body} =
        Set.diff
          (super#visit_expr m body)
          (super#visit_pat m pat)
    end
  
  (* let mut_fvars_of_expr' (e : expr) : S.t = *)
  (*   () *)
  (*     #visit_expr *)
  (*     () e *)

  (* let mut_fvars_of_expr: expr -> local_ident list = *)
  (*   mut_fvars_of_expr' >> Set.to_list *)
  
  (* let mut_fvars_of_exprs: expr list -> local_ident list = *)
  (*   List.map ~f:mut_fvars_of_expr' *)
  (*   >> Set.union_list (module LocalIdent) *)
  (*   >> Set.to_list *)
end

module Make (F: Features.T
             with type mutable_reference = Features.off
              and type mutable_pointer   = Features.off
              and type     raw_pointer   = Features.off
              and type continue          = Features.off
              and type monadic           = Features.off
         )
= struct
  open Ast
  module F' = struct
    include F
    type mutable_variable = Features.off [@@deriving show, yojson, eq]
  end
  module A = Ast.Make(F)
  module B = Ast.Make(F')

  module Collect = struct
    include MakePatCollector(F')
    include MakeExprCollector(F)
  end

  let rec dty (t: A.ty): B.ty =
    match t with
    | TBool -> TBool
    | TChar -> TChar
    | TInt k -> TInt k
    | TFloat -> TFloat
    | TStr -> TStr
    | TApp { ident; args } -> TApp {ident; args = List.map ~f:dgeneric_value args}
    | TArray { typ; length } -> TArray { typ = dty typ; length }
    | TSlice { witness; ty } -> TSlice { witness; ty = dty ty }
    | TRef { witness; typ; mut; region } -> TRef {
        witness; typ = dty typ; mut; region
      }
    | TFalse -> TFalse
    | TParam local_ident -> TParam local_ident
    | TArrow (inputs, output) -> TArrow (List.map ~f:dty inputs, dty output)
    | TProjectedAssociatedType string -> TProjectedAssociatedType string
  
    | TRawPointer {witness} -> .
  and dgeneric_value (g: A.generic_value): B.generic_value =
    match g with
    | GLifetime {lt; witness} -> GLifetime {lt; witness}
    | GType t -> GType (dty t)
    | GConst c -> GConst c

  let dborrow_kind (k: A.borrow_kind): B.borrow_kind =
    match k with
    | Shared -> Shared
    | Unique -> Unique
    | Mut witness -> Mut witness

  let rec dpat (p: A.pat): B.pat =
    {p = dpat' p.p; span = p.span; typ = dty p.typ}
  and dpat' (p: A.pat'): B.pat' =
    match p with
    | PWild -> PWild
    | PAscription { typ; typ_span; pat } -> PAscription {
        typ = dty typ;
        typ_span;
        pat = dpat pat
      }
    | PConstruct { name; args; record } -> PConstruct {
        name; record;
        args = List.map ~f:dfield_pat args;
      }
    | PArray { args } -> PArray { args = List.map ~f:dpat args }
    | PConstant { lit } -> PConstant { lit }
    | PBinding {
        mut;
        mode;
        var : LocalIdent.t;
        typ;
        subpat
        } -> PBinding {
            mut = Immutable;
            mode = ByValue;
            var;
            typ = dty typ;
            subpat = Option.map ~f:(dpat *** Fn.id) subpat
          }
    | PDeref { subpat } -> (dpat subpat).p
    | _ -> .
  and dfield_pat (p: A.field_pat): B.field_pat =
    {field = p.field; pat = dpat p.pat}
  and dbinding_mode (m: A.binding_mode): B.binding_mode =
    match m with
    | ByValue -> ByValue
    | ByRef (kind, witness) -> ByRef (dborrow_kind kind, witness)


  let unit_typ : B.ty = TApp { ident = `TupleType 0; args = [] }
  let unit_expr : B.expr =
    {
      typ = unit_typ;
      span = Dummy;
      e =
        B.App
          {
            f =
              {
                e = B.GlobalVar (`TupleCons 0);
                span = Dummy;
                typ = B.TArrow ([], unit_typ)
              };
            args = [];
          };
    }

  let let_of_binding ((var, rhs): local_ident * B.expr) (body: B.expr): B.expr
    = { body with
        e = B.Let { lhs = { typ = rhs.typ
                          ; p = B.PBinding { mut = Immutable
                                          ; mode = ByValue
                                          ; var
                                          ; typ = rhs.typ
                                          ; subpat = None
                                  }
                          ; span = rhs.span }
                    ; rhs = rhs
                    ; body }
      }

  let lets_of_bindings (bindings: (local_ident * B.expr) list) (body: B.expr): B.expr
    = List.fold_right ~init:body ~f:(let_of_binding) bindings
      
  (* let expr_of_local_ident (v: local_ident): B.expr *)
  (*   = { v = B.LocalVar v; typ =  } *)

  let make_tuple_typ (tuple: B.ty list): B.ty =
    B.TApp
      { ident = `TupleType (List.length tuple);
        args = List.map ~f:(fun typ -> B.GType typ) tuple
      }

  let make_var_pat (var: local_ident) (typ: B.ty) (span: span): B.pat =
    {
      p = B.PBinding {
        mut = Immutable;
        mode = B.ByValue;
        var;
        typ;
        subpat = None;
      };
      span; typ
    }

  let make_tuple_field_pat (len: int) (nth: int) (pat: B.pat): B.field_pat
    = { field = `TupleField (nth+1, len); pat }
      
  let make_tuple_pat (tuple: B.field_pat list): B.pat =
    let len = List.length tuple in
    let span = (* TODO: union of r.bindings's spans *) Dummy in    
    { p = B.PConstruct {
            name = `TupleCons len;
            args = tuple;(*List.mapi ~f:(make_tuple_field_pat len) tuple;*)
            record = false;
          }
        ; typ = make_tuple_typ @@ List.map ~f:(fun {pat = {typ}} -> typ) tuple
        ; span
      }

  let make_tuple_expr ~(span: span) (tuple: B.expr list): B.expr =
    let len = List.length tuple in
    {
      e = B.Construct
          { constructor = `TupleCons len;
            constructs_record = false;
            fields = List.mapi ~f:(fun i x -> `TupleField (i, len), x)
              @@ tuple;
            base = None;
          };
      typ = make_tuple_typ @@ List.map ~f:(fun {typ} -> typ) tuple;
      span;
    }

  let rec collect_let_bindings (e: A.expr): (A.pat * A.expr) list * A.expr
    = match e.e with
    | Let {lhs; rhs; body} ->
       let bindings, body = collect_let_bindings body in
       (lhs, rhs)::bindings, body
    | _ -> [], e

  module Fresh = struct
    let state = ref 0
    let int (): int =
      let state' = !state in
      state := state' + 1;
      state'

    let local_ident (name: string): local_ident =
      (* TODO, this gives no guarrantee of freshness whatsoever *)
      let id = int () in
      {name = name ^ string_of_int id; id}
  end
             
  module BTypedLocalIdent = TypedLocalIdent(B)
  module MutatedVarSet = struct
    include Set.M(BTypedLocalIdent)
    module L = struct
      type t = BTypedLocalIdent.t list [@@deriving show, yojson, eq]
    end
    let show = Set.to_list >> [%show: L.t]
    let pp f = Set.to_list >> L.pp f
    let equal = Set.equal
    let t_of_yojson = L.t_of_yojson >> Set.of_list (module BTypedLocalIdent)
    let yojson_of_t = Set.to_list >> L.yojson_of_t  
  end


  module BTyLocIdentUniqueList = UniqueList(BTypedLocalIdent)
  module ShadowingTuple = struct
    (* We consider values of type [α × β₁ × … × βₙ]
       [β₁], ... and [βₙ] are shadowed variables
     *)
    type t =
      { expr: B.expr
      ; result_type: B.ty option
      ; shadowings: BTyLocIdentUniqueList.t
      } [@@deriving show, yojson, eq]
     
    let pat (val_pat: B.pat option) (t: t): B.pat =
      let value = Option.map ~f:(fun _ -> Option.value_exn val_pat) t.result_type in
      let chunks = value::List.map ~f:(
                              fun (var, ty) -> Some (make_var_pat var ty Dummy)
                            ) (BTyLocIdentUniqueList.to_list t.shadowings)
                   |> List.filter_map ~f:Fn.id in
      chunks
      |> List.mapi
           ~f:(fun i pat -> B.{
                   field = `TupleField (i, List.length chunks);
                   pat
           })
      |> make_tuple_pat
    
    let pat' (name: string) (t: t): (local_ident * B.ty) option * B.pat =
      let val_id_ty = Option.map ~f:((fun _ -> Fresh.local_ident name) &&& Fn.id) t.result_type in
      let val_pat = Option.map ~f:(fun (v, t) -> make_var_pat v t Dummy) val_id_ty in
      val_id_ty, pat val_pat t
  
    let collect_mut_idents {shadowings}: MutatedVarSet.t
      = Set.of_list (module BTypedLocalIdent) @@ BTyLocIdentUniqueList.to_list shadowings
    
    let make_let lhs rhs body = B.{ body with e = B.Let {lhs; rhs; body } }
          
    let with_names (val_pat: B.pat) (r: t): B.expr -> B.expr =
      make_let (pat (Some val_pat) r) r.expr
      
    let with_names' (name: string) (r: t): (local_ident * B.ty) option * (B.expr -> B.expr) =
      let val_pat, pat = pat' name r in
      val_pat, make_let pat r.expr
  end

  module Binding = struct
    type t = {
        pat: B.pat;
        e: B.expr;
        mutated_vars: MutatedVarSet.t
        (* mutated_vars: (local_ident * B.ty) list *)
      } [@@deriving show, yojson, eq]

    let collect_mut_idents {mutated_vars}: MutatedVarSet.t = mutated_vars
            
    let with_name ({pat = lhs; e = rhs}: t) ~(body: B.expr): B.expr =
      { body with e = B.Let { lhs; rhs; body } }
      
    let with_names (l: t list) ~(body: B.expr): B.expr =
      List.fold_right l
        ~f:(fun b body -> with_name b ~body)
        ~init:body
  end

  module Result = struct
    (* Our results are of the shape
       [ let … = … in
       …
       let … = … in
       ret[, v₁, …, vₙ]
       ] *)
    type t = {
        bindings: Binding.t list;
        value: ShadowingTuple.t;
      } [@@deriving show, yojson, eq]

    let collect_mut_idents {bindings; value}: MutatedVarSet.t =
      List.fold_left
        ~f:Set.union
        ~init:(ShadowingTuple.collect_mut_idents value)
      @@ List.map ~f:Binding.collect_mut_idents bindings
      
      (* List.concat_map ~f:Binding.collect_mut_idents bindings *)
      (* @ ShadowingTuple.collect_mut_idents value *)

    let as_shadowing_tuple
          (r: t)
          (shadowings: BTyLocIdentUniqueList.t)
      : ShadowingTuple.t =
      let body =
        let shadowings = BTyLocIdentUniqueList.to_list shadowings in      
        match shadowings with
        | [] -> r.value.expr
        | _ ->
          let var, mk = ShadowingTuple.with_names' "value_as_sha_tup" r.value in
          mk
          @@ make_tuple_expr ~span:r.value.expr.span
          @@ List.map ~f:(fun (v, typ) -> B.{
              span = Dummy;
              typ;
              e = B.LocalVar v })
            (var::List.map ~f:Option.some shadowings |> List.filter_map ~f:Fn.id)
      in      
      let expr = Binding.with_names r.bindings body in
      (* print_endline ("as_shadowing_tuple: " ^ [%show: B.expr] expr); *)
      {
        expr; shadowings;
        result_type = r.value.result_type;
      }
  
    let from_bindings
        (bindings: (B.pat * t) list)
        (body: t)
        : t
      = let bindings: Binding.t list =
          List.concat_map ~f:(
            fun (pat, {bindings; value}) ->
              if [%eq: B.expr] value.expr unit_expr
              then bindings
              else               
                bindings @
                [Binding.{
                    pat = ShadowingTuple.pat (Some pat) value;
                    mutated_vars = ShadowingTuple.collect_mut_idents value;
                    e = value.expr
                }]
            ) bindings
        in
        {
          bindings = bindings @ body.bindings;
          value = body.value
        }
  
    let from_match
        (desugar: A.expr -> t)
        (arms: A.arm list)
      = let vars =
        List.map ~f:(Collect.mut_fvars_expr#visit_arm ()) arms
        |> Set.union_list (module Collect.TypedLocalIdent)
        |> Set.map (module BTypedLocalIdent) ~f:(map_snd dty)
        |> BTyLocIdentUniqueList.from_set
      in
        let arms =
        List.map ~f:(fun A.{arm = {pat; body}; span} ->
            B.{
                span;
                arm = {
                    pat = dpat pat;
                  body = (as_shadowing_tuple (desugar body) vars).expr;
                  }
              }) arms
      in 0
  
    let seq (l: t list) (f: B.expr list -> B.expr): t =
      if List.map ~f:collect_mut_idents l |> Set.union_list (module BTypedLocalIdent) |> Set.is_empty
      then
        let expr = f (List.map ~f:(fun {value = {expr}} -> expr) l) in      
        {
          bindings = [];
          value = {
            expr;
            result_type = Some expr.typ;
            shadowings = BTyLocIdentUniqueList.empty
          }
        }
      else         
        let l: (Binding.t list * B.expr) list = List.map
            ~f:(fun {bindings; value} ->
              let var, pat = ShadowingTuple.pat' "arg" value in
                let var = Option.map ~f:(fun (var, typ) -> B.{
                    e = B.LocalVar var;
                      typ;
                      span = Dummy;                
                    }) var |> Option.value ~default:unit_expr in
              (bindings @ [
                    Binding.{
                        pat;
                        e = value.expr;
                        mutated_vars = ShadowingTuple.collect_mut_idents value
                      }
                ]), var
            ) l in
        let bindings = List.concat_map ~f:fst l in
        let expr = f @@ List.map ~f:snd l in
        {
          bindings;
          value = {
            expr;
            result_type = Some expr.typ;
            shadowings = BTyLocIdentUniqueList.empty;
          }
        }
  
    let pure (e0: A.expr) (e: B.expr'): t =
      let typ = dty e0.typ in
      {
        value = ShadowingTuple.{
            expr = {e; span = e0.span; typ};
            result_type = Some typ;
            shadowings = BTyLocIdentUniqueList.empty;
          };
        bindings = []
      }

  end
 
  (* let cons_no_dup (l: (local_ident * 'a) list) (var: local_ident) (x: 'a): (local_ident * 'a) list = *)
  (*   if List.mem ~equal:equal_local_ident (List.map ~f:fst l) var *)
  (*   then l *)
  (*   else (var, x)::l *)

  (* let ( @! ) (l: (local_ident * 'a) list) (l': (local_ident * 'a) list) *)
  (*   = List.fold ~init:l ~f:(fun acc (var, x) -> cons_no_dup acc var x) l' *)

  let rec dexpr (e: A.expr): Result.t =
    match e.e with
    | Literal lit -> Result.pure e @@ B.Literal lit
    | LocalVar v -> Result.pure e @@ B.LocalVar v
    | GlobalVar v -> Result.pure e @@ B.GlobalVar v
    | Assign { lhs = LhsLocalVar var; e = e'; witness } ->
        let e'_r = dexpr e' in
        let var_typ = dty e'.typ in
        let var_pat = make_var_pat var var_typ e.span in
        let var_binding: Binding.t = {
          pat = ShadowingTuple.pat (Some var_pat) e'_r.value;
          e = e'_r.value.expr;
          mutated_vars = Set.add (ShadowingTuple.collect_mut_idents e'_r.value) (var, var_typ);
        } in
        Result.{
            bindings = var_binding::e'_r.bindings;
            value = ShadowingTuple.{
                  expr = unit_expr;
                  result_type = None;
                  shadowings = BTyLocIdentUniqueList.empty;
                };
          }
    | Let _ ->
      let lets, body = collect_let_bindings e in
      (* [%yojson_of: ((A.pat * A.expr) list) * A.expr] (lets, body) *)
      (* |> Yojson.Safe.pretty_to_string |> print_endline; *)
      let lets = List.map ~f:(fun (p, e) -> dpat p, dexpr e) lets in
      (* [%yojson_of: (B.pat * (Result.t)) list] lets *)
      (* |> Yojson.Safe.pretty_to_string |> print_endline;         *)
      let r = Result.from_bindings lets (dexpr body) in
      (* ( *)
      (*   [%yojson_of: (local_ident * B.ty) list] (Result.collect_mut_idents r) *)
      (*   |> Yojson.Safe.pretty_to_string |> print_endline *)
      (* ); *)
      let value = Result.as_shadowing_tuple r (Result.collect_mut_idents r |> BTyLocIdentUniqueList.from_set) in
      (* [%yojson_of: (local_ident * B.ty) list] value.shadowings *)
      (* |> Yojson.Safe.pretty_to_string |> print_endline;         *)
      {
        bindings = [];
        value
      }
    | App {f; args} ->
      Result.seq (List.map ~f:dexpr @@ f::args) (function
          | f::args -> B.{
              e = App {f; args};
              typ = dty e.typ;
              span = e.span;
            }
          | _ -> failwith "Internal fatal error: Result.seq didn't kept its promise"
        )
    | _ -> failwith ("dexpr TODO: " ^ [%show: A.expr] e)

  (* let reify_bindings *)
  (*       (required: local_ident list option) *)
  (*       (r: result) *)
  (*     : shadowing_tuple = *)
  (*   let shadowed_names = shadowed_names_of_result r in *)
  (*   let required = Option.value ~default:shadowed_names required in *)
  (*   if List.for_all ~f:(List.mem ~equal:[%eq: local_ident] required) shadowed_names *)
  (*   then 0 else 0 *)

  (* let with_names_of_result *)
  (*       ?(name: string = "value") *)
  (*       (r: result) *)
  (*     : local_ident option * (body:B.expr -> B.expr) = *)
  (*   with_names_of_shadowing_tuple name r.value *)
    
  (*
  let shadowed_names_of_result (r: result): local_ident list =
    List.map ~f:fst r.value.shadowings

      
  module Seq = struct
    type value =
      | Binding of binding
      | Shadowings of shadowing_tuple

    type bundle = {
        order: int;
        handle: int option;
        value: value
      }


      
        
      
    let mk_match (l: (B.pat * result) list): result =
      todo ()
          
    let mk_seq (l: result list) (f: B.expr list -> B.expr): result =
      todo ()

  end

    
  type result
    = { returns: B.expr
      ; shadows: (local_ident * B.ty) list
      }
      [@@deriving show]

  let pure (e0: A.expr) (e: B.expr'): result
    = { returns = {e; span = e0.span; typ = dty e0.typ}
      ; shadows = [] }

 

      
    (* { *)
    (*   returns = List.fold_right ~init:r.returns ~f:(fun (var, e) body -> *)
    (*                 ({ *)
    (*                     body with *)
    (*                     v = B.Let { *)
    (*                             lhs = { *)
    (*                               typ = e.typ; *)
    (*                               v = B.Binding { *)
    (*                                       mut = Immutable; *)
    (*                                       mode = ByValue; *)
    (*                                       var; *)
    (*                                       typ = e.typ; *)
    (*                                       subpat = None; *)
    (*                                     }; *)
    (*                               span = e.span; *)
    (*                             }; *)
    (*                             rhs = e; *)
    (*                             body *)
    (*                           } *)
    (*                   } : B.expr) *)
    (*               ) r.shadows; *)
    (*   shadows = List.map ~f:(fun (var, e) -> *)
    (*                 (var, {e with v = B.LocalVar var}) *)
    (*               ) r.shadows *)
    (* } *)

  (* let shadows_projectors *)
  (*       (bundle: B.expr) *)
  (*       (shadows: (local_ident * B.ty) list) *)
  (*     : B.expr list *)
  (*   = let len = List.length shadows + 1 in *)
  (*     List.mapi ~f:(fun i (_, typ) -> *)
  (*         let nth = i + 1 in *)
  (*         let proj = B.GlobalVar (`Projector (`TupleField (nth, len))) in *)
  (*         ({ span = Dummy *)
  (*          ; typ *)
  (*          ; v = B.App { *)
  (*                    f = { span = Dummy *)
  (*                        ; v = proj *)
  (*                        ; typ = B.Arrow ([bundle.typ], typ) *)
  (*                        }; *)
  (*                    args = [bundle] *)
  (*                } *)
  (*          }: B.expr) *)
  (*       ) shadows *)

  let cons_no_dup (l: (local_ident * 'a) list) (var: local_ident) (x: 'a): (local_ident * 'a) list =
    if List.mem ~equal:equal_local_ident (List.map ~f:fst l) var
    then l
    else (var, x)::l

  let ( @! ) (l: (local_ident * 'a) list) (l': (local_ident * 'a) list)
    = List.fold ~init:l ~f:(fun acc (var, x) -> cons_no_dup acc var x) l'
      

  let with_names (r: result) (name: string): local_ident * (B.expr -> B.expr) =
    let len = List.length r.shadows + 1 in
    let var: local_ident = {name; id = 123} in (* TODO: we need a fresh variable here *)
    let var_pat = make_var_pat var r.returns.typ Dummy in    
    let lhs = make_tuple_pat (
        var_pat::List.map ~f:(fun (var, typ) ->
            make_var_pat var typ Dummy
          ) r.shadows
        |> List.mapi ~f:(make_tuple_field_pat len)
      ) in
    var, fun body -> { body with e = B.Let {lhs; rhs = r.returns; body } }
        
  (* let with_names (r: result) (name: string): local_ident * (B.expr -> B.expr) = *)
    (* if List.is_empty r.shadows *)
  (* then  *)
    
  let rec dexpr (e: A.expr): result =
    match e.e with
    | Literal lit -> pure e @@ B.Literal lit
    | LocalVar v -> pure e @@ B.LocalVar v
    | GlobalVar v -> pure e @@ B.GlobalVar v
    | Assign { lhs = LhsLocalVar var; e = e'; witness } ->
        let {returns; shadows} = dexpr e' in
        {
          returns = make_tuple_expr ~span:e.span @@
              unit_expr::returns::List.map
                ~f:(fun (v, typ) -> B.{e = B.LocalVar v; typ; span = Dummy})
              shadows;
          shadows = cons_no_dup shadows var returns.typ
        }
    | Let { lhs; rhs; body } ->
        let lhs, rhs, body = dpat lhs, dexpr rhs, dexpr body in
        (* 1. reflect [rhs.shadows] in [lhs] *)
        let len = List.length rhs.shadows + 1 in
        let lhs' = make_tuple_pat (
            lhs::List.map ~f:(fun (var, typ) ->
                  make_var_pat var typ Dummy
              ) rhs.shadows
            |> List.mapi ~f:(make_tuple_field_pat len)
          ) in
        let mk_let (body: B.expr) = { body with e = B.Let {lhs = lhs'; rhs = rhs.returns; body } } in
        (* 2. union of [rhs.shadows] with [body.shadows], removing variables of pattern [lhs] *)
        let shadows =
          let local_vars = local_idents_of_pat lhs in
          let is_local = List.mem local_vars ~equal:equal_local_ident in
          rhs.shadows @! List.filter ~f:(fst >> is_local) body.shadows
        in
        prerr_endline ("#############################");
        prerr_endline ("LHS=" ^ [%show: B.pat] lhs);
        prerr_endline ("RHS=" ^ [%show: result] rhs);
        prerr_endline ("BODY=" ^ [%show: result] body);
        prerr_endline ("SHADOWS=" ^ [%show: (local_ident * B.ty) list] shadows);
        (* 3. crafts a tuple that corresponds to [shadows] *)
        let returns = make_tuple_expr ~span:e.span @@
          body.returns
             ::([]
            (* List.map ~f:(fun (var, typ) -> B.{e = B.LocalVar var; span = Dummy; typ}) shadows *)
          ) in
        (* let v = mk_let returns; *)
        {
          returns = mk_let returns;
          shadows = rhs.shadows
        }
    | App {f; args} ->
        let args_r = List.map ~f:dexpr args in
        let f_r = dexpr f in
        if List.for_all ~f:(fun {shadows} -> List.is_empty shadows) @@ f_r::args_r
        then
          let args = List.map ~f:(fun {returns} -> returns) args_r in
          let f = f_r.returns in
          pure e @@ B.App {f; args}
        else 
          let shadows, bds_args, mk_args = List.fold_right ~f:(fun (i, arg) (shadows, binders, acc) ->
                let binder, mk = with_names arg ("arg" ^ string_of_int i) in
              shadows @! arg.shadows, binder::binders, acc << mk
              ) ~init:([], [], Fn.id) (List.mapi ~f:(fun i arg -> (i, arg)) args_r) in
          let f_bd, mk_f = with_names f_r "f" in
          let shadows = shadows @! f_r.shadows in
          let app: B.expr = {
              e = B.App {
                      f = {e = B.LocalVar f_bd; typ = dty f.typ; span = f.span};
                      args = List.map
                               ~f:(fun (var, (arg: A.expr)) -> ({e = B.LocalVar var; typ = dty arg.typ; span = arg.span}: B.expr))
                             @@ List.zip_exn bds_args args;
                    };
              span = e.span;
              typ = dty e.typ
            }
          in
          let tuple = make_tuple_expr ~span:e.span @@ app::(
                        List.map ~f:(fun (var, typ) -> ({e = B.LocalVar var; span = Dummy; typ}: B.expr)) shadows
                      ) in
          { returns = (mk_f << mk_args) tuple;
            shadows
          }
    | Construct {constructor; constructs_record; fields; base = None} ->
        let args = List.map ~f:snd fields in
        let fields_name = List.map ~f:fst fields in
        let args_r = List.map ~f:dexpr args in
        if List.for_all ~f:(fun {shadows} -> List.is_empty shadows) @@ args_r
        then
          let args = List.map ~f:(fun {returns} -> returns) args_r in
          let fields = List.zip_exn fields_name args in
          pure e @@ B.Construct {constructor; constructs_record; fields; base = None}
        else 
          let shadows, bds_args, mk_args = List.fold_right ~f:(fun (i, arg) (shadows, binders, acc) ->
                let binder, mk = with_names arg ("arg" ^ string_of_int i) in
              shadows @! arg.shadows, binder::binders, acc << mk
              ) ~init:([], [], Fn.id) (List.mapi ~f:(fun i arg -> (i, arg)) args_r) in
          let fields = List.zip_exn fields_name args in          
          let app: B.expr = {
            e = B.Construct {
                constructor;
                constructs_record;
                fields = List.map
                    ~f:(fun (var, (arg: A.expr)) -> ({e = B.LocalVar var; typ = dty arg.typ; span = arg.span}: B.expr))
                    (List.zip_exn bds_args args)
                         |> List.zip_exn fields_name;
                base = None
              };
              span = e.span;
              typ = dty e.typ
            }
          in
          let tuple = make_tuple_expr ~span:e.span @@ app::(
                        List.map ~f:(fun (var, typ) -> ({e = B.LocalVar var; span = Dummy; typ}: B.expr)) shadows
                      ) in
          { returns = mk_args tuple;
            shadows
          }
    | Loop _ ->
      (* Here, we should collect all [N] assignations in the body of the loop
         Then [dexpr] the body, but each break should return a tuple of size [N]
       *)
        failwith "TODO loops"    
    | Break { e = e'; label; witness } ->
        failwith "TODO break"
    (* pure e @@ B.Break { e = (dexpr e).returns; label; witness } *)
    | Return {e = ret; witness} ->
       let ret' = dexpr ret in
       pure e
       @@ Return {
              e = {
                e = failwith "TODO return"; (* B.App () ret'.returns; *)
                span = e.span;
                typ = dty e.typ
              };
              witness
            }
       (* { returns = Return {e; witness}; *)
       (*   shadows =  *)
    | Borrow {kind; e; witness} ->
       let e' = dexpr e in
       let borrow, mk = with_names e' "borrow" in
       let shadows = e'.shadows in
       let self: B.expr = {
           typ = dty e.typ;
           span = e.span;
           e = B.Borrow {
                   kind = dborrow_kind kind;
                   e = {
                       typ = dty e.typ;
                       span = e.span;
                       e = B.LocalVar borrow
                     };
                   witness
                 }
         } in
       let tuple = make_tuple_expr ~span:e.span @@ self::(
                     List.map ~f:(fun (var, typ) -> ({e = B.LocalVar var; span = Dummy; typ}: B.expr)) shadows
                   ) in
       { returns = mk tuple; shadows }
    | AddressOf _ | Continue _ | MonadicNode _ -> .
    | e -> failwith ("TODO: " ^ A.show_expr' e)

*)

  let ditem (item: A.item): B.item
    = let v = match item.v with
      | Fn {name; generics; body; params} ->
          B.Fn {
              name;
              generics = {
                  params = [];
                  constraints = [];
                }; (* TODO *)
              body = (Result.as_shadowing_tuple (dexpr body) BTyLocIdentUniqueList.empty).expr;
              params = []
            }
      | other -> B.NotImplementedYet
    in {v; span = item.span}
             
  (* type ('a, 'b) fsig = local_ident list -> 'a -> 'b *)
   
  (* let rec dexpr (e: A.expr): B.expr =  *)
  (*   {v = dexpr' e.v; span = e.span; typ = dty e.typ} *)
  (* and dexpr' (ty) (e: A.expr'): B.expr' = *)
  (*   match e with *)
  (*   | If { cond; then_; else_ } -> *)
  (*     If { cond = dexpr cond; *)
  (*          then_ = dexpr then_; *)
  (*          else_ = Option.map ~f:dexpr else_ *)
  (*        } *)
  (*   | App { f; args } -> *)
  (*     App { f = dexpr f; args = List.map ~f:dexpr args } *)
  (*   | Literal lit -> Literal lit *)
  (*   | Array l -> Array (List.map ~f:dexpr l) *)
  (*   | Construct { constructor *)
  (*               ; constructs_record *)
  (*               ; fields *)
  (*               ; base *)
  (*               } *)
  (*       -> Construct { constructor *)
  (*                    ; constructs_record *)
  (*                    ; fields = List.map ~f:(map_snd dexpr) fields *)
  (*                    ; base = Option.map ~f:dexpr base *)
  (*                    } *)
  (*   | Match { scrutinee; arms } -> *)
  (*     Match { scrutinee = dexpr scrutinee; arms = List.map ~f:darm arms } *)
  (*   | Let { lhs; rhs; body } *)
  (*     -> Let { lhs = dpat lhs; rhs = dexpr rhs; body = dexpr body } *)
  (*   | LocalVar local_ident -> LocalVar local_ident *)
  (*   | GlobalVar global_ident -> GlobalVar global_ident *)
  (*   | Ascription { e; typ } -> Ascription { e = dexpr e; typ = dty typ } *)
  (*   | MacroInvokation { macro; args; witness } -> *)
  (*     MacroInvokation { macro; args; witness } *)
  (*   | Assign { lhs; e; witness } -> Assign { lhs = dlhs lhs; e = dexpr e; witness } *)
  (*   | Loop { body; label; witness } -> *)
  (*     Loop { body = dexpr body; label; witness } *)
  (*   | Break { e; label; witness } -> Break { e = Option.map ~f:dexpr e; label; witness } *)
  (*   | Return { e; witness } -> Return { e = Option.map ~f:dexpr e; witness } *)
  (*   | Continue { label; witness } -> Continue { label; witness } *)
  (*   | Borrow { kind; e; witness } -> Borrow {kind = dborrow_kind kind; e = dexpr e; witness } *)
  (*   | MonadicNode { witness } -> MonadicNode { witness } *)
  (*   | AddressOf { mut; e; witness } -> AddressOf { *)
  (*           mut *)
  (*         ; e = dexpr e *)
  (*         ; witness *)
  (*         } *)
  (* and darm (a: A.arm): B.arm = *)
  (*   {span = a.span; v = darm' a.v } *)
  (* and darm' (a: A.arm'): B.arm' = *)
  (*   { pat = dpat a.pat; body = dexpr a.body } *)
  (* and dlhs (e: A.lhs): B.lhs = *)
  (*   match e with *)
  (*   | FieldAccessor { e; field } -> FieldAccessor { e = dexpr e; field } *)
  (*   | ArrayAccessor { e; index } -> ArrayAccessor { e = dexpr e; index = dexpr index } *)
  (*   | LhsLocalVar id -> LhsLocalVar id *)
end

