open Ast
open! Utils
open Base

module Make =
functor
  (F : Features.T)
  ->
  struct
    [@@@warning "-27"]

    open Make (F)

    class virtual ['self] map =
      object (self : 'self)
        method visit_F__arbitrary_lhs
            : 'env -> F.arbitrary_lhs -> F.arbitrary_lhs =
          fun env___var v___payload -> v___payload

        method visit_F__as_pattern : 'env -> F.as_pattern -> F.as_pattern =
          fun env___var v___payload -> v___payload

        method visit_F__block : 'env -> F.block -> F.block =
          fun env___var v___payload -> v___payload

        method visit_F__break : 'env -> F.break -> F.break =
          fun env___var v___payload -> v___payload

        method visit_F__construct_base
            : 'env -> F.construct_base -> F.construct_base =
          fun env___var v___payload -> v___payload

        method visit_F__continue : 'env -> F.continue -> F.continue =
          fun env___var v___payload -> v___payload

        method visit_F__early_exit : 'env -> F.early_exit -> F.early_exit =
          fun env___var v___payload -> v___payload

        method visit_F__for_index_loop
            : 'env -> F.for_index_loop -> F.for_index_loop =
          fun env___var v___payload -> v___payload

        method visit_F__for_loop : 'env -> F.for_loop -> F.for_loop =
          fun env___var v___payload -> v___payload

        method visit_F__lifetime : 'env -> F.lifetime -> F.lifetime =
          fun env___var v___payload -> v___payload

        method visit_F__loop : 'env -> F.loop -> F.loop =
          fun env___var v___payload -> v___payload

        method visit_F__macro : 'env -> F.macro -> F.macro =
          fun env___var v___payload -> v___payload

        method visit_F__monadic_action
            : 'env -> F.monadic_action -> F.monadic_action =
          fun env___var v___payload -> v___payload

        method visit_F__monadic_binding
            : 'env -> F.monadic_binding -> F.monadic_binding =
          fun env___var v___payload -> v___payload

        method visit_F__mutable_pointer
            : 'env -> F.mutable_pointer -> F.mutable_pointer =
          fun env___var v___payload -> v___payload

        method visit_F__mutable_reference
            : 'env -> F.mutable_reference -> F.mutable_reference =
          fun env___var v___payload -> v___payload

        method visit_F__mutable_variable
            : 'env -> F.mutable_variable -> F.mutable_variable =
          fun env___var v___payload -> v___payload

        method visit_F__nontrivial_lhs
            : 'env -> F.nontrivial_lhs -> F.nontrivial_lhs =
          fun env___var v___payload -> v___payload

        method visit_F__question_mark
            : 'env -> F.question_mark -> F.question_mark =
          fun env___var v___payload -> v___payload

        method visit_F__raw_pointer : 'env -> F.raw_pointer -> F.raw_pointer =
          fun env___var v___payload -> v___payload

        method visit_F__reference : 'env -> F.reference -> F.reference =
          fun env___var v___payload -> v___payload

        method visit_F__slice : 'env -> F.slice -> F.slice =
          fun env___var v___payload -> v___payload

        method visit_F__state_passing_loop
            : 'env -> F.state_passing_loop -> F.state_passing_loop =
          fun env___var v___payload -> v___payload

        method visit_F__while_loop : 'env -> F.while_loop -> F.while_loop =
          fun env___var v___payload -> v___payload

        method visit_Local_ident__t : 'env -> Local_ident.t -> Local_ident.t =
          fun env___var v___payload -> v___payload

        method visit_attr : 'env -> attr -> attr =
          fun env___var v___payload -> v___payload

        method visit_bool : 'env -> bool -> bool =
          fun env___var v___payload -> v___payload

        method visit_char : 'env -> char -> char =
          fun env___var v___payload -> v___payload

        method visit_concrete_ident : 'env -> concrete_ident -> concrete_ident =
          fun env___var v___payload -> v___payload

        method visit_float_kind : 'env -> float_kind -> float_kind =
          fun env___var v___payload -> v___payload

        method visit_global_ident : 'env -> global_ident -> global_ident =
          fun env___var v___payload -> v___payload

        method visit_int_kind : 'env -> int_kind -> int_kind =
          fun env___var v___payload -> v___payload

        method visit_local_ident : 'env -> local_ident -> local_ident =
          fun env___var v___payload -> v___payload

        method visit_quote : 'env -> quote -> quote =
          fun env___var v___payload -> v___payload

        method visit_span : 'env -> span -> span =
          fun env___var v___payload -> v___payload

        method visit_string : 'env -> string -> string =
          fun env___var v___payload -> v___payload

        method visit_todo : 'env -> todo -> todo =
          fun env___var v___payload -> v___payload

        method visit_prim___tuple_2
            : 't0 't1.
              ('env -> 't0 -> 't0) ->
              ('env -> 't1 -> 't1) ->
              'env ->
              't0 * 't1 ->
              't0 * 't1 =
          fun visit_'t0 visit_'t1 env___var v___payload ->
            match v___payload with
            | x0, x1 ->
                let x0 = visit_'t0 env___var x0 in
                let x1 = visit_'t1 env___var x1 in
                (x0, x1)

        method visit_prim___tuple_3
            : 't0 't1 't2.
              ('env -> 't0 -> 't0) ->
              ('env -> 't1 -> 't1) ->
              ('env -> 't2 -> 't2) ->
              'env ->
              't0 * 't1 * 't2 ->
              't0 * 't1 * 't2 =
          fun visit_'t0 visit_'t1 visit_'t2 env___var v___payload ->
            match v___payload with
            | x0, x1, x2 ->
                let x0 = visit_'t0 env___var x0 in
                let x1 = visit_'t1 env___var x1 in
                let x2 = visit_'t2 env___var x2 in
                (x0, x1, x2)

        method visit_prim___tuple_4
            : 't0 't1 't2 't3.
              ('env -> 't0 -> 't0) ->
              ('env -> 't1 -> 't1) ->
              ('env -> 't2 -> 't2) ->
              ('env -> 't3 -> 't3) ->
              'env ->
              't0 * 't1 * 't2 * 't3 ->
              't0 * 't1 * 't2 * 't3 =
          fun visit_'t0 visit_'t1 visit_'t2 visit_'t3 env___var v___payload ->
            match v___payload with
            | x0, x1, x2, x3 ->
                let x0 = visit_'t0 env___var x0 in
                let x1 = visit_'t1 env___var x1 in
                let x2 = visit_'t2 env___var x2 in
                let x3 = visit_'t3 env___var x3 in
                (x0, x1, x2, x3)

        method visit_option
            : 'a. ('env -> 'a -> 'a) -> 'env -> 'a option -> 'a option =
          fun visit_'a env___var v___payload ->
            match v___payload with
            | Some x0 ->
                let x0 = visit_'a env___var x0 in
                Some x0
            | None -> None

        method visit_attrs : 'env -> attrs -> attrs =
          fun env___var v___payload ->
            self#visit_list self#visit_attr env___var v___payload

        method visit_literal : 'env -> literal -> literal =
          fun env___var v___payload ->
            match v___payload with
            | String x0 ->
                let x0 = self#visit_string env___var x0 in
                String x0
            | Char x0 ->
                let x0 = self#visit_char env___var x0 in
                Char x0
            | Int v___payload ->
                let value = self#visit_string env___var v___payload.value in
                let negative = self#visit_bool env___var v___payload.negative in
                let kind = self#visit_int_kind env___var v___payload.kind in
                Int { value; negative; kind }
            | Float v___payload ->
                let value = self#visit_string env___var v___payload.value in
                let negative = self#visit_bool env___var v___payload.negative in
                let kind = self#visit_float_kind env___var v___payload.kind in
                Float { value; negative; kind }
            | Bool x0 ->
                let x0 = self#visit_bool env___var x0 in
                Bool x0

        method visit_mutability
            : 'mut_witness.
              ('env -> 'mut_witness -> 'mut_witness) ->
              'env ->
              'mut_witness mutability ->
              'mut_witness mutability =
          fun visit_'mut_witness env___var v___payload ->
            match v___payload with
            | Mutable x0 ->
                let x0 = visit_'mut_witness env___var x0 in
                Mutable x0
            | Immutable -> Immutable

        method visit_borrow_kind : 'env -> borrow_kind -> borrow_kind =
          fun env___var v___payload ->
            match v___payload with
            | Shared -> Shared
            | Unique -> Unique
            | Mut x0 ->
                let x0 = self#visit_F__mutable_reference env___var x0 in
                Mut x0

        method visit_binding_mode : 'env -> binding_mode -> binding_mode =
          fun env___var v___payload ->
            match v___payload with
            | ByValue -> ByValue
            | ByRef (x0, x1) ->
                let x0 = self#visit_borrow_kind env___var x0 in
                let x1 = self#visit_F__reference env___var x1 in
                ByRef (x0, x1)

        method visit_ty : 'env -> ty -> ty =
          fun env___var v___payload ->
            match v___payload with
            | TBool -> TBool
            | TChar -> TChar
            | TInt x0 ->
                let x0 = self#visit_int_kind env___var x0 in
                TInt x0
            | TFloat x0 ->
                let x0 = self#visit_float_kind env___var x0 in
                TFloat x0
            | TStr -> TStr
            | TApp v___payload ->
                let ident =
                  self#visit_global_ident env___var v___payload.ident
                in
                let args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.args
                in
                TApp { ident; args }
            | TArray v___payload ->
                let typ = self#visit_ty env___var v___payload.typ in
                let length = self#visit_expr env___var v___payload.length in
                TArray { typ; length }
            | TSlice v___payload ->
                let witness =
                  self#visit_F__slice env___var v___payload.witness
                in
                let ty = self#visit_ty env___var v___payload.ty in
                TSlice { witness; ty }
            | TRawPointer v___payload ->
                let witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                TRawPointer { witness }
            | TRef v___payload ->
                let witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                let region = self#visit_todo env___var v___payload.region in
                let typ = self#visit_ty env___var v___payload.typ in
                let mut =
                  self#visit_mutability self#visit_F__mutable_reference
                    env___var v___payload.mut
                in
                TRef { witness; region; typ; mut }
            | TParam x0 ->
                let x0 = self#visit_local_ident env___var x0 in
                TParam x0
            | TArrow (x0, x1) ->
                let x0 = self#visit_list self#visit_ty env___var x0 in
                let x1 = self#visit_ty env___var x1 in
                TArrow (x0, x1)
            | TAssociatedType v___payload ->
                let impl = self#visit_impl_expr env___var v___payload.impl in
                let item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                TAssociatedType { impl; item }
            | TOpaque x0 ->
                let x0 = self#visit_concrete_ident env___var x0 in
                TOpaque x0

        method visit_generic_value : 'env -> generic_value -> generic_value =
          fun env___var v___payload ->
            match v___payload with
            | GLifetime v___payload ->
                let lt = self#visit_todo env___var v___payload.lt in
                let witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                GLifetime { lt; witness }
            | GType x0 ->
                let x0 = self#visit_ty env___var x0 in
                GType x0
            | GConst x0 ->
                let x0 = self#visit_expr env___var x0 in
                GConst x0

        method visit_impl_expr : 'env -> impl_expr -> impl_expr =
          fun env___var v___payload ->
            match v___payload with
            | Self -> Self
            | Concrete x0 ->
                let x0 = self#visit_trait_goal env___var x0 in
                Concrete x0
            | LocalBound v___payload ->
                let id = self#visit_string env___var v___payload.id in
                LocalBound { id }
            | Parent v___payload ->
                let impl = self#visit_impl_expr env___var v___payload.impl in
                let ident = self#visit_impl_ident env___var v___payload.ident in
                Parent { impl; ident }
            | Projection v___payload ->
                let impl = self#visit_impl_expr env___var v___payload.impl in
                let item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                let ident = self#visit_impl_ident env___var v___payload.ident in
                Projection { impl; item; ident }
            | ImplApp v___payload ->
                let impl = self#visit_impl_expr env___var v___payload.impl in
                let args =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.args
                in
                ImplApp { impl; args }
            | Dyn -> Dyn
            | Builtin x0 ->
                let x0 = self#visit_trait_goal env___var x0 in
                Builtin x0

        method visit_trait_goal : 'env -> trait_goal -> trait_goal =
          fun env___var v___payload ->
            let trait = self#visit_concrete_ident env___var v___payload.trait in
            let args =
              self#visit_list self#visit_generic_value env___var
                v___payload.args
            in
            { trait; args }

        method visit_impl_ident : 'env -> impl_ident -> impl_ident =
          fun env___var v___payload ->
            let goal = self#visit_trait_goal env___var v___payload.goal in
            let name = self#visit_string env___var v___payload.name in
            { goal; name }

        method visit_pat' : 'env -> pat' -> pat' =
          fun env___var v___payload ->
            match v___payload with
            | PWild -> PWild
            | PAscription v___payload ->
                let typ = self#visit_ty env___var v___payload.typ in
                let typ_span = self#visit_span env___var v___payload.typ_span in
                let pat = self#visit_pat env___var v___payload.pat in
                PAscription { typ; typ_span; pat }
            | PConstruct v___payload ->
                let name = self#visit_global_ident env___var v___payload.name in
                let args =
                  self#visit_list self#visit_field_pat env___var
                    v___payload.args
                in
                let is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                PConstruct { name; args; is_record; is_struct }
            | POr v___payload ->
                let subpats =
                  self#visit_list self#visit_pat env___var v___payload.subpats
                in
                POr { subpats }
            | PArray v___payload ->
                let args =
                  self#visit_list self#visit_pat env___var v___payload.args
                in
                PArray { args }
            | PDeref v___payload ->
                let subpat = self#visit_pat env___var v___payload.subpat in
                let witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                PDeref { subpat; witness }
            | PConstant v___payload ->
                let lit = self#visit_literal env___var v___payload.lit in
                PConstant { lit }
            | PBinding v___payload ->
                let mut =
                  self#visit_mutability self#visit_F__mutable_variable env___var
                    v___payload.mut
                in
                let mode = self#visit_binding_mode env___var v___payload.mode in
                let var = self#visit_local_ident env___var v___payload.var in
                let typ = self#visit_ty env___var v___payload.typ in
                let subpat =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_pat
                       self#visit_F__as_pattern)
                    env___var v___payload.subpat
                in
                PBinding { mut; mode; var; typ; subpat }

        method visit_pat : 'env -> pat -> pat =
          fun env___var v___payload ->
            let p = self#visit_pat' env___var v___payload.p in
            let span = self#visit_span env___var v___payload.span in
            let typ = self#visit_ty env___var v___payload.typ in
            { p; span; typ }

        method visit_field_pat : 'env -> field_pat -> field_pat =
          fun env___var v___payload ->
            let field = self#visit_global_ident env___var v___payload.field in
            let pat = self#visit_pat env___var v___payload.pat in
            { field; pat }

        method visit_expr' : 'env -> expr' -> expr' =
          fun env___var v___payload ->
            match v___payload with
            | If v___payload ->
                let cond = self#visit_expr env___var v___payload.cond in
                let then_ = self#visit_expr env___var v___payload.then_ in
                let else_ =
                  self#visit_option self#visit_expr env___var v___payload.else_
                in
                If { cond; then_; else_ }
            | App v___payload ->
                let f = self#visit_expr env___var v___payload.f in
                let args =
                  self#visit_list self#visit_expr env___var v___payload.args
                in
                let generic_args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.generic_args
                in
                let bounds_impls =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.bounds_impls
                in
                let impl =
                  self#visit_option self#visit_impl_expr env___var
                    v___payload.impl
                in
                App { f; args; generic_args; bounds_impls; impl }
            | Literal x0 ->
                let x0 = self#visit_literal env___var x0 in
                Literal x0
            | Array x0 ->
                let x0 = self#visit_list self#visit_expr env___var x0 in
                Array x0
            | Construct v___payload ->
                let constructor =
                  self#visit_global_ident env___var v___payload.constructor
                in
                let is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                let fields =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_global_ident
                       self#visit_expr)
                    env___var v___payload.fields
                in
                let base =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_expr
                       self#visit_F__construct_base)
                    env___var v___payload.base
                in
                Construct { constructor; is_record; is_struct; fields; base }
            | Match v___payload ->
                let scrutinee =
                  self#visit_expr env___var v___payload.scrutinee
                in
                let arms =
                  self#visit_list self#visit_arm env___var v___payload.arms
                in
                Match { scrutinee; arms }
            | Let v___payload ->
                let monadic =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_supported_monads
                       self#visit_F__monadic_binding)
                    env___var v___payload.monadic
                in
                let lhs = self#visit_pat env___var v___payload.lhs in
                let rhs = self#visit_expr env___var v___payload.rhs in
                let body = self#visit_expr env___var v___payload.body in
                Let { monadic; lhs; rhs; body }
            | Block (x0, x1) ->
                let x0 = self#visit_expr env___var x0 in
                let x1 = self#visit_F__block env___var x1 in
                Block (x0, x1)
            | LocalVar x0 ->
                let x0 = self#visit_local_ident env___var x0 in
                LocalVar x0
            | GlobalVar x0 ->
                let x0 = self#visit_global_ident env___var x0 in
                GlobalVar x0
            | Ascription v___payload ->
                let e = self#visit_expr env___var v___payload.e in
                let typ = self#visit_ty env___var v___payload.typ in
                Ascription { e; typ }
            | MacroInvokation v___payload ->
                let macro =
                  self#visit_global_ident env___var v___payload.macro
                in
                let args = self#visit_string env___var v___payload.args in
                let witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                MacroInvokation { macro; args; witness }
            | Assign v___payload ->
                let lhs = self#visit_lhs env___var v___payload.lhs in
                let e = self#visit_expr env___var v___payload.e in
                let witness =
                  self#visit_F__mutable_variable env___var v___payload.witness
                in
                Assign { lhs; e; witness }
            | Loop v___payload ->
                let body = self#visit_expr env___var v___payload.body in
                let kind = self#visit_loop_kind env___var v___payload.kind in
                let state =
                  self#visit_option self#visit_loop_state env___var
                    v___payload.state
                in
                let label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness =
                  self#visit_F__loop env___var v___payload.witness
                in
                Loop { body; kind; state; label; witness }
            | Break v___payload ->
                let e = self#visit_expr env___var v___payload.e in
                let label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness =
                  self#visit_prim___tuple_2 self#visit_F__break
                    self#visit_F__loop env___var v___payload.witness
                in
                Break { e; label; witness }
            | Return v___payload ->
                let e = self#visit_expr env___var v___payload.e in
                let witness =
                  self#visit_F__early_exit env___var v___payload.witness
                in
                Return { e; witness }
            | QuestionMark v___payload ->
                let e = self#visit_expr env___var v___payload.e in
                let return_typ =
                  self#visit_ty env___var v___payload.return_typ
                in
                let witness =
                  self#visit_F__question_mark env___var v___payload.witness
                in
                QuestionMark { e; return_typ; witness }
            | Continue v___payload ->
                let e =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_F__state_passing_loop
                       self#visit_expr)
                    env___var v___payload.e
                in
                let label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness =
                  self#visit_prim___tuple_2 self#visit_F__continue
                    self#visit_F__loop env___var v___payload.witness
                in
                Continue { e; label; witness }
            | Borrow v___payload ->
                let kind = self#visit_borrow_kind env___var v___payload.kind in
                let e = self#visit_expr env___var v___payload.e in
                let witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                Borrow { kind; e; witness }
            | AddressOf v___payload ->
                let mut =
                  self#visit_mutability self#visit_F__mutable_pointer env___var
                    v___payload.mut
                in
                let e = self#visit_expr env___var v___payload.e in
                let witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                AddressOf { mut; e; witness }
            | Closure v___payload ->
                let params =
                  self#visit_list self#visit_pat env___var v___payload.params
                in
                let body = self#visit_expr env___var v___payload.body in
                let captures =
                  self#visit_list self#visit_expr env___var v___payload.captures
                in
                Closure { params; body; captures }
            | EffectAction v___payload ->
                let action =
                  self#visit_F__monadic_action env___var v___payload.action
                in
                let argument = self#visit_expr env___var v___payload.argument in
                EffectAction { action; argument }
            | Quote x0 ->
                let x0 = self#visit_quote env___var x0 in
                Quote x0

        method visit_expr : 'env -> expr -> expr =
          fun env___var v___payload ->
            let e = self#visit_expr' env___var v___payload.e in
            let span = self#visit_span env___var v___payload.span in
            let typ = self#visit_ty env___var v___payload.typ in
            { e; span; typ }

        method visit_supported_monads
            : 'env -> supported_monads -> supported_monads =
          fun env___var v___payload ->
            match v___payload with
            | MException x0 ->
                let x0 = self#visit_ty env___var x0 in
                MException x0
            | MResult x0 ->
                let x0 = self#visit_ty env___var x0 in
                MResult x0
            | MOption -> MOption

        method visit_loop_kind : 'env -> loop_kind -> loop_kind =
          fun env___var v___payload ->
            match v___payload with
            | UnconditionalLoop -> UnconditionalLoop
            | WhileLoop v___payload ->
                let condition =
                  self#visit_expr env___var v___payload.condition
                in
                let witness =
                  self#visit_F__while_loop env___var v___payload.witness
                in
                WhileLoop { condition; witness }
            | ForLoop v___payload ->
                let pat = self#visit_pat env___var v___payload.pat in
                let it = self#visit_expr env___var v___payload.it in
                let witness =
                  self#visit_F__for_loop env___var v___payload.witness
                in
                ForLoop { pat; it; witness }
            | ForIndexLoop v___payload ->
                let start = self#visit_expr env___var v___payload.start in
                let end_ = self#visit_expr env___var v___payload.end_ in
                let var = self#visit_local_ident env___var v___payload.var in
                let var_typ = self#visit_ty env___var v___payload.var_typ in
                let witness =
                  self#visit_F__for_index_loop env___var v___payload.witness
                in
                ForIndexLoop { start; end_; var; var_typ; witness }

        method visit_loop_state : 'env -> loop_state -> loop_state =
          fun env___var v___payload ->
            let init = self#visit_expr env___var v___payload.init in
            let bpat = self#visit_pat env___var v___payload.bpat in
            let witness =
              self#visit_F__state_passing_loop env___var v___payload.witness
            in
            { init; bpat; witness }

        method visit_lhs : 'env -> lhs -> lhs =
          fun env___var v___payload ->
            match v___payload with
            | LhsLocalVar v___payload ->
                let var = self#visit_Local_ident__t env___var v___payload.var in
                let typ = self#visit_ty env___var v___payload.typ in
                LhsLocalVar { var; typ }
            | LhsArbitraryExpr v___payload ->
                let e = self#visit_expr env___var v___payload.e in
                let witness =
                  self#visit_F__arbitrary_lhs env___var v___payload.witness
                in
                LhsArbitraryExpr { e; witness }
            | LhsFieldAccessor v___payload ->
                let e = self#visit_lhs env___var v___payload.e in
                let typ = self#visit_ty env___var v___payload.typ in
                let field =
                  self#visit_global_ident env___var v___payload.field
                in
                let witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                LhsFieldAccessor { e; typ; field; witness }
            | LhsArrayAccessor v___payload ->
                let e = self#visit_lhs env___var v___payload.e in
                let typ = self#visit_ty env___var v___payload.typ in
                let index = self#visit_expr env___var v___payload.index in
                let witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                LhsArrayAccessor { e; typ; index; witness }

        method visit_arm' : 'env -> arm' -> arm' =
          fun env___var v___payload ->
            let arm_pat = self#visit_pat env___var v___payload.arm_pat in
            let body = self#visit_expr env___var v___payload.body in
            { arm_pat; body }

        method visit_arm : 'env -> arm -> arm =
          fun env___var v___payload ->
            let arm = self#visit_arm' env___var v___payload.arm in
            let span = self#visit_span env___var v___payload.span in
            { arm; span }

        method visit_generic_param : 'env -> generic_param -> generic_param =
          fun env___var v___payload ->
            let ident = self#visit_local_ident env___var v___payload.ident in
            let span = self#visit_span env___var v___payload.span in
            let attrs = self#visit_attrs env___var v___payload.attrs in
            let kind =
              self#visit_generic_param_kind env___var v___payload.kind
            in
            { ident; span; attrs; kind }

        method visit_generic_param_kind
            : 'env -> generic_param_kind -> generic_param_kind =
          fun env___var v___payload ->
            match v___payload with
            | GPLifetime v___payload ->
                let witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                GPLifetime { witness }
            | GPType v___payload ->
                let default =
                  self#visit_option self#visit_ty env___var v___payload.default
                in
                GPType { default }
            | GPConst v___payload ->
                let typ = self#visit_ty env___var v___payload.typ in
                GPConst { typ }

        method visit_generic_constraint
            : 'env -> generic_constraint -> generic_constraint =
          fun env___var v___payload ->
            match v___payload with
            | GCLifetime (x0, x1) ->
                let x0 = self#visit_todo env___var x0 in
                let x1 = self#visit_F__lifetime env___var x1 in
                GCLifetime (x0, x1)
            | GCType x0 ->
                let x0 = self#visit_impl_ident env___var x0 in
                GCType x0

        method visit_param : 'env -> param -> param =
          fun env___var v___payload ->
            let pat = self#visit_pat env___var v___payload.pat in
            let typ = self#visit_ty env___var v___payload.typ in
            let typ_span =
              self#visit_option self#visit_span env___var v___payload.typ_span
            in
            let attrs = self#visit_attrs env___var v___payload.attrs in
            { pat; typ; typ_span; attrs }

        method visit_generics : 'env -> generics -> generics =
          fun env___var v___payload ->
            let params =
              self#visit_list self#visit_generic_param env___var
                v___payload.params
            in
            let constraints =
              self#visit_list self#visit_generic_constraint env___var
                v___payload.constraints
            in
            { params; constraints }

        method visit_variant : 'env -> variant -> variant =
          fun env___var v___payload ->
            let name = self#visit_concrete_ident env___var v___payload.name in
            let arguments =
              self#visit_list
                (self#visit_prim___tuple_3 self#visit_concrete_ident
                   self#visit_ty self#visit_attrs)
                env___var v___payload.arguments
            in
            let is_record = self#visit_bool env___var v___payload.is_record in
            let attrs = self#visit_attrs env___var v___payload.attrs in
            { name; arguments; is_record; attrs }

        method visit_item' : 'env -> item' -> item' =
          fun env___var v___payload ->
            match v___payload with
            | Fn v___payload ->
                let name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics =
                  self#visit_generics env___var v___payload.generics
                in
                let body = self#visit_expr env___var v___payload.body in
                let params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                Fn { name; generics; body; params }
            | TyAlias v___payload ->
                let name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics =
                  self#visit_generics env___var v___payload.generics
                in
                let ty = self#visit_ty env___var v___payload.ty in
                TyAlias { name; generics; ty }
            | Type v___payload ->
                let name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics =
                  self#visit_generics env___var v___payload.generics
                in
                let variants =
                  self#visit_list self#visit_variant env___var
                    v___payload.variants
                in
                let is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                Type { name; generics; variants; is_struct }
            | IMacroInvokation v___payload ->
                let macro =
                  self#visit_concrete_ident env___var v___payload.macro
                in
                let argument =
                  self#visit_string env___var v___payload.argument
                in
                let span = self#visit_span env___var v___payload.span in
                let witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                IMacroInvokation { macro; argument; span; witness }
            | Trait v___payload ->
                let name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics =
                  self#visit_generics env___var v___payload.generics
                in
                let items =
                  self#visit_list self#visit_trait_item env___var
                    v___payload.items
                in
                Trait { name; generics; items }
            | Impl v___payload ->
                let generics =
                  self#visit_generics env___var v___payload.generics
                in
                let self_ty = self#visit_ty env___var v___payload.self_ty in
                let of_trait =
                  self#visit_prim___tuple_2 self#visit_global_ident
                    (self#visit_list self#visit_generic_value)
                    env___var v___payload.of_trait
                in
                let items =
                  self#visit_list self#visit_impl_item env___var
                    v___payload.items
                in
                let parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                Impl { generics; self_ty; of_trait; items; parent_bounds }
            | Alias v___payload ->
                let name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                Alias { name; item }
            | Use v___payload ->
                let path =
                  self#visit_list self#visit_string env___var v___payload.path
                in
                let is_external =
                  self#visit_bool env___var v___payload.is_external
                in
                let rename =
                  self#visit_option self#visit_string env___var
                    v___payload.rename
                in
                Use { path; is_external; rename }
            | Quote x0 ->
                let x0 = self#visit_quote env___var x0 in
                Quote x0
            | HaxError x0 ->
                let x0 = self#visit_string env___var x0 in
                HaxError x0
            | NotImplementedYet -> NotImplementedYet

        method visit_item : 'env -> item -> item =
          fun env___var v___payload ->
            let v = self#visit_item' env___var v___payload.v in
            let span = self#visit_span env___var v___payload.span in
            let ident = self#visit_concrete_ident env___var v___payload.ident in
            let attrs = self#visit_attrs env___var v___payload.attrs in
            { v; span; ident; attrs }

        method visit_impl_item' : 'env -> impl_item' -> impl_item' =
          fun env___var v___payload ->
            match v___payload with
            | IIType v___payload ->
                let typ = self#visit_ty env___var v___payload.typ in
                let parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                IIType { typ; parent_bounds }
            | IIFn v___payload ->
                let body = self#visit_expr env___var v___payload.body in
                let params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                IIFn { body; params }

        method visit_impl_item : 'env -> impl_item -> impl_item =
          fun env___var v___payload ->
            let ii_span = self#visit_span env___var v___payload.ii_span in
            let ii_generics =
              self#visit_generics env___var v___payload.ii_generics
            in
            let ii_v = self#visit_impl_item' env___var v___payload.ii_v in
            let ii_ident =
              self#visit_concrete_ident env___var v___payload.ii_ident
            in
            let ii_attrs = self#visit_attrs env___var v___payload.ii_attrs in
            { ii_span; ii_generics; ii_v; ii_ident; ii_attrs }

        method visit_trait_item' : 'env -> trait_item' -> trait_item' =
          fun env___var v___payload ->
            match v___payload with
            | TIType x0 ->
                let x0 = self#visit_list self#visit_impl_ident env___var x0 in
                TIType x0
            | TIFn x0 ->
                let x0 = self#visit_ty env___var x0 in
                TIFn x0

        method visit_trait_item : 'env -> trait_item -> trait_item =
          fun env___var v___payload ->
            let ti_span = self#visit_span env___var v___payload.ti_span in
            let ti_generics =
              self#visit_generics env___var v___payload.ti_generics
            in
            let ti_v = self#visit_trait_item' env___var v___payload.ti_v in
            let ti_ident =
              self#visit_concrete_ident env___var v___payload.ti_ident
            in
            let ti_attrs = self#visit_attrs env___var v___payload.ti_attrs in
            { ti_span; ti_generics; ti_v; ti_ident; ti_attrs }

        method visit_modul : 'env -> modul -> modul =
          fun env___var v___payload ->
            self#visit_list self#visit_item env___var v___payload

        method visit_list : 'a. ('env -> 'a -> 'a) -> 'env -> 'a list -> 'a list
            =
          fun v env -> Base.List.map ~f:(v env)
      end

    class virtual ['self] mapreduce =
      object (self : 'self)
        method visit_F__arbitrary_lhs
            : 'env -> F.arbitrary_lhs -> F.arbitrary_lhs * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__as_pattern : 'env -> F.as_pattern -> F.as_pattern * 'acc
            =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__block : 'env -> F.block -> F.block * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__break : 'env -> F.break -> F.break * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__construct_base
            : 'env -> F.construct_base -> F.construct_base * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__continue : 'env -> F.continue -> F.continue * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__early_exit : 'env -> F.early_exit -> F.early_exit * 'acc
            =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__for_index_loop
            : 'env -> F.for_index_loop -> F.for_index_loop * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__for_loop : 'env -> F.for_loop -> F.for_loop * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__lifetime : 'env -> F.lifetime -> F.lifetime * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__loop : 'env -> F.loop -> F.loop * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__macro : 'env -> F.macro -> F.macro * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__monadic_action
            : 'env -> F.monadic_action -> F.monadic_action * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__monadic_binding
            : 'env -> F.monadic_binding -> F.monadic_binding * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__mutable_pointer
            : 'env -> F.mutable_pointer -> F.mutable_pointer * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__mutable_reference
            : 'env -> F.mutable_reference -> F.mutable_reference * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__mutable_variable
            : 'env -> F.mutable_variable -> F.mutable_variable * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__nontrivial_lhs
            : 'env -> F.nontrivial_lhs -> F.nontrivial_lhs * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__question_mark
            : 'env -> F.question_mark -> F.question_mark * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__raw_pointer
            : 'env -> F.raw_pointer -> F.raw_pointer * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__reference : 'env -> F.reference -> F.reference * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__slice : 'env -> F.slice -> F.slice * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__state_passing_loop
            : 'env -> F.state_passing_loop -> F.state_passing_loop * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_F__while_loop : 'env -> F.while_loop -> F.while_loop * 'acc
            =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_Local_ident__t
            : 'env -> Local_ident.t -> Local_ident.t * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_attr : 'env -> attr -> attr * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_bool : 'env -> bool -> bool * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_char : 'env -> char -> char * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_concrete_ident
            : 'env -> concrete_ident -> concrete_ident * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_float_kind : 'env -> float_kind -> float_kind * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_global_ident : 'env -> global_ident -> global_ident * 'acc
            =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_int_kind : 'env -> int_kind -> int_kind * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_local_ident : 'env -> local_ident -> local_ident * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_quote : 'env -> quote -> quote * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_span : 'env -> span -> span * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_string : 'env -> string -> string * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_todo : 'env -> todo -> todo * 'acc =
          fun env___var v___payload -> (v___payload, self#zero)

        method visit_prim___tuple_2
            : 't0 't1.
              ('env -> 't0 -> 't0 * 'acc) ->
              ('env -> 't1 -> 't1 * 'acc) ->
              'env ->
              't0 * 't1 ->
              ('t0 * 't1) * 'acc =
          fun visit_'t0 visit_'t1 env___var v___payload ->
            match v___payload with
            | x0, x1 ->
                let x0, a0 = visit_'t0 env___var x0 in
                let x1, a1 = visit_'t1 env___var x1 in
                ((x0, x1), self#plus a0 a1)

        method visit_prim___tuple_3
            : 't0 't1 't2.
              ('env -> 't0 -> 't0 * 'acc) ->
              ('env -> 't1 -> 't1 * 'acc) ->
              ('env -> 't2 -> 't2 * 'acc) ->
              'env ->
              't0 * 't1 * 't2 ->
              ('t0 * 't1 * 't2) * 'acc =
          fun visit_'t0 visit_'t1 visit_'t2 env___var v___payload ->
            match v___payload with
            | x0, x1, x2 ->
                let x0, a0 = visit_'t0 env___var x0 in
                let x1, a1 = visit_'t1 env___var x1 in
                let x2, a2 = visit_'t2 env___var x2 in
                ((x0, x1, x2), self#plus (self#plus a0 a1) a2)

        method visit_prim___tuple_4
            : 't0 't1 't2 't3.
              ('env -> 't0 -> 't0 * 'acc) ->
              ('env -> 't1 -> 't1 * 'acc) ->
              ('env -> 't2 -> 't2 * 'acc) ->
              ('env -> 't3 -> 't3 * 'acc) ->
              'env ->
              't0 * 't1 * 't2 * 't3 ->
              ('t0 * 't1 * 't2 * 't3) * 'acc =
          fun visit_'t0 visit_'t1 visit_'t2 visit_'t3 env___var v___payload ->
            match v___payload with
            | x0, x1, x2, x3 ->
                let x0, a0 = visit_'t0 env___var x0 in
                let x1, a1 = visit_'t1 env___var x1 in
                let x2, a2 = visit_'t2 env___var x2 in
                let x3, a3 = visit_'t3 env___var x3 in
                ((x0, x1, x2, x3), self#plus (self#plus (self#plus a0 a1) a2) a3)

        method visit_option
            : 'a.
              ('env -> 'a -> 'a * 'acc) -> 'env -> 'a option -> 'a option * 'acc
            =
          fun visit_'a env___var v___payload ->
            match v___payload with
            | Some x0 ->
                let x0, a0 = visit_'a env___var x0 in
                (Some x0, a0)
            | None -> (None, self#zero)

        method visit_attrs : 'env -> attrs -> attrs * 'acc =
          fun env___var v___payload ->
            self#visit_list self#visit_attr env___var v___payload

        method visit_literal : 'env -> literal -> literal * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | String x0 ->
                let x0, a0 = self#visit_string env___var x0 in
                (String x0, a0)
            | Char x0 ->
                let x0, a0 = self#visit_char env___var x0 in
                (Char x0, a0)
            | Int v___payload ->
                let value, acc___value =
                  self#visit_string env___var v___payload.value
                in
                let negative, acc___negative =
                  self#visit_bool env___var v___payload.negative
                in
                let kind, acc___kind =
                  self#visit_int_kind env___var v___payload.kind
                in
                ( Int { value; negative; kind },
                  self#plus (self#plus acc___value acc___negative) acc___kind )
            | Float v___payload ->
                let value, acc___value =
                  self#visit_string env___var v___payload.value
                in
                let negative, acc___negative =
                  self#visit_bool env___var v___payload.negative
                in
                let kind, acc___kind =
                  self#visit_float_kind env___var v___payload.kind
                in
                ( Float { value; negative; kind },
                  self#plus (self#plus acc___value acc___negative) acc___kind )
            | Bool x0 ->
                let x0, a0 = self#visit_bool env___var x0 in
                (Bool x0, a0)

        method visit_mutability
            : 'mut_witness.
              ('env -> 'mut_witness -> 'mut_witness * 'acc) ->
              'env ->
              'mut_witness mutability ->
              'mut_witness mutability * 'acc =
          fun visit_'mut_witness env___var v___payload ->
            match v___payload with
            | Mutable x0 ->
                let x0, a0 = visit_'mut_witness env___var x0 in
                (Mutable x0, a0)
            | Immutable -> (Immutable, self#zero)

        method visit_borrow_kind : 'env -> borrow_kind -> borrow_kind * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Shared -> (Shared, self#zero)
            | Unique -> (Unique, self#zero)
            | Mut x0 ->
                let x0, a0 = self#visit_F__mutable_reference env___var x0 in
                (Mut x0, a0)

        method visit_binding_mode : 'env -> binding_mode -> binding_mode * 'acc
            =
          fun env___var v___payload ->
            match v___payload with
            | ByValue -> (ByValue, self#zero)
            | ByRef (x0, x1) ->
                let x0, a0 = self#visit_borrow_kind env___var x0 in
                let x1, a1 = self#visit_F__reference env___var x1 in
                (ByRef (x0, x1), self#plus a0 a1)

        method visit_ty : 'env -> ty -> ty * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | TBool -> (TBool, self#zero)
            | TChar -> (TChar, self#zero)
            | TInt x0 ->
                let x0, a0 = self#visit_int_kind env___var x0 in
                (TInt x0, a0)
            | TFloat x0 ->
                let x0, a0 = self#visit_float_kind env___var x0 in
                (TFloat x0, a0)
            | TStr -> (TStr, self#zero)
            | TApp v___payload ->
                let ident, acc___ident =
                  self#visit_global_ident env___var v___payload.ident
                in
                let args, acc___args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.args
                in
                (TApp { ident; args }, self#plus acc___ident acc___args)
            | TArray v___payload ->
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let length, acc___length =
                  self#visit_expr env___var v___payload.length
                in
                (TArray { typ; length }, self#plus acc___typ acc___length)
            | TSlice v___payload ->
                let witness, acc___witness =
                  self#visit_F__slice env___var v___payload.witness
                in
                let ty, acc___ty = self#visit_ty env___var v___payload.ty in
                (TSlice { witness; ty }, self#plus acc___witness acc___ty)
            | TRawPointer v___payload ->
                let witness, acc___witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                (TRawPointer { witness }, acc___witness)
            | TRef v___payload ->
                let witness, acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                let region, acc___region =
                  self#visit_todo env___var v___payload.region
                in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let mut, acc___mut =
                  self#visit_mutability self#visit_F__mutable_reference
                    env___var v___payload.mut
                in
                ( TRef { witness; region; typ; mut },
                  self#plus
                    (self#plus (self#plus acc___witness acc___region) acc___typ)
                    acc___mut )
            | TParam x0 ->
                let x0, a0 = self#visit_local_ident env___var x0 in
                (TParam x0, a0)
            | TArrow (x0, x1) ->
                let x0, a0 = self#visit_list self#visit_ty env___var x0 in
                let x1, a1 = self#visit_ty env___var x1 in
                (TArrow (x0, x1), self#plus a0 a1)
            | TAssociatedType v___payload ->
                let impl, acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let item, acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                (TAssociatedType { impl; item }, self#plus acc___impl acc___item)
            | TOpaque x0 ->
                let x0, a0 = self#visit_concrete_ident env___var x0 in
                (TOpaque x0, a0)

        method visit_generic_value
            : 'env -> generic_value -> generic_value * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GLifetime v___payload ->
                let lt, acc___lt = self#visit_todo env___var v___payload.lt in
                let witness, acc___witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                (GLifetime { lt; witness }, self#plus acc___lt acc___witness)
            | GType x0 ->
                let x0, a0 = self#visit_ty env___var x0 in
                (GType x0, a0)
            | GConst x0 ->
                let x0, a0 = self#visit_expr env___var x0 in
                (GConst x0, a0)

        method visit_impl_expr : 'env -> impl_expr -> impl_expr * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Self -> (Self, self#zero)
            | Concrete x0 ->
                let x0, a0 = self#visit_trait_goal env___var x0 in
                (Concrete x0, a0)
            | LocalBound v___payload ->
                let id, acc___id = self#visit_string env___var v___payload.id in
                (LocalBound { id }, acc___id)
            | Parent v___payload ->
                let impl, acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let ident, acc___ident =
                  self#visit_impl_ident env___var v___payload.ident
                in
                (Parent { impl; ident }, self#plus acc___impl acc___ident)
            | Projection v___payload ->
                let impl, acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let item, acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                let ident, acc___ident =
                  self#visit_impl_ident env___var v___payload.ident
                in
                ( Projection { impl; item; ident },
                  self#plus (self#plus acc___impl acc___item) acc___ident )
            | ImplApp v___payload ->
                let impl, acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let args, acc___args =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.args
                in
                (ImplApp { impl; args }, self#plus acc___impl acc___args)
            | Dyn -> (Dyn, self#zero)
            | Builtin x0 ->
                let x0, a0 = self#visit_trait_goal env___var x0 in
                (Builtin x0, a0)

        method visit_trait_goal : 'env -> trait_goal -> trait_goal * 'acc =
          fun env___var v___payload ->
            let trait, acc___trait =
              self#visit_concrete_ident env___var v___payload.trait
            in
            let args, acc___args =
              self#visit_list self#visit_generic_value env___var
                v___payload.args
            in
            ({ trait; args }, self#plus acc___trait acc___args)

        method visit_impl_ident : 'env -> impl_ident -> impl_ident * 'acc =
          fun env___var v___payload ->
            let goal, acc___goal =
              self#visit_trait_goal env___var v___payload.goal
            in
            let name, acc___name =
              self#visit_string env___var v___payload.name
            in
            ({ goal; name }, self#plus acc___goal acc___name)

        method visit_pat' : 'env -> pat' -> pat' * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | PWild -> (PWild, self#zero)
            | PAscription v___payload ->
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let typ_span, acc___typ_span =
                  self#visit_span env___var v___payload.typ_span
                in
                let pat, acc___pat = self#visit_pat env___var v___payload.pat in
                ( PAscription { typ; typ_span; pat },
                  self#plus (self#plus acc___typ acc___typ_span) acc___pat )
            | PConstruct v___payload ->
                let name, acc___name =
                  self#visit_global_ident env___var v___payload.name
                in
                let args, acc___args =
                  self#visit_list self#visit_field_pat env___var
                    v___payload.args
                in
                let is_record, acc___is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let is_struct, acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                ( PConstruct { name; args; is_record; is_struct },
                  self#plus
                    (self#plus
                       (self#plus acc___name acc___args)
                       acc___is_record)
                    acc___is_struct )
            | POr v___payload ->
                let subpats, acc___subpats =
                  self#visit_list self#visit_pat env___var v___payload.subpats
                in
                (POr { subpats }, acc___subpats)
            | PArray v___payload ->
                let args, acc___args =
                  self#visit_list self#visit_pat env___var v___payload.args
                in
                (PArray { args }, acc___args)
            | PDeref v___payload ->
                let subpat, acc___subpat =
                  self#visit_pat env___var v___payload.subpat
                in
                let witness, acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                ( PDeref { subpat; witness },
                  self#plus acc___subpat acc___witness )
            | PConstant v___payload ->
                let lit, acc___lit =
                  self#visit_literal env___var v___payload.lit
                in
                (PConstant { lit }, acc___lit)
            | PBinding v___payload ->
                let mut, acc___mut =
                  self#visit_mutability self#visit_F__mutable_variable env___var
                    v___payload.mut
                in
                let mode, acc___mode =
                  self#visit_binding_mode env___var v___payload.mode
                in
                let var, acc___var =
                  self#visit_local_ident env___var v___payload.var
                in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let subpat, acc___subpat =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_pat
                       self#visit_F__as_pattern)
                    env___var v___payload.subpat
                in
                ( PBinding { mut; mode; var; typ; subpat },
                  self#plus
                    (self#plus
                       (self#plus (self#plus acc___mut acc___mode) acc___var)
                       acc___typ)
                    acc___subpat )

        method visit_pat : 'env -> pat -> pat * 'acc =
          fun env___var v___payload ->
            let p, acc___p = self#visit_pat' env___var v___payload.p in
            let span, acc___span = self#visit_span env___var v___payload.span in
            let typ, acc___typ = self#visit_ty env___var v___payload.typ in
            ( { p; span; typ },
              self#plus (self#plus acc___p acc___span) acc___typ )

        method visit_field_pat : 'env -> field_pat -> field_pat * 'acc =
          fun env___var v___payload ->
            let field, acc___field =
              self#visit_global_ident env___var v___payload.field
            in
            let pat, acc___pat = self#visit_pat env___var v___payload.pat in
            ({ field; pat }, self#plus acc___field acc___pat)

        method visit_expr' : 'env -> expr' -> expr' * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | If v___payload ->
                let cond, acc___cond =
                  self#visit_expr env___var v___payload.cond
                in
                let then_, acc___then_ =
                  self#visit_expr env___var v___payload.then_
                in
                let else_, acc___else_ =
                  self#visit_option self#visit_expr env___var v___payload.else_
                in
                ( If { cond; then_; else_ },
                  self#plus (self#plus acc___cond acc___then_) acc___else_ )
            | App v___payload ->
                let f, acc___f = self#visit_expr env___var v___payload.f in
                let args, acc___args =
                  self#visit_list self#visit_expr env___var v___payload.args
                in
                let generic_args, acc___generic_args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.generic_args
                in
                let bounds_impls, acc___bounds_impls =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.bounds_impls
                in
                let impl, acc___impl =
                  self#visit_option self#visit_impl_expr env___var
                    v___payload.impl
                in
                ( App { f; args; generic_args; bounds_impls; impl },
                  self#plus
                    (self#plus
                       (self#plus
                          (self#plus acc___f acc___args)
                          acc___generic_args)
                       acc___bounds_impls)
                    acc___impl )
            | Literal x0 ->
                let x0, a0 = self#visit_literal env___var x0 in
                (Literal x0, a0)
            | Array x0 ->
                let x0, a0 = self#visit_list self#visit_expr env___var x0 in
                (Array x0, a0)
            | Construct v___payload ->
                let constructor, acc___constructor =
                  self#visit_global_ident env___var v___payload.constructor
                in
                let is_record, acc___is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let is_struct, acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                let fields, acc___fields =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_global_ident
                       self#visit_expr)
                    env___var v___payload.fields
                in
                let base, acc___base =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_expr
                       self#visit_F__construct_base)
                    env___var v___payload.base
                in
                ( Construct { constructor; is_record; is_struct; fields; base },
                  self#plus
                    (self#plus
                       (self#plus
                          (self#plus acc___constructor acc___is_record)
                          acc___is_struct)
                       acc___fields)
                    acc___base )
            | Match v___payload ->
                let scrutinee, acc___scrutinee =
                  self#visit_expr env___var v___payload.scrutinee
                in
                let arms, acc___arms =
                  self#visit_list self#visit_arm env___var v___payload.arms
                in
                (Match { scrutinee; arms }, self#plus acc___scrutinee acc___arms)
            | Let v___payload ->
                let monadic, acc___monadic =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_supported_monads
                       self#visit_F__monadic_binding)
                    env___var v___payload.monadic
                in
                let lhs, acc___lhs = self#visit_pat env___var v___payload.lhs in
                let rhs, acc___rhs =
                  self#visit_expr env___var v___payload.rhs
                in
                let body, acc___body =
                  self#visit_expr env___var v___payload.body
                in
                ( Let { monadic; lhs; rhs; body },
                  self#plus
                    (self#plus (self#plus acc___monadic acc___lhs) acc___rhs)
                    acc___body )
            | Block (x0, x1) ->
                let x0, a0 = self#visit_expr env___var x0 in
                let x1, a1 = self#visit_F__block env___var x1 in
                (Block (x0, x1), self#plus a0 a1)
            | LocalVar x0 ->
                let x0, a0 = self#visit_local_ident env___var x0 in
                (LocalVar x0, a0)
            | GlobalVar x0 ->
                let x0, a0 = self#visit_global_ident env___var x0 in
                (GlobalVar x0, a0)
            | Ascription v___payload ->
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                (Ascription { e; typ }, self#plus acc___e acc___typ)
            | MacroInvokation v___payload ->
                let macro, acc___macro =
                  self#visit_global_ident env___var v___payload.macro
                in
                let args, acc___args =
                  self#visit_string env___var v___payload.args
                in
                let witness, acc___witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                ( MacroInvokation { macro; args; witness },
                  self#plus (self#plus acc___macro acc___args) acc___witness )
            | Assign v___payload ->
                let lhs, acc___lhs = self#visit_lhs env___var v___payload.lhs in
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let witness, acc___witness =
                  self#visit_F__mutable_variable env___var v___payload.witness
                in
                ( Assign { lhs; e; witness },
                  self#plus (self#plus acc___lhs acc___e) acc___witness )
            | Loop v___payload ->
                let body, acc___body =
                  self#visit_expr env___var v___payload.body
                in
                let kind, acc___kind =
                  self#visit_loop_kind env___var v___payload.kind
                in
                let state, acc___state =
                  self#visit_option self#visit_loop_state env___var
                    v___payload.state
                in
                let label, acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness, acc___witness =
                  self#visit_F__loop env___var v___payload.witness
                in
                ( Loop { body; kind; state; label; witness },
                  self#plus
                    (self#plus
                       (self#plus (self#plus acc___body acc___kind) acc___state)
                       acc___label)
                    acc___witness )
            | Break v___payload ->
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let label, acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness, acc___witness =
                  self#visit_prim___tuple_2 self#visit_F__break
                    self#visit_F__loop env___var v___payload.witness
                in
                ( Break { e; label; witness },
                  self#plus (self#plus acc___e acc___label) acc___witness )
            | Return v___payload ->
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let witness, acc___witness =
                  self#visit_F__early_exit env___var v___payload.witness
                in
                (Return { e; witness }, self#plus acc___e acc___witness)
            | QuestionMark v___payload ->
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let return_typ, acc___return_typ =
                  self#visit_ty env___var v___payload.return_typ
                in
                let witness, acc___witness =
                  self#visit_F__question_mark env___var v___payload.witness
                in
                ( QuestionMark { e; return_typ; witness },
                  self#plus (self#plus acc___e acc___return_typ) acc___witness
                )
            | Continue v___payload ->
                let e, acc___e =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_F__state_passing_loop
                       self#visit_expr)
                    env___var v___payload.e
                in
                let label, acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let witness, acc___witness =
                  self#visit_prim___tuple_2 self#visit_F__continue
                    self#visit_F__loop env___var v___payload.witness
                in
                ( Continue { e; label; witness },
                  self#plus (self#plus acc___e acc___label) acc___witness )
            | Borrow v___payload ->
                let kind, acc___kind =
                  self#visit_borrow_kind env___var v___payload.kind
                in
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let witness, acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                ( Borrow { kind; e; witness },
                  self#plus (self#plus acc___kind acc___e) acc___witness )
            | AddressOf v___payload ->
                let mut, acc___mut =
                  self#visit_mutability self#visit_F__mutable_pointer env___var
                    v___payload.mut
                in
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let witness, acc___witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                ( AddressOf { mut; e; witness },
                  self#plus (self#plus acc___mut acc___e) acc___witness )
            | Closure v___payload ->
                let params, acc___params =
                  self#visit_list self#visit_pat env___var v___payload.params
                in
                let body, acc___body =
                  self#visit_expr env___var v___payload.body
                in
                let captures, acc___captures =
                  self#visit_list self#visit_expr env___var v___payload.captures
                in
                ( Closure { params; body; captures },
                  self#plus (self#plus acc___params acc___body) acc___captures
                )
            | EffectAction v___payload ->
                let action, acc___action =
                  self#visit_F__monadic_action env___var v___payload.action
                in
                let argument, acc___argument =
                  self#visit_expr env___var v___payload.argument
                in
                ( EffectAction { action; argument },
                  self#plus acc___action acc___argument )
            | Quote x0 ->
                let x0, a0 = self#visit_quote env___var x0 in
                (Quote x0, a0)

        method visit_expr : 'env -> expr -> expr * 'acc =
          fun env___var v___payload ->
            let e, acc___e = self#visit_expr' env___var v___payload.e in
            let span, acc___span = self#visit_span env___var v___payload.span in
            let typ, acc___typ = self#visit_ty env___var v___payload.typ in
            ( { e; span; typ },
              self#plus (self#plus acc___e acc___span) acc___typ )

        method visit_supported_monads
            : 'env -> supported_monads -> supported_monads * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | MException x0 ->
                let x0, a0 = self#visit_ty env___var x0 in
                (MException x0, a0)
            | MResult x0 ->
                let x0, a0 = self#visit_ty env___var x0 in
                (MResult x0, a0)
            | MOption -> (MOption, self#zero)

        method visit_loop_kind : 'env -> loop_kind -> loop_kind * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | UnconditionalLoop -> (UnconditionalLoop, self#zero)
            | WhileLoop v___payload ->
                let condition, acc___condition =
                  self#visit_expr env___var v___payload.condition
                in
                let witness, acc___witness =
                  self#visit_F__while_loop env___var v___payload.witness
                in
                ( WhileLoop { condition; witness },
                  self#plus acc___condition acc___witness )
            | ForLoop v___payload ->
                let pat, acc___pat = self#visit_pat env___var v___payload.pat in
                let it, acc___it = self#visit_expr env___var v___payload.it in
                let witness, acc___witness =
                  self#visit_F__for_loop env___var v___payload.witness
                in
                ( ForLoop { pat; it; witness },
                  self#plus (self#plus acc___pat acc___it) acc___witness )
            | ForIndexLoop v___payload ->
                let start, acc___start =
                  self#visit_expr env___var v___payload.start
                in
                let end_, acc___end_ =
                  self#visit_expr env___var v___payload.end_
                in
                let var, acc___var =
                  self#visit_local_ident env___var v___payload.var
                in
                let var_typ, acc___var_typ =
                  self#visit_ty env___var v___payload.var_typ
                in
                let witness, acc___witness =
                  self#visit_F__for_index_loop env___var v___payload.witness
                in
                ( ForIndexLoop { start; end_; var; var_typ; witness },
                  self#plus
                    (self#plus
                       (self#plus (self#plus acc___start acc___end_) acc___var)
                       acc___var_typ)
                    acc___witness )

        method visit_loop_state : 'env -> loop_state -> loop_state * 'acc =
          fun env___var v___payload ->
            let init, acc___init = self#visit_expr env___var v___payload.init in
            let bpat, acc___bpat = self#visit_pat env___var v___payload.bpat in
            let witness, acc___witness =
              self#visit_F__state_passing_loop env___var v___payload.witness
            in
            ( { init; bpat; witness },
              self#plus (self#plus acc___init acc___bpat) acc___witness )

        method visit_lhs : 'env -> lhs -> lhs * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | LhsLocalVar v___payload ->
                let var, acc___var =
                  self#visit_Local_ident__t env___var v___payload.var
                in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                (LhsLocalVar { var; typ }, self#plus acc___var acc___typ)
            | LhsArbitraryExpr v___payload ->
                let e, acc___e = self#visit_expr env___var v___payload.e in
                let witness, acc___witness =
                  self#visit_F__arbitrary_lhs env___var v___payload.witness
                in
                ( LhsArbitraryExpr { e; witness },
                  self#plus acc___e acc___witness )
            | LhsFieldAccessor v___payload ->
                let e, acc___e = self#visit_lhs env___var v___payload.e in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let field, acc___field =
                  self#visit_global_ident env___var v___payload.field
                in
                let witness, acc___witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                ( LhsFieldAccessor { e; typ; field; witness },
                  self#plus
                    (self#plus (self#plus acc___e acc___typ) acc___field)
                    acc___witness )
            | LhsArrayAccessor v___payload ->
                let e, acc___e = self#visit_lhs env___var v___payload.e in
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let index, acc___index =
                  self#visit_expr env___var v___payload.index
                in
                let witness, acc___witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                ( LhsArrayAccessor { e; typ; index; witness },
                  self#plus
                    (self#plus (self#plus acc___e acc___typ) acc___index)
                    acc___witness )

        method visit_arm' : 'env -> arm' -> arm' * 'acc =
          fun env___var v___payload ->
            let arm_pat, acc___arm_pat =
              self#visit_pat env___var v___payload.arm_pat
            in
            let body, acc___body = self#visit_expr env___var v___payload.body in
            ({ arm_pat; body }, self#plus acc___arm_pat acc___body)

        method visit_arm : 'env -> arm -> arm * 'acc =
          fun env___var v___payload ->
            let arm, acc___arm = self#visit_arm' env___var v___payload.arm in
            let span, acc___span = self#visit_span env___var v___payload.span in
            ({ arm; span }, self#plus acc___arm acc___span)

        method visit_generic_param
            : 'env -> generic_param -> generic_param * 'acc =
          fun env___var v___payload ->
            let ident, acc___ident =
              self#visit_local_ident env___var v___payload.ident
            in
            let span, acc___span = self#visit_span env___var v___payload.span in
            let attrs, acc___attrs =
              self#visit_attrs env___var v___payload.attrs
            in
            let kind, acc___kind =
              self#visit_generic_param_kind env___var v___payload.kind
            in
            ( { ident; span; attrs; kind },
              self#plus
                (self#plus (self#plus acc___ident acc___span) acc___attrs)
                acc___kind )

        method visit_generic_param_kind
            : 'env -> generic_param_kind -> generic_param_kind * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GPLifetime v___payload ->
                let witness, acc___witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                (GPLifetime { witness }, acc___witness)
            | GPType v___payload ->
                let default, acc___default =
                  self#visit_option self#visit_ty env___var v___payload.default
                in
                (GPType { default }, acc___default)
            | GPConst v___payload ->
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                (GPConst { typ }, acc___typ)

        method visit_generic_constraint
            : 'env -> generic_constraint -> generic_constraint * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GCLifetime (x0, x1) ->
                let x0, a0 = self#visit_todo env___var x0 in
                let x1, a1 = self#visit_F__lifetime env___var x1 in
                (GCLifetime (x0, x1), self#plus a0 a1)
            | GCType x0 ->
                let x0, a0 = self#visit_impl_ident env___var x0 in
                (GCType x0, a0)

        method visit_param : 'env -> param -> param * 'acc =
          fun env___var v___payload ->
            let pat, acc___pat = self#visit_pat env___var v___payload.pat in
            let typ, acc___typ = self#visit_ty env___var v___payload.typ in
            let typ_span, acc___typ_span =
              self#visit_option self#visit_span env___var v___payload.typ_span
            in
            let attrs, acc___attrs =
              self#visit_attrs env___var v___payload.attrs
            in
            ( { pat; typ; typ_span; attrs },
              self#plus
                (self#plus (self#plus acc___pat acc___typ) acc___typ_span)
                acc___attrs )

        method visit_generics : 'env -> generics -> generics * 'acc =
          fun env___var v___payload ->
            let params, acc___params =
              self#visit_list self#visit_generic_param env___var
                v___payload.params
            in
            let constraints, acc___constraints =
              self#visit_list self#visit_generic_constraint env___var
                v___payload.constraints
            in
            ({ params; constraints }, self#plus acc___params acc___constraints)

        method visit_variant : 'env -> variant -> variant * 'acc =
          fun env___var v___payload ->
            let name, acc___name =
              self#visit_concrete_ident env___var v___payload.name
            in
            let arguments, acc___arguments =
              self#visit_list
                (self#visit_prim___tuple_3 self#visit_concrete_ident
                   self#visit_ty self#visit_attrs)
                env___var v___payload.arguments
            in
            let is_record, acc___is_record =
              self#visit_bool env___var v___payload.is_record
            in
            let attrs, acc___attrs =
              self#visit_attrs env___var v___payload.attrs
            in
            ( { name; arguments; is_record; attrs },
              self#plus
                (self#plus
                   (self#plus acc___name acc___arguments)
                   acc___is_record)
                acc___attrs )

        method visit_item' : 'env -> item' -> item' * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Fn v___payload ->
                let name, acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics, acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let body, acc___body =
                  self#visit_expr env___var v___payload.body
                in
                let params, acc___params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                ( Fn { name; generics; body; params },
                  self#plus
                    (self#plus (self#plus acc___name acc___generics) acc___body)
                    acc___params )
            | TyAlias v___payload ->
                let name, acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics, acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let ty, acc___ty = self#visit_ty env___var v___payload.ty in
                ( TyAlias { name; generics; ty },
                  self#plus (self#plus acc___name acc___generics) acc___ty )
            | Type v___payload ->
                let name, acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics, acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let variants, acc___variants =
                  self#visit_list self#visit_variant env___var
                    v___payload.variants
                in
                let is_struct, acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                ( Type { name; generics; variants; is_struct },
                  self#plus
                    (self#plus
                       (self#plus acc___name acc___generics)
                       acc___variants)
                    acc___is_struct )
            | IMacroInvokation v___payload ->
                let macro, acc___macro =
                  self#visit_concrete_ident env___var v___payload.macro
                in
                let argument, acc___argument =
                  self#visit_string env___var v___payload.argument
                in
                let span, acc___span =
                  self#visit_span env___var v___payload.span
                in
                let witness, acc___witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                ( IMacroInvokation { macro; argument; span; witness },
                  self#plus
                    (self#plus
                       (self#plus acc___macro acc___argument)
                       acc___span)
                    acc___witness )
            | Trait v___payload ->
                let name, acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let generics, acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let items, acc___items =
                  self#visit_list self#visit_trait_item env___var
                    v___payload.items
                in
                ( Trait { name; generics; items },
                  self#plus (self#plus acc___name acc___generics) acc___items )
            | Impl v___payload ->
                let generics, acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let self_ty, acc___self_ty =
                  self#visit_ty env___var v___payload.self_ty
                in
                let of_trait, acc___of_trait =
                  self#visit_prim___tuple_2 self#visit_global_ident
                    (self#visit_list self#visit_generic_value)
                    env___var v___payload.of_trait
                in
                let items, acc___items =
                  self#visit_list self#visit_impl_item env___var
                    v___payload.items
                in
                let parent_bounds, acc___parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                ( Impl { generics; self_ty; of_trait; items; parent_bounds },
                  self#plus
                    (self#plus
                       (self#plus
                          (self#plus acc___generics acc___self_ty)
                          acc___of_trait)
                       acc___items)
                    acc___parent_bounds )
            | Alias v___payload ->
                let name, acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let item, acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                (Alias { name; item }, self#plus acc___name acc___item)
            | Use v___payload ->
                let path, acc___path =
                  self#visit_list self#visit_string env___var v___payload.path
                in
                let is_external, acc___is_external =
                  self#visit_bool env___var v___payload.is_external
                in
                let rename, acc___rename =
                  self#visit_option self#visit_string env___var
                    v___payload.rename
                in
                ( Use { path; is_external; rename },
                  self#plus
                    (self#plus acc___path acc___is_external)
                    acc___rename )
            | Quote x0 ->
                let x0, a0 = self#visit_quote env___var x0 in
                (Quote x0, a0)
            | HaxError x0 ->
                let x0, a0 = self#visit_string env___var x0 in
                (HaxError x0, a0)
            | NotImplementedYet -> (NotImplementedYet, self#zero)

        method visit_item : 'env -> item -> item * 'acc =
          fun env___var v___payload ->
            let v, acc___v = self#visit_item' env___var v___payload.v in
            let span, acc___span = self#visit_span env___var v___payload.span in
            let ident, acc___ident =
              self#visit_concrete_ident env___var v___payload.ident
            in
            let attrs, acc___attrs =
              self#visit_attrs env___var v___payload.attrs
            in
            ( { v; span; ident; attrs },
              self#plus
                (self#plus (self#plus acc___v acc___span) acc___ident)
                acc___attrs )

        method visit_impl_item' : 'env -> impl_item' -> impl_item' * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | IIType v___payload ->
                let typ, acc___typ = self#visit_ty env___var v___payload.typ in
                let parent_bounds, acc___parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                ( IIType { typ; parent_bounds },
                  self#plus acc___typ acc___parent_bounds )
            | IIFn v___payload ->
                let body, acc___body =
                  self#visit_expr env___var v___payload.body
                in
                let params, acc___params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                (IIFn { body; params }, self#plus acc___body acc___params)

        method visit_impl_item : 'env -> impl_item -> impl_item * 'acc =
          fun env___var v___payload ->
            let ii_span, acc___ii_span =
              self#visit_span env___var v___payload.ii_span
            in
            let ii_generics, acc___ii_generics =
              self#visit_generics env___var v___payload.ii_generics
            in
            let ii_v, acc___ii_v =
              self#visit_impl_item' env___var v___payload.ii_v
            in
            let ii_ident, acc___ii_ident =
              self#visit_concrete_ident env___var v___payload.ii_ident
            in
            let ii_attrs, acc___ii_attrs =
              self#visit_attrs env___var v___payload.ii_attrs
            in
            ( { ii_span; ii_generics; ii_v; ii_ident; ii_attrs },
              self#plus
                (self#plus
                   (self#plus
                      (self#plus acc___ii_span acc___ii_generics)
                      acc___ii_v)
                   acc___ii_ident)
                acc___ii_attrs )

        method visit_trait_item' : 'env -> trait_item' -> trait_item' * 'acc =
          fun env___var v___payload ->
            match v___payload with
            | TIType x0 ->
                let x0, a0 =
                  self#visit_list self#visit_impl_ident env___var x0
                in
                (TIType x0, a0)
            | TIFn x0 ->
                let x0, a0 = self#visit_ty env___var x0 in
                (TIFn x0, a0)

        method visit_trait_item : 'env -> trait_item -> trait_item * 'acc =
          fun env___var v___payload ->
            let ti_span, acc___ti_span =
              self#visit_span env___var v___payload.ti_span
            in
            let ti_generics, acc___ti_generics =
              self#visit_generics env___var v___payload.ti_generics
            in
            let ti_v, acc___ti_v =
              self#visit_trait_item' env___var v___payload.ti_v
            in
            let ti_ident, acc___ti_ident =
              self#visit_concrete_ident env___var v___payload.ti_ident
            in
            let ti_attrs, acc___ti_attrs =
              self#visit_attrs env___var v___payload.ti_attrs
            in
            ( { ti_span; ti_generics; ti_v; ti_ident; ti_attrs },
              self#plus
                (self#plus
                   (self#plus
                      (self#plus acc___ti_span acc___ti_generics)
                      acc___ti_v)
                   acc___ti_ident)
                acc___ti_attrs )

        method visit_modul : 'env -> modul -> modul * 'acc =
          fun env___var v___payload ->
            self#visit_list self#visit_item env___var v___payload

        method visit_list
            : 'a. ('env -> 'a -> 'a * 'acc) -> 'env -> 'a list -> 'a list * 'acc
            =
          fun v env ->
            Base.List.fold_map ~init:self#zero ~f:(fun acc x ->
                let x, acc' = v env x in
                (self#plus acc acc', x))
            >> swap
      end

    class virtual ['self] reduce =
      object (self : 'self)
        method visit_F__arbitrary_lhs : 'env -> F.arbitrary_lhs -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__as_pattern : 'env -> F.as_pattern -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__block : 'env -> F.block -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__break : 'env -> F.break -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__construct_base : 'env -> F.construct_base -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__continue : 'env -> F.continue -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__early_exit : 'env -> F.early_exit -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__for_index_loop : 'env -> F.for_index_loop -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__for_loop : 'env -> F.for_loop -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__lifetime : 'env -> F.lifetime -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__loop : 'env -> F.loop -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__macro : 'env -> F.macro -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__monadic_action : 'env -> F.monadic_action -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__monadic_binding : 'env -> F.monadic_binding -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__mutable_pointer : 'env -> F.mutable_pointer -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__mutable_reference : 'env -> F.mutable_reference -> 'acc
            =
          fun env___var v___payload -> self#zero

        method visit_F__mutable_variable : 'env -> F.mutable_variable -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__nontrivial_lhs : 'env -> F.nontrivial_lhs -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__question_mark : 'env -> F.question_mark -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__raw_pointer : 'env -> F.raw_pointer -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__reference : 'env -> F.reference -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__slice : 'env -> F.slice -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__state_passing_loop
            : 'env -> F.state_passing_loop -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_F__while_loop : 'env -> F.while_loop -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_Local_ident__t : 'env -> Local_ident.t -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_attr : 'env -> attr -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_bool : 'env -> bool -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_char : 'env -> char -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_concrete_ident : 'env -> concrete_ident -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_float_kind : 'env -> float_kind -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_global_ident : 'env -> global_ident -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_int_kind : 'env -> int_kind -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_local_ident : 'env -> local_ident -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_quote : 'env -> quote -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_span : 'env -> span -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_string : 'env -> string -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_todo : 'env -> todo -> 'acc =
          fun env___var v___payload -> self#zero

        method visit_prim___tuple_2
            : 't0 't1.
              ('env -> 't0 -> 'acc) ->
              ('env -> 't1 -> 'acc) ->
              'env ->
              't0 * 't1 ->
              'acc =
          fun visit_'t0 visit_'t1 env___var v___payload ->
            match v___payload with
            | x0, x1 ->
                let a0 = visit_'t0 env___var x0 in
                let a1 = visit_'t1 env___var x1 in
                self#plus a0 a1

        method visit_prim___tuple_3
            : 't0 't1 't2.
              ('env -> 't0 -> 'acc) ->
              ('env -> 't1 -> 'acc) ->
              ('env -> 't2 -> 'acc) ->
              'env ->
              't0 * 't1 * 't2 ->
              'acc =
          fun visit_'t0 visit_'t1 visit_'t2 env___var v___payload ->
            match v___payload with
            | x0, x1, x2 ->
                let a0 = visit_'t0 env___var x0 in
                let a1 = visit_'t1 env___var x1 in
                let a2 = visit_'t2 env___var x2 in
                self#plus (self#plus a0 a1) a2

        method visit_prim___tuple_4
            : 't0 't1 't2 't3.
              ('env -> 't0 -> 'acc) ->
              ('env -> 't1 -> 'acc) ->
              ('env -> 't2 -> 'acc) ->
              ('env -> 't3 -> 'acc) ->
              'env ->
              't0 * 't1 * 't2 * 't3 ->
              'acc =
          fun visit_'t0 visit_'t1 visit_'t2 visit_'t3 env___var v___payload ->
            match v___payload with
            | x0, x1, x2, x3 ->
                let a0 = visit_'t0 env___var x0 in
                let a1 = visit_'t1 env___var x1 in
                let a2 = visit_'t2 env___var x2 in
                let a3 = visit_'t3 env___var x3 in
                self#plus (self#plus (self#plus a0 a1) a2) a3

        method visit_option
            : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a option -> 'acc =
          fun visit_'a env___var v___payload ->
            match v___payload with
            | Some x0 ->
                let a0 = visit_'a env___var x0 in
                a0
            | None -> self#zero

        method visit_attrs : 'env -> attrs -> 'acc =
          fun env___var v___payload ->
            self#visit_list self#visit_attr env___var v___payload

        method visit_literal : 'env -> literal -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | String x0 ->
                let a0 = self#visit_string env___var x0 in
                a0
            | Char x0 ->
                let a0 = self#visit_char env___var x0 in
                a0
            | Int v___payload ->
                let acc___value =
                  self#visit_string env___var v___payload.value
                in
                let acc___negative =
                  self#visit_bool env___var v___payload.negative
                in
                let acc___kind =
                  self#visit_int_kind env___var v___payload.kind
                in
                self#plus (self#plus acc___value acc___negative) acc___kind
            | Float v___payload ->
                let acc___value =
                  self#visit_string env___var v___payload.value
                in
                let acc___negative =
                  self#visit_bool env___var v___payload.negative
                in
                let acc___kind =
                  self#visit_float_kind env___var v___payload.kind
                in
                self#plus (self#plus acc___value acc___negative) acc___kind
            | Bool x0 ->
                let a0 = self#visit_bool env___var x0 in
                a0

        method visit_mutability
            : 'mut_witness.
              ('env -> 'mut_witness -> 'acc) ->
              'env ->
              'mut_witness mutability ->
              'acc =
          fun visit_'mut_witness env___var v___payload ->
            match v___payload with
            | Mutable x0 ->
                let a0 = visit_'mut_witness env___var x0 in
                a0
            | Immutable -> self#zero

        method visit_borrow_kind : 'env -> borrow_kind -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Shared -> self#zero
            | Unique -> self#zero
            | Mut x0 ->
                let a0 = self#visit_F__mutable_reference env___var x0 in
                a0

        method visit_binding_mode : 'env -> binding_mode -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | ByValue -> self#zero
            | ByRef (x0, x1) ->
                let a0 = self#visit_borrow_kind env___var x0 in
                let a1 = self#visit_F__reference env___var x1 in
                self#plus a0 a1

        method visit_ty : 'env -> ty -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | TBool -> self#zero
            | TChar -> self#zero
            | TInt x0 ->
                let a0 = self#visit_int_kind env___var x0 in
                a0
            | TFloat x0 ->
                let a0 = self#visit_float_kind env___var x0 in
                a0
            | TStr -> self#zero
            | TApp v___payload ->
                let acc___ident =
                  self#visit_global_ident env___var v___payload.ident
                in
                let acc___args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.args
                in
                self#plus acc___ident acc___args
            | TArray v___payload ->
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___length =
                  self#visit_expr env___var v___payload.length
                in
                self#plus acc___typ acc___length
            | TSlice v___payload ->
                let acc___witness =
                  self#visit_F__slice env___var v___payload.witness
                in
                let acc___ty = self#visit_ty env___var v___payload.ty in
                self#plus acc___witness acc___ty
            | TRawPointer v___payload ->
                let acc___witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                acc___witness
            | TRef v___payload ->
                let acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                let acc___region =
                  self#visit_todo env___var v___payload.region
                in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___mut =
                  self#visit_mutability self#visit_F__mutable_reference
                    env___var v___payload.mut
                in
                self#plus
                  (self#plus (self#plus acc___witness acc___region) acc___typ)
                  acc___mut
            | TParam x0 ->
                let a0 = self#visit_local_ident env___var x0 in
                a0
            | TArrow (x0, x1) ->
                let a0 = self#visit_list self#visit_ty env___var x0 in
                let a1 = self#visit_ty env___var x1 in
                self#plus a0 a1
            | TAssociatedType v___payload ->
                let acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                self#plus acc___impl acc___item
            | TOpaque x0 ->
                let a0 = self#visit_concrete_ident env___var x0 in
                a0

        method visit_generic_value : 'env -> generic_value -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GLifetime v___payload ->
                let acc___lt = self#visit_todo env___var v___payload.lt in
                let acc___witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                self#plus acc___lt acc___witness
            | GType x0 ->
                let a0 = self#visit_ty env___var x0 in
                a0
            | GConst x0 ->
                let a0 = self#visit_expr env___var x0 in
                a0

        method visit_impl_expr : 'env -> impl_expr -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Self -> self#zero
            | Concrete x0 ->
                let a0 = self#visit_trait_goal env___var x0 in
                a0
            | LocalBound v___payload ->
                let acc___id = self#visit_string env___var v___payload.id in
                acc___id
            | Parent v___payload ->
                let acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let acc___ident =
                  self#visit_impl_ident env___var v___payload.ident
                in
                self#plus acc___impl acc___ident
            | Projection v___payload ->
                let acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                let acc___ident =
                  self#visit_impl_ident env___var v___payload.ident
                in
                self#plus (self#plus acc___impl acc___item) acc___ident
            | ImplApp v___payload ->
                let acc___impl =
                  self#visit_impl_expr env___var v___payload.impl
                in
                let acc___args =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.args
                in
                self#plus acc___impl acc___args
            | Dyn -> self#zero
            | Builtin x0 ->
                let a0 = self#visit_trait_goal env___var x0 in
                a0

        method visit_trait_goal : 'env -> trait_goal -> 'acc =
          fun env___var v___payload ->
            let acc___trait =
              self#visit_concrete_ident env___var v___payload.trait
            in
            let acc___args =
              self#visit_list self#visit_generic_value env___var
                v___payload.args
            in
            self#plus acc___trait acc___args

        method visit_impl_ident : 'env -> impl_ident -> 'acc =
          fun env___var v___payload ->
            let acc___goal = self#visit_trait_goal env___var v___payload.goal in
            let acc___name = self#visit_string env___var v___payload.name in
            self#plus acc___goal acc___name

        method visit_pat' : 'env -> pat' -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | PWild -> self#zero
            | PAscription v___payload ->
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___typ_span =
                  self#visit_span env___var v___payload.typ_span
                in
                let acc___pat = self#visit_pat env___var v___payload.pat in
                self#plus (self#plus acc___typ acc___typ_span) acc___pat
            | PConstruct v___payload ->
                let acc___name =
                  self#visit_global_ident env___var v___payload.name
                in
                let acc___args =
                  self#visit_list self#visit_field_pat env___var
                    v___payload.args
                in
                let acc___is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                self#plus
                  (self#plus (self#plus acc___name acc___args) acc___is_record)
                  acc___is_struct
            | POr v___payload ->
                let acc___subpats =
                  self#visit_list self#visit_pat env___var v___payload.subpats
                in
                acc___subpats
            | PArray v___payload ->
                let acc___args =
                  self#visit_list self#visit_pat env___var v___payload.args
                in
                acc___args
            | PDeref v___payload ->
                let acc___subpat =
                  self#visit_pat env___var v___payload.subpat
                in
                let acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                self#plus acc___subpat acc___witness
            | PConstant v___payload ->
                let acc___lit = self#visit_literal env___var v___payload.lit in
                acc___lit
            | PBinding v___payload ->
                let acc___mut =
                  self#visit_mutability self#visit_F__mutable_variable env___var
                    v___payload.mut
                in
                let acc___mode =
                  self#visit_binding_mode env___var v___payload.mode
                in
                let acc___var =
                  self#visit_local_ident env___var v___payload.var
                in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___subpat =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_pat
                       self#visit_F__as_pattern)
                    env___var v___payload.subpat
                in
                self#plus
                  (self#plus
                     (self#plus (self#plus acc___mut acc___mode) acc___var)
                     acc___typ)
                  acc___subpat

        method visit_pat : 'env -> pat -> 'acc =
          fun env___var v___payload ->
            let acc___p = self#visit_pat' env___var v___payload.p in
            let acc___span = self#visit_span env___var v___payload.span in
            let acc___typ = self#visit_ty env___var v___payload.typ in
            self#plus (self#plus acc___p acc___span) acc___typ

        method visit_field_pat : 'env -> field_pat -> 'acc =
          fun env___var v___payload ->
            let acc___field =
              self#visit_global_ident env___var v___payload.field
            in
            let acc___pat = self#visit_pat env___var v___payload.pat in
            self#plus acc___field acc___pat

        method visit_expr' : 'env -> expr' -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | If v___payload ->
                let acc___cond = self#visit_expr env___var v___payload.cond in
                let acc___then_ = self#visit_expr env___var v___payload.then_ in
                let acc___else_ =
                  self#visit_option self#visit_expr env___var v___payload.else_
                in
                self#plus (self#plus acc___cond acc___then_) acc___else_
            | App v___payload ->
                let acc___f = self#visit_expr env___var v___payload.f in
                let acc___args =
                  self#visit_list self#visit_expr env___var v___payload.args
                in
                let acc___generic_args =
                  self#visit_list self#visit_generic_value env___var
                    v___payload.generic_args
                in
                let acc___bounds_impls =
                  self#visit_list self#visit_impl_expr env___var
                    v___payload.bounds_impls
                in
                let acc___impl =
                  self#visit_option self#visit_impl_expr env___var
                    v___payload.impl
                in
                self#plus
                  (self#plus
                     (self#plus
                        (self#plus acc___f acc___args)
                        acc___generic_args)
                     acc___bounds_impls)
                  acc___impl
            | Literal x0 ->
                let a0 = self#visit_literal env___var x0 in
                a0
            | Array x0 ->
                let a0 = self#visit_list self#visit_expr env___var x0 in
                a0
            | Construct v___payload ->
                let acc___constructor =
                  self#visit_global_ident env___var v___payload.constructor
                in
                let acc___is_record =
                  self#visit_bool env___var v___payload.is_record
                in
                let acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                let acc___fields =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_global_ident
                       self#visit_expr)
                    env___var v___payload.fields
                in
                let acc___base =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_expr
                       self#visit_F__construct_base)
                    env___var v___payload.base
                in
                self#plus
                  (self#plus
                     (self#plus
                        (self#plus acc___constructor acc___is_record)
                        acc___is_struct)
                     acc___fields)
                  acc___base
            | Match v___payload ->
                let acc___scrutinee =
                  self#visit_expr env___var v___payload.scrutinee
                in
                let acc___arms =
                  self#visit_list self#visit_arm env___var v___payload.arms
                in
                self#plus acc___scrutinee acc___arms
            | Let v___payload ->
                let acc___monadic =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_supported_monads
                       self#visit_F__monadic_binding)
                    env___var v___payload.monadic
                in
                let acc___lhs = self#visit_pat env___var v___payload.lhs in
                let acc___rhs = self#visit_expr env___var v___payload.rhs in
                let acc___body = self#visit_expr env___var v___payload.body in
                self#plus
                  (self#plus (self#plus acc___monadic acc___lhs) acc___rhs)
                  acc___body
            | Block (x0, x1) ->
                let a0 = self#visit_expr env___var x0 in
                let a1 = self#visit_F__block env___var x1 in
                self#plus a0 a1
            | LocalVar x0 ->
                let a0 = self#visit_local_ident env___var x0 in
                a0
            | GlobalVar x0 ->
                let a0 = self#visit_global_ident env___var x0 in
                a0
            | Ascription v___payload ->
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                self#plus acc___e acc___typ
            | MacroInvokation v___payload ->
                let acc___macro =
                  self#visit_global_ident env___var v___payload.macro
                in
                let acc___args = self#visit_string env___var v___payload.args in
                let acc___witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                self#plus (self#plus acc___macro acc___args) acc___witness
            | Assign v___payload ->
                let acc___lhs = self#visit_lhs env___var v___payload.lhs in
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___witness =
                  self#visit_F__mutable_variable env___var v___payload.witness
                in
                self#plus (self#plus acc___lhs acc___e) acc___witness
            | Loop v___payload ->
                let acc___body = self#visit_expr env___var v___payload.body in
                let acc___kind =
                  self#visit_loop_kind env___var v___payload.kind
                in
                let acc___state =
                  self#visit_option self#visit_loop_state env___var
                    v___payload.state
                in
                let acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let acc___witness =
                  self#visit_F__loop env___var v___payload.witness
                in
                self#plus
                  (self#plus
                     (self#plus (self#plus acc___body acc___kind) acc___state)
                     acc___label)
                  acc___witness
            | Break v___payload ->
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let acc___witness =
                  self#visit_prim___tuple_2 self#visit_F__break
                    self#visit_F__loop env___var v___payload.witness
                in
                self#plus (self#plus acc___e acc___label) acc___witness
            | Return v___payload ->
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___witness =
                  self#visit_F__early_exit env___var v___payload.witness
                in
                self#plus acc___e acc___witness
            | QuestionMark v___payload ->
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___return_typ =
                  self#visit_ty env___var v___payload.return_typ
                in
                let acc___witness =
                  self#visit_F__question_mark env___var v___payload.witness
                in
                self#plus (self#plus acc___e acc___return_typ) acc___witness
            | Continue v___payload ->
                let acc___e =
                  self#visit_option
                    (self#visit_prim___tuple_2 self#visit_F__state_passing_loop
                       self#visit_expr)
                    env___var v___payload.e
                in
                let acc___label =
                  self#visit_option self#visit_string env___var
                    v___payload.label
                in
                let acc___witness =
                  self#visit_prim___tuple_2 self#visit_F__continue
                    self#visit_F__loop env___var v___payload.witness
                in
                self#plus (self#plus acc___e acc___label) acc___witness
            | Borrow v___payload ->
                let acc___kind =
                  self#visit_borrow_kind env___var v___payload.kind
                in
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___witness =
                  self#visit_F__reference env___var v___payload.witness
                in
                self#plus (self#plus acc___kind acc___e) acc___witness
            | AddressOf v___payload ->
                let acc___mut =
                  self#visit_mutability self#visit_F__mutable_pointer env___var
                    v___payload.mut
                in
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___witness =
                  self#visit_F__raw_pointer env___var v___payload.witness
                in
                self#plus (self#plus acc___mut acc___e) acc___witness
            | Closure v___payload ->
                let acc___params =
                  self#visit_list self#visit_pat env___var v___payload.params
                in
                let acc___body = self#visit_expr env___var v___payload.body in
                let acc___captures =
                  self#visit_list self#visit_expr env___var v___payload.captures
                in
                self#plus (self#plus acc___params acc___body) acc___captures
            | EffectAction v___payload ->
                let acc___action =
                  self#visit_F__monadic_action env___var v___payload.action
                in
                let acc___argument =
                  self#visit_expr env___var v___payload.argument
                in
                self#plus acc___action acc___argument
            | Quote x0 ->
                let a0 = self#visit_quote env___var x0 in
                a0

        method visit_expr : 'env -> expr -> 'acc =
          fun env___var v___payload ->
            let acc___e = self#visit_expr' env___var v___payload.e in
            let acc___span = self#visit_span env___var v___payload.span in
            let acc___typ = self#visit_ty env___var v___payload.typ in
            self#plus (self#plus acc___e acc___span) acc___typ

        method visit_supported_monads : 'env -> supported_monads -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | MException x0 ->
                let a0 = self#visit_ty env___var x0 in
                a0
            | MResult x0 ->
                let a0 = self#visit_ty env___var x0 in
                a0
            | MOption -> self#zero

        method visit_loop_kind : 'env -> loop_kind -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | UnconditionalLoop -> self#zero
            | WhileLoop v___payload ->
                let acc___condition =
                  self#visit_expr env___var v___payload.condition
                in
                let acc___witness =
                  self#visit_F__while_loop env___var v___payload.witness
                in
                self#plus acc___condition acc___witness
            | ForLoop v___payload ->
                let acc___pat = self#visit_pat env___var v___payload.pat in
                let acc___it = self#visit_expr env___var v___payload.it in
                let acc___witness =
                  self#visit_F__for_loop env___var v___payload.witness
                in
                self#plus (self#plus acc___pat acc___it) acc___witness
            | ForIndexLoop v___payload ->
                let acc___start = self#visit_expr env___var v___payload.start in
                let acc___end_ = self#visit_expr env___var v___payload.end_ in
                let acc___var =
                  self#visit_local_ident env___var v___payload.var
                in
                let acc___var_typ =
                  self#visit_ty env___var v___payload.var_typ
                in
                let acc___witness =
                  self#visit_F__for_index_loop env___var v___payload.witness
                in
                self#plus
                  (self#plus
                     (self#plus (self#plus acc___start acc___end_) acc___var)
                     acc___var_typ)
                  acc___witness

        method visit_loop_state : 'env -> loop_state -> 'acc =
          fun env___var v___payload ->
            let acc___init = self#visit_expr env___var v___payload.init in
            let acc___bpat = self#visit_pat env___var v___payload.bpat in
            let acc___witness =
              self#visit_F__state_passing_loop env___var v___payload.witness
            in
            self#plus (self#plus acc___init acc___bpat) acc___witness

        method visit_lhs : 'env -> lhs -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | LhsLocalVar v___payload ->
                let acc___var =
                  self#visit_Local_ident__t env___var v___payload.var
                in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                self#plus acc___var acc___typ
            | LhsArbitraryExpr v___payload ->
                let acc___e = self#visit_expr env___var v___payload.e in
                let acc___witness =
                  self#visit_F__arbitrary_lhs env___var v___payload.witness
                in
                self#plus acc___e acc___witness
            | LhsFieldAccessor v___payload ->
                let acc___e = self#visit_lhs env___var v___payload.e in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___field =
                  self#visit_global_ident env___var v___payload.field
                in
                let acc___witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                self#plus
                  (self#plus (self#plus acc___e acc___typ) acc___field)
                  acc___witness
            | LhsArrayAccessor v___payload ->
                let acc___e = self#visit_lhs env___var v___payload.e in
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___index = self#visit_expr env___var v___payload.index in
                let acc___witness =
                  self#visit_F__nontrivial_lhs env___var v___payload.witness
                in
                self#plus
                  (self#plus (self#plus acc___e acc___typ) acc___index)
                  acc___witness

        method visit_arm' : 'env -> arm' -> 'acc =
          fun env___var v___payload ->
            let acc___arm_pat = self#visit_pat env___var v___payload.arm_pat in
            let acc___body = self#visit_expr env___var v___payload.body in
            self#plus acc___arm_pat acc___body

        method visit_arm : 'env -> arm -> 'acc =
          fun env___var v___payload ->
            let acc___arm = self#visit_arm' env___var v___payload.arm in
            let acc___span = self#visit_span env___var v___payload.span in
            self#plus acc___arm acc___span

        method visit_generic_param : 'env -> generic_param -> 'acc =
          fun env___var v___payload ->
            let acc___ident =
              self#visit_local_ident env___var v___payload.ident
            in
            let acc___span = self#visit_span env___var v___payload.span in
            let acc___attrs = self#visit_attrs env___var v___payload.attrs in
            let acc___kind =
              self#visit_generic_param_kind env___var v___payload.kind
            in
            self#plus
              (self#plus (self#plus acc___ident acc___span) acc___attrs)
              acc___kind

        method visit_generic_param_kind : 'env -> generic_param_kind -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GPLifetime v___payload ->
                let acc___witness =
                  self#visit_F__lifetime env___var v___payload.witness
                in
                acc___witness
            | GPType v___payload ->
                let acc___default =
                  self#visit_option self#visit_ty env___var v___payload.default
                in
                acc___default
            | GPConst v___payload ->
                let acc___typ = self#visit_ty env___var v___payload.typ in
                acc___typ

        method visit_generic_constraint : 'env -> generic_constraint -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | GCLifetime (x0, x1) ->
                let a0 = self#visit_todo env___var x0 in
                let a1 = self#visit_F__lifetime env___var x1 in
                self#plus a0 a1
            | GCType x0 ->
                let a0 = self#visit_impl_ident env___var x0 in
                a0

        method visit_param : 'env -> param -> 'acc =
          fun env___var v___payload ->
            let acc___pat = self#visit_pat env___var v___payload.pat in
            let acc___typ = self#visit_ty env___var v___payload.typ in
            let acc___typ_span =
              self#visit_option self#visit_span env___var v___payload.typ_span
            in
            let acc___attrs = self#visit_attrs env___var v___payload.attrs in
            self#plus
              (self#plus (self#plus acc___pat acc___typ) acc___typ_span)
              acc___attrs

        method visit_generics : 'env -> generics -> 'acc =
          fun env___var v___payload ->
            let acc___params =
              self#visit_list self#visit_generic_param env___var
                v___payload.params
            in
            let acc___constraints =
              self#visit_list self#visit_generic_constraint env___var
                v___payload.constraints
            in
            self#plus acc___params acc___constraints

        method visit_variant : 'env -> variant -> 'acc =
          fun env___var v___payload ->
            let acc___name =
              self#visit_concrete_ident env___var v___payload.name
            in
            let acc___arguments =
              self#visit_list
                (self#visit_prim___tuple_3 self#visit_concrete_ident
                   self#visit_ty self#visit_attrs)
                env___var v___payload.arguments
            in
            let acc___is_record =
              self#visit_bool env___var v___payload.is_record
            in
            let acc___attrs = self#visit_attrs env___var v___payload.attrs in
            self#plus
              (self#plus (self#plus acc___name acc___arguments) acc___is_record)
              acc___attrs

        method visit_item' : 'env -> item' -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | Fn v___payload ->
                let acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let acc___body = self#visit_expr env___var v___payload.body in
                let acc___params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                self#plus
                  (self#plus (self#plus acc___name acc___generics) acc___body)
                  acc___params
            | TyAlias v___payload ->
                let acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let acc___ty = self#visit_ty env___var v___payload.ty in
                self#plus (self#plus acc___name acc___generics) acc___ty
            | Type v___payload ->
                let acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let acc___variants =
                  self#visit_list self#visit_variant env___var
                    v___payload.variants
                in
                let acc___is_struct =
                  self#visit_bool env___var v___payload.is_struct
                in
                self#plus
                  (self#plus
                     (self#plus acc___name acc___generics)
                     acc___variants)
                  acc___is_struct
            | IMacroInvokation v___payload ->
                let acc___macro =
                  self#visit_concrete_ident env___var v___payload.macro
                in
                let acc___argument =
                  self#visit_string env___var v___payload.argument
                in
                let acc___span = self#visit_span env___var v___payload.span in
                let acc___witness =
                  self#visit_F__macro env___var v___payload.witness
                in
                self#plus
                  (self#plus (self#plus acc___macro acc___argument) acc___span)
                  acc___witness
            | Trait v___payload ->
                let acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let acc___items =
                  self#visit_list self#visit_trait_item env___var
                    v___payload.items
                in
                self#plus (self#plus acc___name acc___generics) acc___items
            | Impl v___payload ->
                let acc___generics =
                  self#visit_generics env___var v___payload.generics
                in
                let acc___self_ty =
                  self#visit_ty env___var v___payload.self_ty
                in
                let acc___of_trait =
                  self#visit_prim___tuple_2 self#visit_global_ident
                    (self#visit_list self#visit_generic_value)
                    env___var v___payload.of_trait
                in
                let acc___items =
                  self#visit_list self#visit_impl_item env___var
                    v___payload.items
                in
                let acc___parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                self#plus
                  (self#plus
                     (self#plus
                        (self#plus acc___generics acc___self_ty)
                        acc___of_trait)
                     acc___items)
                  acc___parent_bounds
            | Alias v___payload ->
                let acc___name =
                  self#visit_concrete_ident env___var v___payload.name
                in
                let acc___item =
                  self#visit_concrete_ident env___var v___payload.item
                in
                self#plus acc___name acc___item
            | Use v___payload ->
                let acc___path =
                  self#visit_list self#visit_string env___var v___payload.path
                in
                let acc___is_external =
                  self#visit_bool env___var v___payload.is_external
                in
                let acc___rename =
                  self#visit_option self#visit_string env___var
                    v___payload.rename
                in
                self#plus (self#plus acc___path acc___is_external) acc___rename
            | Quote x0 ->
                let a0 = self#visit_quote env___var x0 in
                a0
            | HaxError x0 ->
                let a0 = self#visit_string env___var x0 in
                a0
            | NotImplementedYet -> self#zero

        method visit_item : 'env -> item -> 'acc =
          fun env___var v___payload ->
            let acc___v = self#visit_item' env___var v___payload.v in
            let acc___span = self#visit_span env___var v___payload.span in
            let acc___ident =
              self#visit_concrete_ident env___var v___payload.ident
            in
            let acc___attrs = self#visit_attrs env___var v___payload.attrs in
            self#plus
              (self#plus (self#plus acc___v acc___span) acc___ident)
              acc___attrs

        method visit_impl_item' : 'env -> impl_item' -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | IIType v___payload ->
                let acc___typ = self#visit_ty env___var v___payload.typ in
                let acc___parent_bounds =
                  self#visit_list
                    (self#visit_prim___tuple_2 self#visit_impl_expr
                       self#visit_impl_ident)
                    env___var v___payload.parent_bounds
                in
                self#plus acc___typ acc___parent_bounds
            | IIFn v___payload ->
                let acc___body = self#visit_expr env___var v___payload.body in
                let acc___params =
                  self#visit_list self#visit_param env___var v___payload.params
                in
                self#plus acc___body acc___params

        method visit_impl_item : 'env -> impl_item -> 'acc =
          fun env___var v___payload ->
            let acc___ii_span = self#visit_span env___var v___payload.ii_span in
            let acc___ii_generics =
              self#visit_generics env___var v___payload.ii_generics
            in
            let acc___ii_v = self#visit_impl_item' env___var v___payload.ii_v in
            let acc___ii_ident =
              self#visit_concrete_ident env___var v___payload.ii_ident
            in
            let acc___ii_attrs =
              self#visit_attrs env___var v___payload.ii_attrs
            in
            self#plus
              (self#plus
                 (self#plus
                    (self#plus acc___ii_span acc___ii_generics)
                    acc___ii_v)
                 acc___ii_ident)
              acc___ii_attrs

        method visit_trait_item' : 'env -> trait_item' -> 'acc =
          fun env___var v___payload ->
            match v___payload with
            | TIType x0 ->
                let a0 = self#visit_list self#visit_impl_ident env___var x0 in
                a0
            | TIFn x0 ->
                let a0 = self#visit_ty env___var x0 in
                a0

        method visit_trait_item : 'env -> trait_item -> 'acc =
          fun env___var v___payload ->
            let acc___ti_span = self#visit_span env___var v___payload.ti_span in
            let acc___ti_generics =
              self#visit_generics env___var v___payload.ti_generics
            in
            let acc___ti_v =
              self#visit_trait_item' env___var v___payload.ti_v
            in
            let acc___ti_ident =
              self#visit_concrete_ident env___var v___payload.ti_ident
            in
            let acc___ti_attrs =
              self#visit_attrs env___var v___payload.ti_attrs
            in
            self#plus
              (self#plus
                 (self#plus
                    (self#plus acc___ti_span acc___ti_generics)
                    acc___ti_v)
                 acc___ti_ident)
              acc___ti_attrs

        method visit_modul : 'env -> modul -> 'acc =
          fun env___var v___payload ->
            self#visit_list self#visit_item env___var v___payload

        method visit_list : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a list -> 'acc
            =
          fun v env this ->
            Base.List.fold ~init:self#zero
              ~f:(fun acc -> v env >> self#plus acc)
              this
      end
  end
