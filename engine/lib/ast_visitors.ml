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
        method visit_literal (env : 'env) (this : literal) : literal =
          match this with
          | String x0 ->
              let x0 = self#visit_string env x0 in
              String x0
          | Char x0 ->
              let x0 = self#visit_char env x0 in
              Char x0
          | Int record_payload ->
              let value = self#visit_string env record_payload.value in
              let negative = self#visit_bool env record_payload.negative in
              let kind = self#visit_int_kind env record_payload.kind in
              Int { value; negative; kind }
          | Float record_payload ->
              let value = self#visit_string env record_payload.value in
              let negative = self#visit_bool env record_payload.negative in
              let kind = self#visit_float_kind env record_payload.kind in
              Float { value; negative; kind }
          | Bool x0 ->
              let x0 = self#visit_bool env x0 in
              Bool x0

        method visit_attr_kind (env : 'env) (this : attr_kind) : attr_kind =
          match this with
          | Tool record_payload ->
              let path = self#visit_string env record_payload.path in
              let tokens = self#visit_string env record_payload.tokens in
              Tool { path; tokens }
          | DocComment record_payload ->
              let kind = self#visit_doc_comment_kind env record_payload.kind in
              let body = self#visit_string env record_payload.body in
              DocComment { kind; body }

        method visit_attr (env : 'env) (this : attr) : attr =
          let kind = self#visit_attr_kind env this.kind in
          let span = self#visit_span env this.span in
          let out : attr = { kind; span } in
          out

        method visit_doc_comment_kind (env : 'env) (this : doc_comment_kind)
            : doc_comment_kind =
          match this with DCKLine -> DCKLine | DCKBlock -> DCKBlock

        method visit_borrow_kind (env : 'env) (this : borrow_kind) : borrow_kind
            =
          match this with
          | Shared -> Shared
          | Unique -> Unique
          | Mut x0 ->
              let x0 = self#visit_feature_mutable_reference env x0 in
              Mut x0

        method visit_binding_mode (env : 'env) (this : binding_mode)
            : binding_mode =
          match this with
          | ByValue -> ByValue
          | ByRef (x0, x1) ->
              let x0 = self#visit_borrow_kind env x0 in
              let x1 = self#visit_feature_reference env x1 in
              ByRef (x0, x1)

        method visit_ty (env : 'env) (this : ty) : ty =
          match this with
          | TBool -> TBool
          | TChar -> TChar
          | TInt x0 ->
              let x0 = self#visit_int_kind env x0 in
              TInt x0
          | TFloat x0 ->
              let x0 = self#visit_float_kind env x0 in
              TFloat x0
          | TStr -> TStr
          | TApp record_payload ->
              let ident = self#visit_global_ident env record_payload.ident in
              let args =
                self#visit_list self#visit_generic_value env record_payload.args
              in
              TApp { ident; args }
          | TArray record_payload ->
              let typ = self#visit_ty env record_payload.typ in
              let length = self#visit_expr env record_payload.length in
              TArray { typ; length }
          | TSlice record_payload ->
              let witness =
                self#visit_feature_slice env record_payload.witness
              in
              let ty = self#visit_ty env record_payload.ty in
              TSlice { witness; ty }
          | TRawPointer record_payload ->
              let witness =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              TRawPointer { witness }
          | TRef record_payload ->
              let witness =
                self#visit_feature_reference env record_payload.witness
              in
              let region = self#visit_todo env record_payload.region in
              let typ = self#visit_ty env record_payload.typ in
              let mut =
                self#visit_mutability self#visit_feature_mutable_reference env
                  record_payload.mut
              in
              TRef { witness; region; typ; mut }
          | TParam x0 ->
              let x0 = self#visit_local_ident env x0 in
              TParam x0
          | TArrow (x0, x1) ->
              let x0 = self#visit_list self#visit_ty env x0 in
              let x1 = self#visit_ty env x1 in
              TArrow (x0, x1)
          | TAssociatedType record_payload ->
              let impl = self#visit_impl_expr env record_payload.impl in
              let item = self#visit_concrete_ident env record_payload.item in
              TAssociatedType { impl; item }
          | TOpaque x0 ->
              let x0 = self#visit_concrete_ident env x0 in
              TOpaque x0

        method visit_generic_value (env : 'env) (this : generic_value)
            : generic_value =
          match this with
          | GLifetime record_payload ->
              let lt = self#visit_todo env record_payload.lt in
              let witness =
                self#visit_feature_lifetime env record_payload.witness
              in
              GLifetime { lt; witness }
          | GType x0 ->
              let x0 = self#visit_ty env x0 in
              GType x0
          | GConst x0 ->
              let x0 = self#visit_expr env x0 in
              GConst x0

        method visit_impl_expr (env : 'env) (this : impl_expr) : impl_expr =
          match this with
          | Self -> Self
          | Concrete x0 ->
              let x0 = self#visit_trait_goal env x0 in
              Concrete x0
          | LocalBound record_payload ->
              let id = self#visit_string env record_payload.id in
              LocalBound { id }
          | Parent record_payload ->
              let impl = self#visit_impl_expr env record_payload.impl in
              let ident = self#visit_impl_ident env record_payload.ident in
              Parent { impl; ident }
          | Projection record_payload ->
              let impl = self#visit_impl_expr env record_payload.impl in
              let ident = self#visit_impl_ident env record_payload.ident in
              let item = self#visit_concrete_ident env record_payload.item in
              Projection { impl; ident; item }
          | ImplApp record_payload ->
              let impl = self#visit_impl_expr env record_payload.impl in
              let args =
                self#visit_list self#visit_impl_expr env record_payload.args
              in
              ImplApp { impl; args }
          | Dyn x0 ->
              let x0 = self#visit_trait_goal env x0 in
              Dyn x0
          | Builtin x0 ->
              let x0 = self#visit_trait_goal env x0 in
              Builtin x0
          | FnPointer x0 ->
              let x0 = self#visit_ty env x0 in
              FnPointer x0
          | ClosureIE x0 ->
              let x0 = self#visit_todo env x0 in
              ClosureIE x0

        method visit_trait_goal (env : 'env) (this : trait_goal) : trait_goal =
          let trait = self#visit_concrete_ident env this.trait in
          let args = self#visit_list self#visit_generic_value env this.args in
          let out : trait_goal = { trait; args } in
          out

        method visit_impl_ident (env : 'env) (this : impl_ident) : impl_ident =
          let goal = self#visit_trait_goal env this.goal in
          let out : impl_ident = { goal; name = this.name } in
          out

        method visit_pat' (env : 'env) (this : pat') : pat' =
          match this with
          | PWild -> PWild
          | PAscription record_payload ->
              let typ = self#visit_ty env record_payload.typ in
              let typ_span = self#visit_span env record_payload.typ_span in
              let pat = self#visit_pat env record_payload.pat in
              PAscription { typ; typ_span; pat }
          | PConstruct record_payload ->
              let name = self#visit_global_ident env record_payload.name in
              let args =
                self#visit_list self#visit_field_pat env record_payload.args
              in
              let is_record = self#visit_bool env record_payload.is_record in
              let is_struct = self#visit_bool env record_payload.is_struct in
              PConstruct { name; args; is_record; is_struct }
          | POr record_payload ->
              let subpats =
                self#visit_list self#visit_pat env record_payload.subpats
              in
              POr { subpats }
          | PArray record_payload ->
              let args =
                self#visit_list self#visit_pat env record_payload.args
              in
              PArray { args }
          | PDeref record_payload ->
              let subpat = self#visit_pat env record_payload.subpat in
              let witness =
                self#visit_feature_reference env record_payload.witness
              in
              PDeref { subpat; witness }
          | PConstant record_payload ->
              let lit = self#visit_literal env record_payload.lit in
              PConstant { lit }
          | PBinding record_payload ->
              let mut =
                self#visit_mutability self#visit_feature_mutable_variable env
                  record_payload.mut
              in
              let mode = self#visit_binding_mode env record_payload.mode in
              let var = self#visit_local_ident env record_payload.var in
              let typ = self#visit_ty env record_payload.typ in
              let subpat =
                self#visit_option
                  (self#visit_tuple2 self#visit_pat
                     self#visit_feature_as_pattern)
                  env record_payload.subpat
              in
              PBinding { mut; mode; var; typ; subpat }

        method visit_pat (env : 'env) (this : pat) : pat =
          let p = self#visit_pat' env this.p in
          let span = self#visit_span env this.span in
          let typ = self#visit_ty env this.typ in
          let out : pat = { p; span; typ } in
          out

        method visit_field_pat (env : 'env) (this : field_pat) : field_pat =
          let field = self#visit_global_ident env this.field in
          let pat = self#visit_pat env this.pat in
          let out : field_pat = { field; pat } in
          out

        method visit_expr' (env : 'env) (this : expr') : expr' =
          match this with
          | If record_payload ->
              let cond = self#visit_expr env record_payload.cond in
              let then_ = self#visit_expr env record_payload.then_ in
              let else_ =
                self#visit_option self#visit_expr env record_payload.else_
              in
              If { cond; then_; else_ }
          | App record_payload ->
              let f = self#visit_expr env record_payload.f in
              let args =
                self#visit_list self#visit_expr env record_payload.args
              in
              let generic_args =
                self#visit_list self#visit_generic_value env
                  record_payload.generic_args
              in
              let impl =
                self#visit_option self#visit_impl_expr env record_payload.impl
              in
              App { f; args; generic_args; impl }
          | Literal x0 ->
              let x0 = self#visit_literal env x0 in
              Literal x0
          | Array x0 ->
              let x0 = self#visit_list self#visit_expr env x0 in
              Array x0
          | Construct record_payload ->
              let constructor =
                self#visit_global_ident env record_payload.constructor
              in
              let is_record = self#visit_bool env record_payload.is_record in
              let is_struct = self#visit_bool env record_payload.is_struct in
              let fields =
                self#visit_list
                  (self#visit_tuple2 self#visit_global_ident self#visit_expr)
                  env record_payload.fields
              in
              let base =
                self#visit_option
                  (self#visit_tuple2 self#visit_expr
                     self#visit_feature_construct_base)
                  env record_payload.base
              in
              Construct { constructor; is_record; is_struct; fields; base }
          | Match record_payload ->
              let scrutinee = self#visit_expr env record_payload.scrutinee in
              let arms =
                self#visit_list self#visit_arm env record_payload.arms
              in
              Match { scrutinee; arms }
          | Let record_payload ->
              let monadic =
                self#visit_option
                  (self#visit_tuple2 self#visit_supported_monads
                     self#visit_feature_monadic_binding)
                  env record_payload.monadic
              in
              let lhs = self#visit_pat env record_payload.lhs in
              let rhs = self#visit_expr env record_payload.rhs in
              let body = self#visit_expr env record_payload.body in
              Let { monadic; lhs; rhs; body }
          | Block (x0, x1) ->
              let x0 = self#visit_expr env x0 in
              let x1 = self#visit_feature_block env x1 in
              Block (x0, x1)
          | LocalVar x0 ->
              let x0 = self#visit_local_ident env x0 in
              LocalVar x0
          | GlobalVar x0 ->
              let x0 = self#visit_global_ident env x0 in
              GlobalVar x0
          | Ascription record_payload ->
              let e = self#visit_expr env record_payload.e in
              let typ = self#visit_ty env record_payload.typ in
              Ascription { e; typ }
          | MacroInvokation record_payload ->
              let macro = self#visit_global_ident env record_payload.macro in
              let args = self#visit_string env record_payload.args in
              let witness =
                self#visit_feature_macro env record_payload.witness
              in
              MacroInvokation { macro; args; witness }
          | Assign record_payload ->
              let lhs = self#visit_lhs env record_payload.lhs in
              let e = self#visit_expr env record_payload.e in
              let witness =
                self#visit_feature_mutable_variable env record_payload.witness
              in
              Assign { lhs; e; witness }
          | Loop record_payload ->
              let body = self#visit_expr env record_payload.body in
              let kind = self#visit_loop_kind env record_payload.kind in
              let state =
                self#visit_option self#visit_loop_state env record_payload.state
              in
              let label =
                self#visit_option self#visit_string env record_payload.label
              in
              let witness =
                self#visit_feature_loop env record_payload.witness
              in
              Loop { body; kind; state; label; witness }
          | Break record_payload ->
              let e = self#visit_expr env record_payload.e in
              let label =
                self#visit_option self#visit_string env record_payload.label
              in
              let witness =
                self#visit_tuple2 self#visit_feature_break
                  self#visit_feature_loop env record_payload.witness
              in
              Break { e; label; witness }
          | Return record_payload ->
              let e = self#visit_expr env record_payload.e in
              let witness =
                self#visit_feature_early_exit env record_payload.witness
              in
              Return { e; witness }
          | QuestionMark record_payload ->
              let e = self#visit_expr env record_payload.e in
              let return_typ = self#visit_ty env record_payload.return_typ in
              let witness =
                self#visit_feature_question_mark env record_payload.witness
              in
              QuestionMark { e; return_typ; witness }
          | Continue record_payload ->
              let e =
                self#visit_option
                  (self#visit_tuple2 self#visit_feature_state_passing_loop
                     self#visit_expr)
                  env record_payload.e
              in
              let label =
                self#visit_option self#visit_string env record_payload.label
              in
              let witness =
                self#visit_tuple2 self#visit_feature_continue
                  self#visit_feature_loop env record_payload.witness
              in
              Continue { e; label; witness }
          | Borrow record_payload ->
              let kind = self#visit_borrow_kind env record_payload.kind in
              let e = self#visit_expr env record_payload.e in
              let witness =
                self#visit_feature_reference env record_payload.witness
              in
              Borrow { kind; e; witness }
          | AddressOf record_payload ->
              let mut =
                self#visit_mutability self#visit_feature_mutable_pointer env
                  record_payload.mut
              in
              let e = self#visit_expr env record_payload.e in
              let witness =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              AddressOf { mut; e; witness }
          | Closure record_payload ->
              let params =
                self#visit_list self#visit_pat env record_payload.params
              in
              let body = self#visit_expr env record_payload.body in
              let captures =
                self#visit_list self#visit_expr env record_payload.captures
              in
              Closure { params; body; captures }
          | EffectAction record_payload ->
              let action =
                self#visit_feature_monadic_action env record_payload.action
              in
              let argument = self#visit_expr env record_payload.argument in
              EffectAction { action; argument }
          | Quote quote -> Quote (self#visit_quote env quote)

        method visit_expr (env : 'env) (this : expr) : expr =
          let e = self#visit_expr' env this.e in
          let span = self#visit_span env this.span in
          let typ = self#visit_ty env this.typ in
          let out : expr = { e; span; typ } in
          out

        method visit_quote (env : 'env) ({ contents; witness } : quote) : quote
            =
          let contents =
            self#visit_list
              (fun env -> function
                | `Verbatim code -> `Verbatim code
                | `Expr e -> `Expr (self#visit_expr env e)
                | `Pat p -> `Pat (self#visit_pat env p))
              env contents
          in
          let witness = self#visit_feature_quote env witness in
          { contents; witness }

        method visit_supported_monads (env : 'env) (this : supported_monads)
            : supported_monads =
          match this with
          | MException x0 ->
              let x0 = self#visit_ty env x0 in
              MException x0
          | MResult x0 ->
              let x0 = self#visit_ty env x0 in
              MResult x0
          | MOption -> MOption

        method visit_loop_kind (env : 'env) (this : loop_kind) : loop_kind =
          match this with
          | UnconditionalLoop -> UnconditionalLoop
          | WhileLoop record_payload ->
              let condition = self#visit_expr env record_payload.condition in
              let witness =
                self#visit_feature_while_loop env record_payload.witness
              in
              WhileLoop { condition; witness }
          | ForLoop record_payload ->
              let pat = self#visit_pat env record_payload.pat in
              let it = self#visit_expr env record_payload.it in
              let witness =
                self#visit_feature_for_loop env record_payload.witness
              in
              ForLoop { pat; it; witness }
          | ForIndexLoop record_payload ->
              let start = self#visit_expr env record_payload.start in
              let end_ = self#visit_expr env record_payload.end_ in
              let var = self#visit_local_ident env record_payload.var in
              let var_typ = self#visit_ty env record_payload.var_typ in
              let witness =
                self#visit_feature_for_index_loop env record_payload.witness
              in
              ForIndexLoop { start; end_; var; var_typ; witness }

        method visit_loop_state (env : 'env) (this : loop_state) : loop_state =
          let init = self#visit_expr env this.init in
          let bpat = self#visit_pat env this.bpat in
          let witness =
            self#visit_feature_state_passing_loop env this.witness
          in
          let out : loop_state = { init; bpat; witness } in
          out

        method visit_lhs (env : 'env) (this : lhs) : lhs =
          match this with
          | LhsLocalVar record_payload ->
              let var = self#visit_local_ident env record_payload.var in
              let typ = self#visit_ty env record_payload.typ in
              LhsLocalVar { var; typ }
          | LhsArbitraryExpr record_payload ->
              let e = self#visit_expr env record_payload.e in
              let witness =
                self#visit_feature_arbitrary_lhs env record_payload.witness
              in
              LhsArbitraryExpr { e; witness }
          | LhsFieldAccessor record_payload ->
              let e = self#visit_lhs env record_payload.e in
              let typ = self#visit_ty env record_payload.typ in
              let field = self#visit_global_ident env record_payload.field in
              let witness =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              LhsFieldAccessor { e; typ; field; witness }
          | LhsArrayAccessor record_payload ->
              let e = self#visit_lhs env record_payload.e in
              let typ = self#visit_ty env record_payload.typ in
              let index = self#visit_expr env record_payload.index in
              let witness =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              LhsArrayAccessor { e; typ; index; witness }

        method visit_arm' (env : 'env) (this : arm') : arm' =
          let arm_pat = self#visit_pat env this.arm_pat in
          let body = self#visit_expr env this.body in
          let out : arm' = { arm_pat; body } in
          out

        method visit_arm (env : 'env) (this : arm) : arm =
          let arm = self#visit_arm' env this.arm in
          let span = self#visit_span env this.span in
          let out : arm = { arm; span } in
          out

        method visit_generic_param (env : 'env) (this : generic_param)
            : generic_param =
          let ident = self#visit_local_ident env this.ident in
          let span = self#visit_span env this.span in
          let attrs = self#visit_list self#visit_attr env this.attrs in
          let kind = self#visit_generic_param_kind env this.kind in
          let out : generic_param = { ident; span; attrs; kind } in
          out

        method visit_generic_param_kind (env : 'env) (this : generic_param_kind)
            : generic_param_kind =
          match this with
          | GPLifetime record_payload ->
              let witness =
                self#visit_feature_lifetime env record_payload.witness
              in
              GPLifetime { witness }
          | GPType record_payload ->
              let default =
                self#visit_option self#visit_ty env record_payload.default
              in
              GPType { default }
          | GPConst record_payload ->
              let typ = self#visit_ty env record_payload.typ in
              GPConst { typ }

        method visit_generic_constraint (env : 'env) (this : generic_constraint)
            : generic_constraint =
          match this with
          | GCLifetime (x0, x1) ->
              let x0 = self#visit_todo env x0 in
              let x1 = self#visit_feature_lifetime env x1 in
              GCLifetime (x0, x1)
          | GCType x0 ->
              let x0 = self#visit_impl_ident env x0 in
              GCType x0

        method visit_param (env : 'env) (this : param) : param =
          let pat = self#visit_pat env this.pat in
          let typ = self#visit_ty env this.typ in
          let typ_span = self#visit_option self#visit_span env this.typ_span in
          let attrs = self#visit_list self#visit_attr env this.attrs in
          let out : param = { pat; typ; typ_span; attrs } in
          out

        method visit_generics (env : 'env) (this : generics) : generics =
          let params =
            self#visit_list self#visit_generic_param env this.params
          in
          let constraints =
            self#visit_list self#visit_generic_constraint env this.constraints
          in
          let out : generics = { params; constraints } in
          out

        method visit_variant (env : 'env) (this : variant) : variant =
          let name = self#visit_concrete_ident env this.name in
          let arguments =
            self#visit_list
              (self#visit_tuple3 self#visit_concrete_ident self#visit_ty
                 (self#visit_list self#visit_attr))
              env this.arguments
          in
          let is_record = self#visit_bool env this.is_record in
          let attrs = self#visit_list self#visit_attr env this.attrs in
          let out : variant = { name; arguments; is_record; attrs } in
          out

        method visit_item' (env : 'env) (this : item') : item' =
          match this with
          | Fn record_payload ->
              let name = self#visit_concrete_ident env record_payload.name in
              let generics = self#visit_generics env record_payload.generics in
              let body = self#visit_expr env record_payload.body in
              let params =
                self#visit_list self#visit_param env record_payload.params
              in
              Fn { name; generics; body; params }
          | TyAlias record_payload ->
              let name = self#visit_concrete_ident env record_payload.name in
              let generics = self#visit_generics env record_payload.generics in
              let ty = self#visit_ty env record_payload.ty in
              TyAlias { name; generics; ty }
          | Type record_payload ->
              let name = self#visit_concrete_ident env record_payload.name in
              let generics = self#visit_generics env record_payload.generics in
              let variants =
                self#visit_list self#visit_variant env record_payload.variants
              in
              let is_struct = self#visit_bool env record_payload.is_struct in
              Type { name; generics; variants; is_struct }
          | IMacroInvokation record_payload ->
              let macro = self#visit_concrete_ident env record_payload.macro in
              let argument = self#visit_string env record_payload.argument in
              let span = self#visit_span env record_payload.span in
              let witness =
                self#visit_feature_macro env record_payload.witness
              in
              IMacroInvokation { macro; argument; span; witness }
          | Trait record_payload ->
              let name = self#visit_concrete_ident env record_payload.name in
              let generics = self#visit_generics env record_payload.generics in
              let items =
                self#visit_list self#visit_trait_item env record_payload.items
              in
              Trait { name; generics; items }
          | Impl record_payload ->
              let generics = self#visit_generics env record_payload.generics in
              let self_ty = self#visit_ty env record_payload.self_ty in
              let of_trait =
                self#visit_tuple2 self#visit_global_ident
                  (self#visit_list self#visit_generic_value)
                  env record_payload.of_trait
              in
              let items =
                self#visit_list self#visit_impl_item env record_payload.items
              in
              let parent_bounds =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              Impl { generics; self_ty; of_trait; items; parent_bounds }
          | Alias record_payload ->
              let name = self#visit_concrete_ident env record_payload.name in
              let item = self#visit_concrete_ident env record_payload.item in
              Alias { name; item }
          | Use record_payload ->
              let path =
                self#visit_list self#visit_string env record_payload.path
              in
              let is_external =
                self#visit_bool env record_payload.is_external
              in
              let rename =
                self#visit_option self#visit_string env record_payload.rename
              in
              Use { path; is_external; rename }
          | Quote quote -> Quote (self#visit_quote env quote)
          | HaxError x0 ->
              let x0 = self#visit_string env x0 in
              HaxError x0
          | NotImplementedYet -> NotImplementedYet

        method visit_item (env : 'env) (this : item) : item =
          let v = self#visit_item' env this.v in
          let span = self#visit_span env this.span in
          let ident = self#visit_concrete_ident env this.ident in
          let attrs = self#visit_list self#visit_attr env this.attrs in
          let out : item = { v; span; ident; attrs } in
          out

        method visit_impl_item' (env : 'env) (this : impl_item') : impl_item' =
          match this with
          | IIType record_payload ->
              let typ = self#visit_ty env record_payload.typ in
              let parent_bounds =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              IIType { typ; parent_bounds }
          | IIFn record_payload ->
              let body = self#visit_expr env record_payload.body in
              let params =
                self#visit_list self#visit_param env record_payload.params
              in
              IIFn { body; params }

        method visit_impl_item (env : 'env) (this : impl_item) : impl_item =
          let ii_span = self#visit_span env this.ii_span in
          let ii_generics = self#visit_generics env this.ii_generics in
          let ii_v = self#visit_impl_item' env this.ii_v in
          let ii_ident = self#visit_concrete_ident env this.ii_ident in
          let ii_attrs = self#visit_list self#visit_attr env this.ii_attrs in
          let out : impl_item =
            { ii_span; ii_generics; ii_v; ii_ident; ii_attrs }
          in
          out

        method visit_trait_item' (env : 'env) (this : trait_item') : trait_item'
            =
          match this with
          | TIType x0 ->
              let x0 = self#visit_list self#visit_impl_ident env x0 in
              TIType x0
          | TIFn x0 ->
              let x0 = self#visit_ty env x0 in
              TIFn x0

        method visit_trait_item (env : 'env) (this : trait_item) : trait_item =
          let ti_span = self#visit_span env this.ti_span in
          let ti_generics = self#visit_generics env this.ti_generics in
          let ti_v = self#visit_trait_item' env this.ti_v in
          let ti_ident = self#visit_concrete_ident env this.ti_ident in
          let ti_attrs = self#visit_list self#visit_attr env this.ti_attrs in
          let out : trait_item =
            { ti_span; ti_generics; ti_v; ti_ident; ti_attrs }
          in
          out

        method visit_list : 'a. ('env -> 'a -> 'a) -> 'env -> 'a list -> 'a list
            =
          fun v env -> Base.List.map ~f:(v env)

        method visit_option
            : 'a. ('env -> 'a -> 'a) -> 'env -> 'a option -> 'a option =
          fun v env this ->
            match this with None -> None | Some x -> Some (v env x)

        method visit_tuple2
            : 'a 'b.
              ('env -> 'a -> 'a) ->
              ('env -> 'b -> 'b) ->
              'env ->
              'a * 'b ->
              'a * 'b =
          fun vx vy env (x, y) ->
            let x = vx env x in
            let y = vy env y in
            (x, y)

        method visit_tuple3
            : 'a 'b 'c.
              ('env -> 'a -> 'a) ->
              ('env -> 'b -> 'b) ->
              ('env -> 'c -> 'c) ->
              'env ->
              'a * 'b * 'c ->
              'a * 'b * 'c =
          fun vx vy vz env (x, y, z) ->
            let x = vx env x in
            let y = vy env y in
            let z = vz env z in
            (x, y, z)

        method visit_mutability
            : 'a. ('env -> 'a -> 'a) -> 'env -> 'a mutability -> 'a mutability =
          fun v env this -> this

        method visit_todo : 'env -> todo -> todo = fun _ x -> x
        method visit_string : 'env -> string -> string = fun _ x -> x
        method visit_span : 'env -> span -> span = fun _ x -> x

        method visit_local_ident : 'env -> local_ident -> local_ident =
          fun _ x -> x

        method visit_global_ident : 'env -> global_ident -> global_ident =
          fun _ x -> x

        method visit_concrete_ident : 'env -> concrete_ident -> concrete_ident =
          fun _ x -> x

        method visit_char : 'env -> char -> char = fun _ x -> x
        method visit_bool : 'env -> bool -> bool = fun _ x -> x
        method visit_int_kind : 'env -> int_kind -> int_kind = fun _ x -> x

        method visit_float_kind : 'env -> float_kind -> float_kind =
          fun _ x -> x

        method visit_feature_mutable_reference
            : 'env -> F.mutable_reference -> F.mutable_reference =
          fun _ x -> x

        method visit_feature_reference : 'env -> F.reference -> F.reference =
          fun _ x -> x

        method visit_feature_slice : 'env -> F.slice -> F.slice = fun _ x -> x

        method visit_feature_raw_pointer
            : 'env -> F.raw_pointer -> F.raw_pointer =
          fun _ x -> x

        method visit_feature_lifetime : 'env -> F.lifetime -> F.lifetime =
          fun _ x -> x

        method visit_feature_mutable_variable
            : 'env -> F.mutable_variable -> F.mutable_variable =
          fun _ x -> x

        method visit_feature_as_pattern : 'env -> F.as_pattern -> F.as_pattern =
          fun _ x -> x

        method visit_feature_construct_base
            : 'env -> F.construct_base -> F.construct_base =
          fun _ x -> x

        method visit_feature_monadic_binding
            : 'env -> F.monadic_binding -> F.monadic_binding =
          fun _ x -> x

        method visit_feature_block : 'env -> F.block -> F.block = fun _ x -> x
        method visit_feature_macro : 'env -> F.macro -> F.macro = fun _ x -> x
        method visit_feature_loop : 'env -> F.loop -> F.loop = fun _ x -> x
        method visit_feature_break : 'env -> F.break -> F.break = fun _ x -> x

        method visit_feature_early_exit : 'env -> F.early_exit -> F.early_exit =
          fun _ x -> x

        method visit_feature_question_mark
            : 'env -> F.question_mark -> F.question_mark =
          fun _ x -> x

        method visit_feature_state_passing_loop
            : 'env -> F.state_passing_loop -> F.state_passing_loop =
          fun _ x -> x

        method visit_feature_continue : 'env -> F.continue -> F.continue =
          fun _ x -> x

        method visit_feature_mutable_pointer
            : 'env -> F.mutable_pointer -> F.mutable_pointer =
          fun _ x -> x

        method visit_feature_monadic_action
            : 'env -> F.monadic_action -> F.monadic_action =
          fun _ x -> x

        method visit_feature_while_loop : 'env -> F.while_loop -> F.while_loop =
          fun _ x -> x

        method visit_feature_for_loop : 'env -> F.for_loop -> F.for_loop =
          fun _ x -> x

        method visit_feature_for_index_loop
            : 'env -> F.for_index_loop -> F.for_index_loop =
          fun _ x -> x

        method visit_feature_arbitrary_lhs
            : 'env -> F.arbitrary_lhs -> F.arbitrary_lhs =
          fun _ x -> x

        method visit_feature_nontrivial_lhs
            : 'env -> F.nontrivial_lhs -> F.nontrivial_lhs =
          fun _ x -> x

        method visit_feature_quote : 'env -> F.quote -> F.quote = fun _ x -> x
      end

    class virtual ['self] mapreduce =
      object (self : 'self)
        method visit_literal (env : 'env) (this : literal) : literal * 'acc =
          match this with
          | String x0 ->
              let x0, reduce_acc = self#visit_string env x0 in
              (String x0, reduce_acc)
          | Char x0 ->
              let x0, reduce_acc = self#visit_char env x0 in
              (Char x0, reduce_acc)
          | Int record_payload ->
              let value, reduce_acc =
                self#visit_string env record_payload.value
              in
              let negative, reduce_acc' =
                self#visit_bool env record_payload.negative
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let kind, reduce_acc' =
                self#visit_int_kind env record_payload.kind
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Int { value; negative; kind }, reduce_acc)
          | Float record_payload ->
              let value, reduce_acc =
                self#visit_string env record_payload.value
              in
              let negative, reduce_acc' =
                self#visit_bool env record_payload.negative
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let kind, reduce_acc' =
                self#visit_float_kind env record_payload.kind
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Float { value; negative; kind }, reduce_acc)
          | Bool x0 ->
              let x0, reduce_acc = self#visit_bool env x0 in
              (Bool x0, reduce_acc)

        method visit_attr_kind (env : 'env) (this : attr_kind)
            : attr_kind * 'acc =
          match this with
          | Tool record_payload ->
              let path, reduce_acc =
                self#visit_string env record_payload.path
              in
              let tokens, reduce_acc' =
                self#visit_string env record_payload.tokens
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Tool { path; tokens }, reduce_acc)
          | DocComment record_payload ->
              let kind, reduce_acc =
                self#visit_doc_comment_kind env record_payload.kind
              in
              let body, reduce_acc' =
                self#visit_string env record_payload.body
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (DocComment { kind; body }, reduce_acc)

        method visit_attr (env : 'env) (this : attr) : attr * 'acc =
          let kind, reduce_acc = self#visit_attr_kind env this.kind in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : attr = { kind; span } in
          (out, reduce_acc)

        method visit_doc_comment_kind (env : 'env) (this : doc_comment_kind)
            : doc_comment_kind * 'acc =
          match this with
          | DCKLine -> (DCKLine, self#zero)
          | DCKBlock -> (DCKBlock, self#zero)

        method visit_borrow_kind (env : 'env) (this : borrow_kind)
            : borrow_kind * 'acc =
          match this with
          | Shared -> (Shared, self#zero)
          | Unique -> (Unique, self#zero)
          | Mut x0 ->
              let x0, reduce_acc =
                self#visit_feature_mutable_reference env x0
              in
              (Mut x0, reduce_acc)

        method visit_binding_mode (env : 'env) (this : binding_mode)
            : binding_mode * 'acc =
          match this with
          | ByValue -> (ByValue, self#zero)
          | ByRef (x0, x1) ->
              let x0, reduce_acc = self#visit_borrow_kind env x0 in
              let x1, reduce_acc' = self#visit_feature_reference env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (ByRef (x0, x1), reduce_acc)

        method visit_ty (env : 'env) (this : ty) : ty * 'acc =
          match this with
          | TBool -> (TBool, self#zero)
          | TChar -> (TChar, self#zero)
          | TInt x0 ->
              let x0, reduce_acc = self#visit_int_kind env x0 in
              (TInt x0, reduce_acc)
          | TFloat x0 ->
              let x0, reduce_acc = self#visit_float_kind env x0 in
              (TFloat x0, reduce_acc)
          | TStr -> (TStr, self#zero)
          | TApp record_payload ->
              let ident, reduce_acc =
                self#visit_global_ident env record_payload.ident
              in
              let args, reduce_acc' =
                self#visit_list self#visit_generic_value env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TApp { ident; args }, reduce_acc)
          | TArray record_payload ->
              let typ, reduce_acc = self#visit_ty env record_payload.typ in
              let length, reduce_acc' =
                self#visit_expr env record_payload.length
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TArray { typ; length }, reduce_acc)
          | TSlice record_payload ->
              let witness, reduce_acc =
                self#visit_feature_slice env record_payload.witness
              in
              let ty, reduce_acc' = self#visit_ty env record_payload.ty in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TSlice { witness; ty }, reduce_acc)
          | TRawPointer record_payload ->
              let witness, reduce_acc =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              (TRawPointer { witness }, reduce_acc)
          | TRef record_payload ->
              let witness, reduce_acc =
                self#visit_feature_reference env record_payload.witness
              in
              let region, reduce_acc' =
                self#visit_todo env record_payload.region
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let mut, reduce_acc' =
                self#visit_mutability self#visit_feature_mutable_reference env
                  record_payload.mut
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TRef { witness; region; typ; mut }, reduce_acc)
          | TParam x0 ->
              let x0, reduce_acc = self#visit_local_ident env x0 in
              (TParam x0, reduce_acc)
          | TArrow (x0, x1) ->
              let x0, reduce_acc = self#visit_list self#visit_ty env x0 in
              let x1, reduce_acc' = self#visit_ty env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TArrow (x0, x1), reduce_acc)
          | TAssociatedType record_payload ->
              let impl, reduce_acc =
                self#visit_impl_expr env record_payload.impl
              in
              let item, reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TAssociatedType { impl; item }, reduce_acc)
          | TOpaque x0 ->
              let x0, reduce_acc = self#visit_concrete_ident env x0 in
              (TOpaque x0, reduce_acc)

        method visit_generic_value (env : 'env) (this : generic_value)
            : generic_value * 'acc =
          match this with
          | GLifetime record_payload ->
              let lt, reduce_acc = self#visit_todo env record_payload.lt in
              let witness, reduce_acc' =
                self#visit_feature_lifetime env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (GLifetime { lt; witness }, reduce_acc)
          | GType x0 ->
              let x0, reduce_acc = self#visit_ty env x0 in
              (GType x0, reduce_acc)
          | GConst x0 ->
              let x0, reduce_acc = self#visit_expr env x0 in
              (GConst x0, reduce_acc)

        method visit_impl_expr (env : 'env) (this : impl_expr)
            : impl_expr * 'acc =
          match this with
          | Self -> (Self, self#zero)
          | Concrete x0 ->
              let x0, reduce_acc = self#visit_trait_goal env x0 in
              (Concrete x0, reduce_acc)
          | LocalBound record_payload ->
              let id, reduce_acc = self#visit_string env record_payload.id in
              (LocalBound { id }, reduce_acc)
          | Parent record_payload ->
              let impl, reduce_acc =
                self#visit_impl_expr env record_payload.impl
              in
              let ident, reduce_acc' =
                self#visit_impl_ident env record_payload.ident
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Parent { impl; ident }, reduce_acc)
          | Projection record_payload ->
              let impl, reduce_acc =
                self#visit_impl_expr env record_payload.impl
              in
              let ident, reduce_acc' =
                self#visit_impl_ident env record_payload.ident
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let item, reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Projection { impl; ident; item }, reduce_acc)
          | ImplApp record_payload ->
              let impl, reduce_acc =
                self#visit_impl_expr env record_payload.impl
              in
              let args, reduce_acc' =
                self#visit_list self#visit_impl_expr env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (ImplApp { impl; args }, reduce_acc)
          | Dyn x0 ->
              let x0, reduce_acc = self#visit_trait_goal env x0 in
              (Dyn x0, reduce_acc)
          | Builtin x0 ->
              let x0, reduce_acc = self#visit_trait_goal env x0 in
              (Builtin x0, reduce_acc)
          | FnPointer x0 ->
              let x0, reduce_acc = self#visit_ty env x0 in
              (FnPointer x0, reduce_acc)
          | ClosureIE x0 ->
              let x0, reduce_acc = self#visit_todo env x0 in
              (ClosureIE x0, reduce_acc)

        method visit_trait_goal (env : 'env) (this : trait_goal)
            : trait_goal * 'acc =
          let trait, reduce_acc = self#visit_concrete_ident env this.trait in
          let args, reduce_acc' =
            self#visit_list self#visit_generic_value env this.args
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : trait_goal = { trait; args } in
          (out, reduce_acc)

        method visit_impl_ident (env : 'env) (this : impl_ident)
            : impl_ident * 'acc =
          let goal, reduce_acc = self#visit_trait_goal env this.goal in
          let out : impl_ident = { goal; name = this.name } in
          (out, reduce_acc)

        method visit_pat' (env : 'env) (this : pat') : pat' * 'acc =
          match this with
          | PWild -> (PWild, self#zero)
          | PAscription record_payload ->
              let typ, reduce_acc = self#visit_ty env record_payload.typ in
              let typ_span, reduce_acc' =
                self#visit_span env record_payload.typ_span
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let pat, reduce_acc' = self#visit_pat env record_payload.pat in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (PAscription { typ; typ_span; pat }, reduce_acc)
          | PConstruct record_payload ->
              let name, reduce_acc =
                self#visit_global_ident env record_payload.name
              in
              let args, reduce_acc' =
                self#visit_list self#visit_field_pat env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let is_record, reduce_acc' =
                self#visit_bool env record_payload.is_record
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let is_struct, reduce_acc' =
                self#visit_bool env record_payload.is_struct
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (PConstruct { name; args; is_record; is_struct }, reduce_acc)
          | POr record_payload ->
              let subpats, reduce_acc =
                self#visit_list self#visit_pat env record_payload.subpats
              in
              (POr { subpats }, reduce_acc)
          | PArray record_payload ->
              let args, reduce_acc =
                self#visit_list self#visit_pat env record_payload.args
              in
              (PArray { args }, reduce_acc)
          | PDeref record_payload ->
              let subpat, reduce_acc =
                self#visit_pat env record_payload.subpat
              in
              let witness, reduce_acc' =
                self#visit_feature_reference env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (PDeref { subpat; witness }, reduce_acc)
          | PConstant record_payload ->
              let lit, reduce_acc = self#visit_literal env record_payload.lit in
              (PConstant { lit }, reduce_acc)
          | PBinding record_payload ->
              let mut, reduce_acc =
                self#visit_mutability self#visit_feature_mutable_variable env
                  record_payload.mut
              in
              let mode, reduce_acc' =
                self#visit_binding_mode env record_payload.mode
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let var, reduce_acc' =
                self#visit_local_ident env record_payload.var
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let subpat, reduce_acc' =
                self#visit_option
                  (self#visit_tuple2 self#visit_pat
                     self#visit_feature_as_pattern)
                  env record_payload.subpat
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (PBinding { mut; mode; var; typ; subpat }, reduce_acc)

        method visit_pat (env : 'env) (this : pat) : pat * 'acc =
          let p, reduce_acc = self#visit_pat' env this.p in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let typ, reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : pat = { p; span; typ } in
          (out, reduce_acc)

        method visit_field_pat (env : 'env) (this : field_pat)
            : field_pat * 'acc =
          let field, reduce_acc = self#visit_global_ident env this.field in
          let pat, reduce_acc' = self#visit_pat env this.pat in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : field_pat = { field; pat } in
          (out, reduce_acc)

        method visit_expr' (env : 'env) (this : expr') : expr' * 'acc =
          match this with
          | If record_payload ->
              let cond, reduce_acc = self#visit_expr env record_payload.cond in
              let then_, reduce_acc' =
                self#visit_expr env record_payload.then_
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let else_, reduce_acc' =
                self#visit_option self#visit_expr env record_payload.else_
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (If { cond; then_; else_ }, reduce_acc)
          | App record_payload ->
              let f, reduce_acc = self#visit_expr env record_payload.f in
              let args, reduce_acc' =
                self#visit_list self#visit_expr env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let generic_args, reduce_acc' =
                self#visit_list self#visit_generic_value env
                  record_payload.generic_args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let impl, reduce_acc' =
                self#visit_option self#visit_impl_expr env record_payload.impl
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (App { f; args; generic_args; impl }, reduce_acc)
          | Literal x0 ->
              let x0, reduce_acc = self#visit_literal env x0 in
              (Literal x0, reduce_acc)
          | Array x0 ->
              let x0, reduce_acc = self#visit_list self#visit_expr env x0 in
              (Array x0, reduce_acc)
          | Construct record_payload ->
              let constructor, reduce_acc =
                self#visit_global_ident env record_payload.constructor
              in
              let is_record, reduce_acc' =
                self#visit_bool env record_payload.is_record
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let is_struct, reduce_acc' =
                self#visit_bool env record_payload.is_struct
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let fields, reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_global_ident self#visit_expr)
                  env record_payload.fields
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let base, reduce_acc' =
                self#visit_option
                  (self#visit_tuple2 self#visit_expr
                     self#visit_feature_construct_base)
                  env record_payload.base
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              ( Construct { constructor; is_record; is_struct; fields; base },
                reduce_acc )
          | Match record_payload ->
              let scrutinee, reduce_acc =
                self#visit_expr env record_payload.scrutinee
              in
              let arms, reduce_acc' =
                self#visit_list self#visit_arm env record_payload.arms
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Match { scrutinee; arms }, reduce_acc)
          | Let record_payload ->
              let monadic, reduce_acc =
                self#visit_option
                  (self#visit_tuple2 self#visit_supported_monads
                     self#visit_feature_monadic_binding)
                  env record_payload.monadic
              in
              let lhs, reduce_acc' = self#visit_pat env record_payload.lhs in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let rhs, reduce_acc' = self#visit_expr env record_payload.rhs in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let body, reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Let { monadic; lhs; rhs; body }, reduce_acc)
          | Block (x0, x1) ->
              let x0, reduce_acc = self#visit_expr env x0 in
              let x1, reduce_acc' = self#visit_feature_block env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Block (x0, x1), reduce_acc)
          | LocalVar x0 ->
              let x0, reduce_acc = self#visit_local_ident env x0 in
              (LocalVar x0, reduce_acc)
          | GlobalVar x0 ->
              let x0, reduce_acc = self#visit_global_ident env x0 in
              (GlobalVar x0, reduce_acc)
          | Ascription record_payload ->
              let e, reduce_acc = self#visit_expr env record_payload.e in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Ascription { e; typ }, reduce_acc)
          | MacroInvokation record_payload ->
              let macro, reduce_acc =
                self#visit_global_ident env record_payload.macro
              in
              let args, reduce_acc' =
                self#visit_string env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_macro env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (MacroInvokation { macro; args; witness }, reduce_acc)
          | Assign record_payload ->
              let lhs, reduce_acc = self#visit_lhs env record_payload.lhs in
              let e, reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_mutable_variable env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Assign { lhs; e; witness }, reduce_acc)
          | Loop record_payload ->
              let body, reduce_acc = self#visit_expr env record_payload.body in
              let kind, reduce_acc' =
                self#visit_loop_kind env record_payload.kind
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let state, reduce_acc' =
                self#visit_option self#visit_loop_state env record_payload.state
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let label, reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Loop { body; kind; state; label; witness }, reduce_acc)
          | Break record_payload ->
              let e, reduce_acc = self#visit_expr env record_payload.e in
              let label, reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_tuple2 self#visit_feature_break
                  self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Break { e; label; witness }, reduce_acc)
          | Return record_payload ->
              let e, reduce_acc = self#visit_expr env record_payload.e in
              let witness, reduce_acc' =
                self#visit_feature_early_exit env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Return { e; witness }, reduce_acc)
          | QuestionMark record_payload ->
              let e, reduce_acc = self#visit_expr env record_payload.e in
              let return_typ, reduce_acc' =
                self#visit_ty env record_payload.return_typ
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_question_mark env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (QuestionMark { e; return_typ; witness }, reduce_acc)
          | Continue record_payload ->
              let e, reduce_acc =
                self#visit_option
                  (self#visit_tuple2 self#visit_feature_state_passing_loop
                     self#visit_expr)
                  env record_payload.e
              in
              let label, reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_tuple2 self#visit_feature_continue
                  self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Continue { e; label; witness }, reduce_acc)
          | Borrow record_payload ->
              let kind, reduce_acc =
                self#visit_borrow_kind env record_payload.kind
              in
              let e, reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_reference env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Borrow { kind; e; witness }, reduce_acc)
          | AddressOf record_payload ->
              let mut, reduce_acc =
                self#visit_mutability self#visit_feature_mutable_pointer env
                  record_payload.mut
              in
              let e, reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (AddressOf { mut; e; witness }, reduce_acc)
          | Closure record_payload ->
              let params, reduce_acc =
                self#visit_list self#visit_pat env record_payload.params
              in
              let body, reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let captures, reduce_acc' =
                self#visit_list self#visit_expr env record_payload.captures
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Closure { params; body; captures }, reduce_acc)
          | EffectAction record_payload ->
              let action, reduce_acc =
                self#visit_feature_monadic_action env record_payload.action
              in
              let argument, reduce_acc' =
                self#visit_expr env record_payload.argument
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (EffectAction { action; argument }, reduce_acc)
          | Quote quote ->
              let quote, acc = self#visit_quote env quote in
              (Quote quote, acc)

        method visit_expr (env : 'env) (this : expr) : expr * 'acc =
          let e, reduce_acc = self#visit_expr' env this.e in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let typ, reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : expr = { e; span; typ } in
          (out, reduce_acc)

        method visit_quote (env : 'env) ({ contents; witness } : quote)
            : quote * 'acc =
          let list, reduce_acc =
            self#visit_list
              (fun env -> function
                | `Verbatim code -> (`Verbatim code, self#zero)
                | `Expr e ->
                    let e, acc = self#visit_expr env e in
                    (`Expr e, acc)
                | `Pat p ->
                    let p, acc = self#visit_pat env p in
                    (`Pat p, acc))
              env contents
          in
          let witness, reduce_acc' = self#visit_feature_quote env witness in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          ({ contents; witness }, reduce_acc)

        method visit_supported_monads (env : 'env) (this : supported_monads)
            : supported_monads * 'acc =
          match this with
          | MException x0 ->
              let x0, reduce_acc = self#visit_ty env x0 in
              (MException x0, reduce_acc)
          | MResult x0 ->
              let x0, reduce_acc = self#visit_ty env x0 in
              (MResult x0, reduce_acc)
          | MOption -> (MOption, self#zero)

        method visit_loop_kind (env : 'env) (this : loop_kind)
            : loop_kind * 'acc =
          match this with
          | UnconditionalLoop -> (UnconditionalLoop, self#zero)
          | WhileLoop record_payload ->
              let condition, reduce_acc =
                self#visit_expr env record_payload.condition
              in
              let witness, reduce_acc' =
                self#visit_feature_while_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (WhileLoop { condition; witness }, reduce_acc)
          | ForLoop record_payload ->
              let pat, reduce_acc = self#visit_pat env record_payload.pat in
              let it, reduce_acc' = self#visit_expr env record_payload.it in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_for_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (ForLoop { pat; it; witness }, reduce_acc)
          | ForIndexLoop record_payload ->
              let start, reduce_acc =
                self#visit_expr env record_payload.start
              in
              let end_, reduce_acc' = self#visit_expr env record_payload.end_ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let var, reduce_acc' =
                self#visit_local_ident env record_payload.var
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let var_typ, reduce_acc' =
                self#visit_ty env record_payload.var_typ
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_for_index_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (ForIndexLoop { start; end_; var; var_typ; witness }, reduce_acc)

        method visit_loop_state (env : 'env) (this : loop_state)
            : loop_state * 'acc =
          let init, reduce_acc = self#visit_expr env this.init in
          let bpat, reduce_acc' = self#visit_pat env this.bpat in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let witness, reduce_acc' =
            self#visit_feature_state_passing_loop env this.witness
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : loop_state = { init; bpat; witness } in
          (out, reduce_acc)

        method visit_lhs (env : 'env) (this : lhs) : lhs * 'acc =
          match this with
          | LhsLocalVar record_payload ->
              let var, reduce_acc =
                self#visit_local_ident env record_payload.var
              in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (LhsLocalVar { var; typ }, reduce_acc)
          | LhsArbitraryExpr record_payload ->
              let e, reduce_acc = self#visit_expr env record_payload.e in
              let witness, reduce_acc' =
                self#visit_feature_arbitrary_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (LhsArbitraryExpr { e; witness }, reduce_acc)
          | LhsFieldAccessor record_payload ->
              let e, reduce_acc = self#visit_lhs env record_payload.e in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let field, reduce_acc' =
                self#visit_global_ident env record_payload.field
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (LhsFieldAccessor { e; typ; field; witness }, reduce_acc)
          | LhsArrayAccessor record_payload ->
              let e, reduce_acc = self#visit_lhs env record_payload.e in
              let typ, reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let index, reduce_acc' =
                self#visit_expr env record_payload.index
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (LhsArrayAccessor { e; typ; index; witness }, reduce_acc)

        method visit_arm' (env : 'env) (this : arm') : arm' * 'acc =
          let arm_pat, reduce_acc = self#visit_pat env this.arm_pat in
          let body, reduce_acc' = self#visit_expr env this.body in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : arm' = { arm_pat; body } in
          (out, reduce_acc)

        method visit_arm (env : 'env) (this : arm) : arm * 'acc =
          let arm, reduce_acc = self#visit_arm' env this.arm in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : arm = { arm; span } in
          (out, reduce_acc)

        method visit_generic_param (env : 'env) (this : generic_param)
            : generic_param * 'acc =
          let ident, reduce_acc = self#visit_local_ident env this.ident in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let kind, reduce_acc' = self#visit_generic_param_kind env this.kind in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : generic_param = { ident; span; attrs; kind } in
          (out, reduce_acc)

        method visit_generic_param_kind (env : 'env) (this : generic_param_kind)
            : generic_param_kind * 'acc =
          match this with
          | GPLifetime record_payload ->
              let witness, reduce_acc =
                self#visit_feature_lifetime env record_payload.witness
              in
              (GPLifetime { witness }, reduce_acc)
          | GPType record_payload ->
              let default, reduce_acc =
                self#visit_option self#visit_ty env record_payload.default
              in
              (GPType { default }, reduce_acc)
          | GPConst record_payload ->
              let typ, reduce_acc = self#visit_ty env record_payload.typ in
              (GPConst { typ }, reduce_acc)

        method visit_generic_constraint (env : 'env) (this : generic_constraint)
            : generic_constraint * 'acc =
          match this with
          | GCLifetime (x0, x1) ->
              let x0, reduce_acc = self#visit_todo env x0 in
              let x1, reduce_acc' = self#visit_feature_lifetime env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (GCLifetime (x0, x1), reduce_acc)
          | GCType x0 ->
              let x0, reduce_acc = self#visit_impl_ident env x0 in
              (GCType x0, reduce_acc)

        method visit_param (env : 'env) (this : param) : param * 'acc =
          let pat, reduce_acc = self#visit_pat env this.pat in
          let typ, reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let typ_span, reduce_acc' =
            self#visit_option self#visit_span env this.typ_span
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : param = { pat; typ; typ_span; attrs } in
          (out, reduce_acc)

        method visit_generics (env : 'env) (this : generics) : generics * 'acc =
          let params, reduce_acc =
            self#visit_list self#visit_generic_param env this.params
          in
          let constraints, reduce_acc' =
            self#visit_list self#visit_generic_constraint env this.constraints
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : generics = { params; constraints } in
          (out, reduce_acc)

        method visit_variant (env : 'env) (this : variant) : variant * 'acc =
          let name, reduce_acc = self#visit_concrete_ident env this.name in
          let arguments, reduce_acc' =
            self#visit_list
              (self#visit_tuple3 self#visit_concrete_ident self#visit_ty
                 (self#visit_list self#visit_attr))
              env this.arguments
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let is_record, reduce_acc' = self#visit_bool env this.is_record in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : variant = { name; arguments; is_record; attrs } in
          (out, reduce_acc)

        method visit_item' (env : 'env) (this : item') : item' * 'acc =
          match this with
          | Fn record_payload ->
              let name, reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let generics, reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let body, reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let params, reduce_acc' =
                self#visit_list self#visit_param env record_payload.params
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Fn { name; generics; body; params }, reduce_acc)
          | TyAlias record_payload ->
              let name, reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let generics, reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let ty, reduce_acc' = self#visit_ty env record_payload.ty in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (TyAlias { name; generics; ty }, reduce_acc)
          | Type record_payload ->
              let name, reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let generics, reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let variants, reduce_acc' =
                self#visit_list self#visit_variant env record_payload.variants
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let is_struct, reduce_acc' =
                self#visit_bool env record_payload.is_struct
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Type { name; generics; variants; is_struct }, reduce_acc)
          | IMacroInvokation record_payload ->
              let macro, reduce_acc =
                self#visit_concrete_ident env record_payload.macro
              in
              let argument, reduce_acc' =
                self#visit_string env record_payload.argument
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let span, reduce_acc' = self#visit_span env record_payload.span in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let witness, reduce_acc' =
                self#visit_feature_macro env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (IMacroInvokation { macro; argument; span; witness }, reduce_acc)
          | Trait record_payload ->
              let name, reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let generics, reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let items, reduce_acc' =
                self#visit_list self#visit_trait_item env record_payload.items
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Trait { name; generics; items }, reduce_acc)
          | Impl record_payload ->
              let generics, reduce_acc =
                self#visit_generics env record_payload.generics
              in
              let self_ty, reduce_acc' =
                self#visit_ty env record_payload.self_ty
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let of_trait, reduce_acc' =
                self#visit_tuple2 self#visit_global_ident
                  (self#visit_list self#visit_generic_value)
                  env record_payload.of_trait
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let items, reduce_acc' =
                self#visit_list self#visit_impl_item env record_payload.items
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let parent_bounds, reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              ( Impl { generics; self_ty; of_trait; items; parent_bounds },
                reduce_acc )
          | Alias record_payload ->
              let name, reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let item, reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Alias { name; item }, reduce_acc)
          | Use record_payload ->
              let path, reduce_acc =
                self#visit_list self#visit_string env record_payload.path
              in
              let is_external, reduce_acc' =
                self#visit_bool env record_payload.is_external
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let rename, reduce_acc' =
                self#visit_option self#visit_string env record_payload.rename
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (Use { path; is_external; rename }, reduce_acc)
          | Quote quote ->
              let quote, acc = self#visit_quote env quote in
              (Quote quote, acc)
          | HaxError x0 ->
              let x0, reduce_acc = self#visit_string env x0 in
              (HaxError x0, reduce_acc)
          | NotImplementedYet -> (NotImplementedYet, self#zero)

        method visit_item (env : 'env) (this : item) : item * 'acc =
          let v, reduce_acc = self#visit_item' env this.v in
          let span, reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ident, reduce_acc' = self#visit_concrete_ident env this.ident in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : item = { v; span; ident; attrs } in
          (out, reduce_acc)

        method visit_impl_item' (env : 'env) (this : impl_item')
            : impl_item' * 'acc =
          match this with
          | IIType record_payload ->
              let typ, reduce_acc = self#visit_ty env record_payload.typ in
              let parent_bounds, reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (IIType { typ; parent_bounds }, reduce_acc)
          | IIFn record_payload ->
              let body, reduce_acc = self#visit_expr env record_payload.body in
              let params, reduce_acc' =
                self#visit_list self#visit_param env record_payload.params
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              (IIFn { body; params }, reduce_acc)

        method visit_impl_item (env : 'env) (this : impl_item)
            : impl_item * 'acc =
          let ii_span, reduce_acc = self#visit_span env this.ii_span in
          let ii_generics, reduce_acc' =
            self#visit_generics env this.ii_generics
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ii_v, reduce_acc' = self#visit_impl_item' env this.ii_v in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ii_ident, reduce_acc' =
            self#visit_concrete_ident env this.ii_ident
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ii_attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.ii_attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : impl_item =
            { ii_span; ii_generics; ii_v; ii_ident; ii_attrs }
          in
          (out, reduce_acc)

        method visit_trait_item' (env : 'env) (this : trait_item')
            : trait_item' * 'acc =
          match this with
          | TIType x0 ->
              let x0, reduce_acc =
                self#visit_list self#visit_impl_ident env x0
              in
              (TIType x0, reduce_acc)
          | TIFn x0 ->
              let x0, reduce_acc = self#visit_ty env x0 in
              (TIFn x0, reduce_acc)

        method visit_trait_item (env : 'env) (this : trait_item)
            : trait_item * 'acc =
          let ti_span, reduce_acc = self#visit_span env this.ti_span in
          let ti_generics, reduce_acc' =
            self#visit_generics env this.ti_generics
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ti_v, reduce_acc' = self#visit_trait_item' env this.ti_v in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ti_ident, reduce_acc' =
            self#visit_concrete_ident env this.ti_ident
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let ti_attrs, reduce_acc' =
            self#visit_list self#visit_attr env this.ti_attrs
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let out : trait_item =
            { ti_span; ti_generics; ti_v; ti_ident; ti_attrs }
          in
          (out, reduce_acc)

        method visit_list
            : 'a. ('env -> 'a -> 'a * 'acc) -> 'env -> 'a list -> 'a list * 'acc
            =
          fun v env ->
            Base.List.fold_map ~init:self#zero ~f:(fun acc x ->
                let x, acc' = v env x in
                (self#plus acc acc', x))
            >> swap

        method visit_option
            : 'a.
              ('env -> 'a -> 'a * 'acc) -> 'env -> 'a option -> 'a option * 'acc
            =
          fun v env this ->
            match this with
            | None -> (None, self#zero)
            | Some x ->
                let x, acc = v env x in
                (Some x, acc)

        method visit_tuple2
            : 'a 'b.
              ('env -> 'a -> 'a * 'acc) ->
              ('env -> 'b -> 'b * 'acc) ->
              'env ->
              'a * 'b ->
              ('a * 'b) * 'acc =
          fun vx vy env (x, y) ->
            let x, acc = vx env x in
            let y, acc' = vy env y in
            let acc = self#plus acc acc' in
            ((x, y), acc)

        method visit_tuple3
            : 'a 'b 'c.
              ('env -> 'a -> 'a * 'acc) ->
              ('env -> 'b -> 'b * 'acc) ->
              ('env -> 'c -> 'c * 'acc) ->
              'env ->
              'a * 'b * 'c ->
              ('a * 'b * 'c) * 'acc =
          fun vx vy vz env (x, y, z) ->
            let x, acc = vx env x in
            let y, acc' = vy env y in
            let acc = self#plus acc acc' in
            let z, acc' = vz env z in
            let acc = self#plus acc acc' in
            ((x, y, z), acc)

        method visit_mutability
            : 'a.
              ('env -> 'a -> 'a * 'acc) ->
              'env ->
              'a mutability ->
              'a mutability * 'acc =
          fun v env this -> (this, self#zero)

        method visit_todo : 'env -> todo -> todo * 'acc =
          fun _ x -> (x, self#zero)

        method visit_string : 'env -> string -> string * 'acc =
          fun _ x -> (x, self#zero)

        method visit_span : 'env -> span -> span * 'acc =
          fun _ x -> (x, self#zero)

        method visit_local_ident : 'env -> local_ident -> local_ident * 'acc =
          fun _ x -> (x, self#zero)

        method visit_global_ident : 'env -> global_ident -> global_ident * 'acc
            =
          fun _ x -> (x, self#zero)

        method visit_concrete_ident
            : 'env -> concrete_ident -> concrete_ident * 'acc =
          fun _ x -> (x, self#zero)

        method visit_char : 'env -> char -> char * 'acc =
          fun _ x -> (x, self#zero)

        method visit_bool : 'env -> bool -> bool * 'acc =
          fun _ x -> (x, self#zero)

        method visit_int_kind : 'env -> int_kind -> int_kind * 'acc =
          fun _ x -> (x, self#zero)

        method visit_float_kind : 'env -> float_kind -> float_kind * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_mutable_reference
            : 'env -> F.mutable_reference -> F.mutable_reference * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_reference
            : 'env -> F.reference -> F.reference * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_slice : 'env -> F.slice -> F.slice * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_raw_pointer
            : 'env -> F.raw_pointer -> F.raw_pointer * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_lifetime : 'env -> F.lifetime -> F.lifetime * 'acc
            =
          fun _ x -> (x, self#zero)

        method visit_feature_mutable_variable
            : 'env -> F.mutable_variable -> F.mutable_variable * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_as_pattern
            : 'env -> F.as_pattern -> F.as_pattern * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_construct_base
            : 'env -> F.construct_base -> F.construct_base * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_monadic_binding
            : 'env -> F.monadic_binding -> F.monadic_binding * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_block : 'env -> F.block -> F.block * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_macro : 'env -> F.macro -> F.macro * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_loop : 'env -> F.loop -> F.loop * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_break : 'env -> F.break -> F.break * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_early_exit
            : 'env -> F.early_exit -> F.early_exit * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_question_mark
            : 'env -> F.question_mark -> F.question_mark * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_state_passing_loop
            : 'env -> F.state_passing_loop -> F.state_passing_loop * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_continue : 'env -> F.continue -> F.continue * 'acc
            =
          fun _ x -> (x, self#zero)

        method visit_feature_mutable_pointer
            : 'env -> F.mutable_pointer -> F.mutable_pointer * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_monadic_action
            : 'env -> F.monadic_action -> F.monadic_action * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_while_loop
            : 'env -> F.while_loop -> F.while_loop * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_for_loop : 'env -> F.for_loop -> F.for_loop * 'acc
            =
          fun _ x -> (x, self#zero)

        method visit_feature_for_index_loop
            : 'env -> F.for_index_loop -> F.for_index_loop * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_arbitrary_lhs
            : 'env -> F.arbitrary_lhs -> F.arbitrary_lhs * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_nontrivial_lhs
            : 'env -> F.nontrivial_lhs -> F.nontrivial_lhs * 'acc =
          fun _ x -> (x, self#zero)

        method visit_feature_quote : 'env -> F.quote -> F.quote * 'acc =
          fun _ x -> (x, self#zero)
      end

    class virtual ['self] reduce =
      object (self : 'self)
        method visit_literal (env : 'env) (this : literal) : 'acc =
          match this with
          | String x0 ->
              let reduce_acc = self#visit_string env x0 in
              reduce_acc
          | Char x0 ->
              let reduce_acc = self#visit_char env x0 in
              reduce_acc
          | Int record_payload ->
              let reduce_acc = self#visit_string env record_payload.value in
              let reduce_acc' = self#visit_bool env record_payload.negative in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_int_kind env record_payload.kind in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Float record_payload ->
              let reduce_acc = self#visit_string env record_payload.value in
              let reduce_acc' = self#visit_bool env record_payload.negative in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_float_kind env record_payload.kind in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Bool x0 ->
              let reduce_acc = self#visit_bool env x0 in
              reduce_acc

        method visit_attr_kind (env : 'env) (this : attr_kind) : 'acc =
          match this with
          | Tool record_payload ->
              let reduce_acc = self#visit_string env record_payload.path in
              let reduce_acc' = self#visit_string env record_payload.tokens in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | DocComment record_payload ->
              let reduce_acc =
                self#visit_doc_comment_kind env record_payload.kind
              in
              let reduce_acc' = self#visit_string env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_attr (env : 'env) (this : attr) : 'acc =
          let reduce_acc = self#visit_attr_kind env this.kind in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_doc_comment_kind (env : 'env) (this : doc_comment_kind)
            : 'acc =
          match this with DCKLine -> self#zero | DCKBlock -> self#zero

        method visit_borrow_kind (env : 'env) (this : borrow_kind) : 'acc =
          match this with
          | Shared -> self#zero
          | Unique -> self#zero
          | Mut x0 ->
              let reduce_acc = self#visit_feature_mutable_reference env x0 in
              reduce_acc

        method visit_binding_mode (env : 'env) (this : binding_mode) : 'acc =
          match this with
          | ByValue -> self#zero
          | ByRef (x0, x1) ->
              let reduce_acc = self#visit_borrow_kind env x0 in
              let reduce_acc' = self#visit_feature_reference env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_ty (env : 'env) (this : ty) : 'acc =
          match this with
          | TBool -> self#zero
          | TChar -> self#zero
          | TInt x0 ->
              let reduce_acc = self#visit_int_kind env x0 in
              reduce_acc
          | TFloat x0 ->
              let reduce_acc = self#visit_float_kind env x0 in
              reduce_acc
          | TStr -> self#zero
          | TApp record_payload ->
              let reduce_acc =
                self#visit_global_ident env record_payload.ident
              in
              let reduce_acc' =
                self#visit_list self#visit_generic_value env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TArray record_payload ->
              let reduce_acc = self#visit_ty env record_payload.typ in
              let reduce_acc' = self#visit_expr env record_payload.length in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TSlice record_payload ->
              let reduce_acc =
                self#visit_feature_slice env record_payload.witness
              in
              let reduce_acc' = self#visit_ty env record_payload.ty in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TRawPointer record_payload ->
              let reduce_acc =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              reduce_acc
          | TRef record_payload ->
              let reduce_acc =
                self#visit_feature_reference env record_payload.witness
              in
              let reduce_acc' = self#visit_todo env record_payload.region in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_mutability self#visit_feature_mutable_reference env
                  record_payload.mut
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TParam x0 ->
              let reduce_acc = self#visit_local_ident env x0 in
              reduce_acc
          | TArrow (x0, x1) ->
              let reduce_acc = self#visit_list self#visit_ty env x0 in
              let reduce_acc' = self#visit_ty env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TAssociatedType record_payload ->
              let reduce_acc = self#visit_impl_expr env record_payload.impl in
              let reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TOpaque x0 ->
              let reduce_acc = self#visit_concrete_ident env x0 in
              reduce_acc

        method visit_generic_value (env : 'env) (this : generic_value) : 'acc =
          match this with
          | GLifetime record_payload ->
              let reduce_acc = self#visit_todo env record_payload.lt in
              let reduce_acc' =
                self#visit_feature_lifetime env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | GType x0 ->
              let reduce_acc = self#visit_ty env x0 in
              reduce_acc
          | GConst x0 ->
              let reduce_acc = self#visit_expr env x0 in
              reduce_acc

        method visit_impl_expr (env : 'env) (this : impl_expr) : 'acc =
          match this with
          | Self -> self#zero
          | Concrete x0 ->
              let reduce_acc = self#visit_trait_goal env x0 in
              reduce_acc
          | LocalBound record_payload ->
              let reduce_acc = self#visit_string env record_payload.id in
              reduce_acc
          | Parent record_payload ->
              let reduce_acc = self#visit_impl_expr env record_payload.impl in
              let reduce_acc' =
                self#visit_impl_ident env record_payload.ident
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Projection record_payload ->
              let reduce_acc = self#visit_impl_expr env record_payload.impl in
              let reduce_acc' =
                self#visit_impl_ident env record_payload.ident
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | ImplApp record_payload ->
              let reduce_acc = self#visit_impl_expr env record_payload.impl in
              let reduce_acc' =
                self#visit_list self#visit_impl_expr env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Dyn x0 ->
              let reduce_acc = self#visit_trait_goal env x0 in
              reduce_acc
          | Builtin x0 ->
              let reduce_acc = self#visit_trait_goal env x0 in
              reduce_acc
          | FnPointer x0 ->
              let reduce_acc = self#visit_ty env x0 in
              reduce_acc
          | ClosureIE x0 ->
              let reduce_acc = self#visit_todo env x0 in
              reduce_acc

        method visit_trait_goal (env : 'env) (this : trait_goal) : 'acc =
          let reduce_acc = self#visit_concrete_ident env this.trait in
          let reduce_acc' =
            self#visit_list self#visit_generic_value env this.args
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_impl_ident (env : 'env) (this : impl_ident) : 'acc =
          let reduce_acc = self#visit_trait_goal env this.goal in
          reduce_acc

        method visit_pat' (env : 'env) (this : pat') : 'acc =
          match this with
          | PWild -> self#zero
          | PAscription record_payload ->
              let reduce_acc = self#visit_ty env record_payload.typ in
              let reduce_acc' = self#visit_span env record_payload.typ_span in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_pat env record_payload.pat in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | PConstruct record_payload ->
              let reduce_acc =
                self#visit_global_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_list self#visit_field_pat env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_bool env record_payload.is_record in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_bool env record_payload.is_struct in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | POr record_payload ->
              let reduce_acc =
                self#visit_list self#visit_pat env record_payload.subpats
              in
              reduce_acc
          | PArray record_payload ->
              let reduce_acc =
                self#visit_list self#visit_pat env record_payload.args
              in
              reduce_acc
          | PDeref record_payload ->
              let reduce_acc = self#visit_pat env record_payload.subpat in
              let reduce_acc' =
                self#visit_feature_reference env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | PConstant record_payload ->
              let reduce_acc = self#visit_literal env record_payload.lit in
              reduce_acc
          | PBinding record_payload ->
              let reduce_acc =
                self#visit_mutability self#visit_feature_mutable_variable env
                  record_payload.mut
              in
              let reduce_acc' =
                self#visit_binding_mode env record_payload.mode
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_local_ident env record_payload.var in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option
                  (self#visit_tuple2 self#visit_pat
                     self#visit_feature_as_pattern)
                  env record_payload.subpat
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_pat (env : 'env) (this : pat) : 'acc =
          let reduce_acc = self#visit_pat' env this.p in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_field_pat (env : 'env) (this : field_pat) : 'acc =
          let reduce_acc = self#visit_global_ident env this.field in
          let reduce_acc' = self#visit_pat env this.pat in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_expr' (env : 'env) (this : expr') : 'acc =
          match this with
          | If record_payload ->
              let reduce_acc = self#visit_expr env record_payload.cond in
              let reduce_acc' = self#visit_expr env record_payload.then_ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option self#visit_expr env record_payload.else_
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | App record_payload ->
              let reduce_acc = self#visit_expr env record_payload.f in
              let reduce_acc' =
                self#visit_list self#visit_expr env record_payload.args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_generic_value env
                  record_payload.generic_args
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option self#visit_impl_expr env record_payload.impl
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Literal x0 ->
              let reduce_acc = self#visit_literal env x0 in
              reduce_acc
          | Array x0 ->
              let reduce_acc = self#visit_list self#visit_expr env x0 in
              reduce_acc
          | Construct record_payload ->
              let reduce_acc =
                self#visit_global_ident env record_payload.constructor
              in
              let reduce_acc' = self#visit_bool env record_payload.is_record in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_bool env record_payload.is_struct in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_global_ident self#visit_expr)
                  env record_payload.fields
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option
                  (self#visit_tuple2 self#visit_expr
                     self#visit_feature_construct_base)
                  env record_payload.base
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Match record_payload ->
              let reduce_acc = self#visit_expr env record_payload.scrutinee in
              let reduce_acc' =
                self#visit_list self#visit_arm env record_payload.arms
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Let record_payload ->
              let reduce_acc =
                self#visit_option
                  (self#visit_tuple2 self#visit_supported_monads
                     self#visit_feature_monadic_binding)
                  env record_payload.monadic
              in
              let reduce_acc' = self#visit_pat env record_payload.lhs in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_expr env record_payload.rhs in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Block (x0, x1) ->
              let reduce_acc = self#visit_expr env x0 in
              let reduce_acc' = self#visit_feature_block env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | LocalVar x0 ->
              let reduce_acc = self#visit_local_ident env x0 in
              reduce_acc
          | GlobalVar x0 ->
              let reduce_acc = self#visit_global_ident env x0 in
              reduce_acc
          | Ascription record_payload ->
              let reduce_acc = self#visit_expr env record_payload.e in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | MacroInvokation record_payload ->
              let reduce_acc =
                self#visit_global_ident env record_payload.macro
              in
              let reduce_acc' = self#visit_string env record_payload.args in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_macro env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Assign record_payload ->
              let reduce_acc = self#visit_lhs env record_payload.lhs in
              let reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_mutable_variable env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Loop record_payload ->
              let reduce_acc = self#visit_expr env record_payload.body in
              let reduce_acc' = self#visit_loop_kind env record_payload.kind in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option self#visit_loop_state env record_payload.state
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Break record_payload ->
              let reduce_acc = self#visit_expr env record_payload.e in
              let reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_tuple2 self#visit_feature_break
                  self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Return record_payload ->
              let reduce_acc = self#visit_expr env record_payload.e in
              let reduce_acc' =
                self#visit_feature_early_exit env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | QuestionMark record_payload ->
              let reduce_acc = self#visit_expr env record_payload.e in
              let reduce_acc' = self#visit_ty env record_payload.return_typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_question_mark env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Continue record_payload ->
              let reduce_acc =
                self#visit_option
                  (self#visit_tuple2 self#visit_feature_state_passing_loop
                     self#visit_expr)
                  env record_payload.e
              in
              let reduce_acc' =
                self#visit_option self#visit_string env record_payload.label
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_tuple2 self#visit_feature_continue
                  self#visit_feature_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Borrow record_payload ->
              let reduce_acc = self#visit_borrow_kind env record_payload.kind in
              let reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_reference env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | AddressOf record_payload ->
              let reduce_acc =
                self#visit_mutability self#visit_feature_mutable_pointer env
                  record_payload.mut
              in
              let reduce_acc' = self#visit_expr env record_payload.e in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_raw_pointer env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Closure record_payload ->
              let reduce_acc =
                self#visit_list self#visit_pat env record_payload.params
              in
              let reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_expr env record_payload.captures
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | EffectAction record_payload ->
              let reduce_acc =
                self#visit_feature_monadic_action env record_payload.action
              in
              let reduce_acc' = self#visit_expr env record_payload.argument in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Quote quote -> self#visit_quote env quote

        method visit_expr (env : 'env) (this : expr) : 'acc =
          let reduce_acc = self#visit_expr' env this.e in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_quote (env : 'env) ({ contents; witness } : quote) : 'acc =
          let reduce_acc =
            self#visit_list
              (fun env -> function
                | `Verbatim code -> self#zero
                | `Expr e -> self#visit_expr env e
                | `Pat p -> self#visit_pat env p)
              env contents
          in
          let reduce_acc' = self#visit_feature_quote env witness in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_supported_monads (env : 'env) (this : supported_monads)
            : 'acc =
          match this with
          | MException x0 ->
              let reduce_acc = self#visit_ty env x0 in
              reduce_acc
          | MResult x0 ->
              let reduce_acc = self#visit_ty env x0 in
              reduce_acc
          | MOption -> self#zero

        method visit_loop_kind (env : 'env) (this : loop_kind) : 'acc =
          match this with
          | UnconditionalLoop -> self#zero
          | WhileLoop record_payload ->
              let reduce_acc = self#visit_expr env record_payload.condition in
              let reduce_acc' =
                self#visit_feature_while_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | ForLoop record_payload ->
              let reduce_acc = self#visit_pat env record_payload.pat in
              let reduce_acc' = self#visit_expr env record_payload.it in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_for_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | ForIndexLoop record_payload ->
              let reduce_acc = self#visit_expr env record_payload.start in
              let reduce_acc' = self#visit_expr env record_payload.end_ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_local_ident env record_payload.var in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_ty env record_payload.var_typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_for_index_loop env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_loop_state (env : 'env) (this : loop_state) : 'acc =
          let reduce_acc = self#visit_expr env this.init in
          let reduce_acc' = self#visit_pat env this.bpat in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' =
            self#visit_feature_state_passing_loop env this.witness
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_lhs (env : 'env) (this : lhs) : 'acc =
          match this with
          | LhsLocalVar record_payload ->
              let reduce_acc = self#visit_local_ident env record_payload.var in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | LhsArbitraryExpr record_payload ->
              let reduce_acc = self#visit_expr env record_payload.e in
              let reduce_acc' =
                self#visit_feature_arbitrary_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | LhsFieldAccessor record_payload ->
              let reduce_acc = self#visit_lhs env record_payload.e in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_global_ident env record_payload.field
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | LhsArrayAccessor record_payload ->
              let reduce_acc = self#visit_lhs env record_payload.e in
              let reduce_acc' = self#visit_ty env record_payload.typ in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_expr env record_payload.index in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_nontrivial_lhs env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_arm' (env : 'env) (this : arm') : 'acc =
          let reduce_acc = self#visit_pat env this.arm_pat in
          let reduce_acc' = self#visit_expr env this.body in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_arm (env : 'env) (this : arm) : 'acc =
          let reduce_acc = self#visit_arm' env this.arm in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_generic_param (env : 'env) (this : generic_param) : 'acc =
          let reduce_acc = self#visit_local_ident env this.ident in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_generic_param_kind env this.kind in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_generic_param_kind (env : 'env) (this : generic_param_kind)
            : 'acc =
          match this with
          | GPLifetime record_payload ->
              let reduce_acc =
                self#visit_feature_lifetime env record_payload.witness
              in
              reduce_acc
          | GPType record_payload ->
              let reduce_acc =
                self#visit_option self#visit_ty env record_payload.default
              in
              reduce_acc
          | GPConst record_payload ->
              let reduce_acc = self#visit_ty env record_payload.typ in
              reduce_acc

        method visit_generic_constraint (env : 'env) (this : generic_constraint)
            : 'acc =
          match this with
          | GCLifetime (x0, x1) ->
              let reduce_acc = self#visit_todo env x0 in
              let reduce_acc' = self#visit_feature_lifetime env x1 in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | GCType x0 ->
              let reduce_acc = self#visit_impl_ident env x0 in
              reduce_acc

        method visit_param (env : 'env) (this : param) : 'acc =
          let reduce_acc = self#visit_pat env this.pat in
          let reduce_acc' = self#visit_ty env this.typ in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' =
            self#visit_option self#visit_span env this.typ_span
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_generics (env : 'env) (this : generics) : 'acc =
          let reduce_acc =
            self#visit_list self#visit_generic_param env this.params
          in
          let reduce_acc' =
            self#visit_list self#visit_generic_constraint env this.constraints
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_variant (env : 'env) (this : variant) : 'acc =
          let reduce_acc = self#visit_concrete_ident env this.name in
          let reduce_acc' =
            self#visit_list
              (self#visit_tuple3 self#visit_concrete_ident self#visit_ty
                 (self#visit_list self#visit_attr))
              env this.arguments
          in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_bool env this.is_record in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_item' (env : 'env) (this : item') : 'acc =
          match this with
          | Fn record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_expr env record_payload.body in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_param env record_payload.params
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | TyAlias record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_ty env record_payload.ty in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Type record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_variant env record_payload.variants
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_bool env record_payload.is_struct in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | IMacroInvokation record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.macro
              in
              let reduce_acc' = self#visit_string env record_payload.argument in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' = self#visit_span env record_payload.span in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_feature_macro env record_payload.witness
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Trait record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_trait_item env record_payload.items
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Impl record_payload ->
              let reduce_acc =
                self#visit_generics env record_payload.generics
              in
              let reduce_acc' = self#visit_ty env record_payload.self_ty in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_tuple2 self#visit_global_ident
                  (self#visit_list self#visit_generic_value)
                  env record_payload.of_trait
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list self#visit_impl_item env record_payload.items
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Alias record_payload ->
              let reduce_acc =
                self#visit_concrete_ident env record_payload.name
              in
              let reduce_acc' =
                self#visit_concrete_ident env record_payload.item
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Use record_payload ->
              let reduce_acc =
                self#visit_list self#visit_string env record_payload.path
              in
              let reduce_acc' =
                self#visit_bool env record_payload.is_external
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              let reduce_acc' =
                self#visit_option self#visit_string env record_payload.rename
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | Quote quote -> self#visit_quote env quote
          | HaxError x0 ->
              let reduce_acc = self#visit_string env x0 in
              reduce_acc
          | NotImplementedYet -> self#zero

        method visit_item (env : 'env) (this : item) : 'acc =
          let reduce_acc = self#visit_item' env this.v in
          let reduce_acc' = self#visit_span env this.span in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_concrete_ident env this.ident in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_impl_item' (env : 'env) (this : impl_item') : 'acc =
          match this with
          | IIType record_payload ->
              let reduce_acc = self#visit_ty env record_payload.typ in
              let reduce_acc' =
                self#visit_list
                  (self#visit_tuple2 self#visit_impl_expr self#visit_impl_ident)
                  env record_payload.parent_bounds
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc
          | IIFn record_payload ->
              let reduce_acc = self#visit_expr env record_payload.body in
              let reduce_acc' =
                self#visit_list self#visit_param env record_payload.params
              in
              let reduce_acc = self#plus reduce_acc reduce_acc' in
              reduce_acc

        method visit_impl_item (env : 'env) (this : impl_item) : 'acc =
          let reduce_acc = self#visit_span env this.ii_span in
          let reduce_acc' = self#visit_generics env this.ii_generics in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_impl_item' env this.ii_v in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_concrete_ident env this.ii_ident in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.ii_attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_trait_item' (env : 'env) (this : trait_item') : 'acc =
          match this with
          | TIType x0 ->
              let reduce_acc = self#visit_list self#visit_impl_ident env x0 in
              reduce_acc
          | TIFn x0 ->
              let reduce_acc = self#visit_ty env x0 in
              reduce_acc

        method visit_trait_item (env : 'env) (this : trait_item) : 'acc =
          let reduce_acc = self#visit_span env this.ti_span in
          let reduce_acc' = self#visit_generics env this.ti_generics in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_trait_item' env this.ti_v in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_concrete_ident env this.ti_ident in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          let reduce_acc' = self#visit_list self#visit_attr env this.ti_attrs in
          let reduce_acc = self#plus reduce_acc reduce_acc' in
          reduce_acc

        method visit_list : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a list -> 'acc
            =
          fun v env this ->
            Base.List.fold ~init:self#zero
              ~f:(fun acc -> v env >> self#plus acc)
              this

        method visit_option
            : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a option -> 'acc =
          fun v env this ->
            match this with
            | None -> self#zero
            | Some x ->
                let acc = v env x in
                acc

        method visit_tuple2
            : 'a 'b.
              ('env -> 'a -> 'acc) ->
              ('env -> 'b -> 'acc) ->
              'env ->
              'a * 'b ->
              'acc =
          fun vx vy env (x, y) ->
            let acc = vx env x in
            let acc' = vy env y in
            let acc = self#plus acc acc' in
            acc

        method visit_tuple3
            : 'a 'b 'c.
              ('env -> 'a -> 'acc) ->
              ('env -> 'b -> 'acc) ->
              ('env -> 'c -> 'acc) ->
              'env ->
              'a * 'b * 'c ->
              'acc =
          fun vx vy vz env (x, y, z) ->
            let acc = vx env x in
            let acc' = vy env y in
            let acc = self#plus acc acc' in
            let acc' = vz env z in
            let acc = self#plus acc acc' in
            acc

        method visit_mutability
            : 'a. ('env -> 'a -> 'acc) -> 'env -> 'a mutability -> 'acc =
          fun v env this -> self#zero

        method visit_todo : 'env -> todo -> 'acc = fun _ _ -> self#zero
        method visit_string : 'env -> string -> 'acc = fun _ _ -> self#zero
        method visit_span : 'env -> span -> 'acc = fun _ _ -> self#zero

        method visit_local_ident : 'env -> local_ident -> 'acc =
          fun _ _ -> self#zero

        method visit_global_ident : 'env -> global_ident -> 'acc =
          fun _ _ -> self#zero

        method visit_concrete_ident : 'env -> concrete_ident -> 'acc =
          fun _ _ -> self#zero

        method visit_char : 'env -> char -> 'acc = fun _ _ -> self#zero
        method visit_bool : 'env -> bool -> 'acc = fun _ _ -> self#zero
        method visit_int_kind : 'env -> int_kind -> 'acc = fun _ _ -> self#zero

        method visit_float_kind : 'env -> float_kind -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_mutable_reference
            : 'env -> F.mutable_reference -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_reference : 'env -> F.reference -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_slice : 'env -> F.slice -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_raw_pointer : 'env -> F.raw_pointer -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_lifetime : 'env -> F.lifetime -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_mutable_variable
            : 'env -> F.mutable_variable -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_as_pattern : 'env -> F.as_pattern -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_construct_base : 'env -> F.construct_base -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_monadic_binding : 'env -> F.monadic_binding -> 'acc
            =
          fun _ _ -> self#zero

        method visit_feature_block : 'env -> F.block -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_macro : 'env -> F.macro -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_loop : 'env -> F.loop -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_break : 'env -> F.break -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_early_exit : 'env -> F.early_exit -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_question_mark : 'env -> F.question_mark -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_state_passing_loop
            : 'env -> F.state_passing_loop -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_continue : 'env -> F.continue -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_mutable_pointer : 'env -> F.mutable_pointer -> 'acc
            =
          fun _ _ -> self#zero

        method visit_feature_monadic_action : 'env -> F.monadic_action -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_while_loop : 'env -> F.while_loop -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_for_loop : 'env -> F.for_loop -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_for_index_loop : 'env -> F.for_index_loop -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_arbitrary_lhs : 'env -> F.arbitrary_lhs -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_nontrivial_lhs : 'env -> F.nontrivial_lhs -> 'acc =
          fun _ _ -> self#zero

        method visit_feature_quote : 'env -> F.quote -> 'acc =
          fun _ _ -> self#zero
      end
  end
