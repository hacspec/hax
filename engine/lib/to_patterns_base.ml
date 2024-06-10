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

    class virtual ['self] pattern_printer =
      object (self : 'self)
        method of_prim___tuple_2
            : 't0 't1. ('t0 -> string) -> ('t1 -> string) -> 't0 * 't1 -> string
            =
          fun of_'t0 of_'t1 v ->
            match v with
            | x0, x1 -> "" ^ "(" ^ of_'t0 x0 ^ ", " ^ of_'t1 x1 ^ ")"

        method of_prim___tuple_3
            : 't0 't1 't2.
              ('t0 -> string) ->
              ('t1 -> string) ->
              ('t2 -> string) ->
              't0 * 't1 * 't2 ->
              string =
          fun of_'t0 of_'t1 of_'t2 v ->
            match v with
            | x0, x1, x2 ->
                "" ^ "(" ^ of_'t0 x0 ^ ", " ^ of_'t1 x1 ^ ", " ^ of_'t2 x2 ^ ")"

        method of_prim___tuple_4
            : 't0 't1 't2 't3.
              ('t0 -> string) ->
              ('t1 -> string) ->
              ('t2 -> string) ->
              ('t3 -> string) ->
              't0 * 't1 * 't2 * 't3 ->
              string =
          fun of_'t0 of_'t1 of_'t2 of_'t3 v ->
            match v with
            | x0, x1, x2, x3 ->
                "" ^ "(" ^ of_'t0 x0 ^ ", " ^ of_'t1 x1 ^ ", " ^ of_'t2 x2
                ^ ", " ^ of_'t3 x3 ^ ")"

        method of_option : 'a. ('a -> string) -> 'a option -> string =
          fun of_'a v ->
            match v with
            | Some x0 -> "Some" ^ "(" ^ of_'a x0 ^ ")"
            | None -> "None"

        method of_attr_kind : attr_kind -> string =
          fun v ->
            match v with
            | Tool payload ->
                "Tool" ^ "{ " ^ "path = "
                ^ self#of_string payload.path
                ^ "; " ^ "tokens = "
                ^ self#of_string payload.tokens
                ^ "; " ^ " }"
            | DocComment payload ->
                "DocComment" ^ "{ " ^ "kind = "
                ^ self#of_doc_comment_kind payload.kind
                ^ "; " ^ "body = "
                ^ self#of_string payload.body
                ^ "; " ^ " }"

        method of_attr : attr -> string =
          fun v ->
            "{ " ^ "kind = " ^ self#of_attr_kind v.kind ^ "; " ^ "span = "
            ^ self#of_span v.span ^ "; " ^ " }"

        method of_doc_comment_kind : doc_comment_kind -> string =
          fun v -> match v with DCKLine -> "DCKLine" | DCKBlock -> "DCKBlock"

        method of_attrs : attrs -> string =
          fun v -> (self#of_list self#of_attr) v

        method of_size : size -> string =
          fun v ->
            match v with
            | S8 -> "S8"
            | S16 -> "S16"
            | S32 -> "S32"
            | S64 -> "S64"
            | S128 -> "S128"
            | SSize -> "SSize"

        method of_signedness : signedness -> string =
          fun v -> match v with Signed -> "Signed" | Unsigned -> "Unsigned"

        method of_int_kind : int_kind -> string =
          fun v ->
            "{ " ^ "size = " ^ self#of_size v.size ^ "; " ^ "signedness = "
            ^ self#of_signedness v.signedness
            ^ "; " ^ " }"

        method of_float_kind : float_kind -> string =
          fun v -> match v with F32 -> "F32" | F64 -> "F64"

        method of_literal : literal -> string =
          fun v ->
            match v with
            | String x0 -> "String" ^ "(" ^ self#of_string x0 ^ ")"
            | Char x0 -> "Char" ^ "(" ^ self#of_char x0 ^ ")"
            | Int payload ->
                "Int" ^ "{ " ^ "value = "
                ^ self#of_string payload.value
                ^ "; " ^ "negative = "
                ^ self#of_bool payload.negative
                ^ "; " ^ "kind = "
                ^ self#of_int_kind payload.kind
                ^ "; " ^ " }"
            | Float payload ->
                "Float" ^ "{ " ^ "value = "
                ^ self#of_string payload.value
                ^ "; " ^ "negative = "
                ^ self#of_bool payload.negative
                ^ "; " ^ "kind = "
                ^ self#of_float_kind payload.kind
                ^ "; " ^ " }"
            | Bool x0 -> "Bool" ^ "(" ^ self#of_bool x0 ^ ")"

        method of_mutability
            : 'mut_witness.
              ('mut_witness -> string) -> 'mut_witness mutability -> string =
          fun of_'mut_witness v ->
            match v with
            | Mutable x0 -> "Mutable" ^ "(" ^ of_'mut_witness x0 ^ ")"
            | Immutable -> "Immutable"

        method of_borrow_kind : borrow_kind -> string =
          fun v ->
            match v with
            | Shared -> "Shared"
            | Unique -> "Unique"
            | Mut x0 -> "Mut" ^ "(" ^ self#of_F__mutable_reference x0 ^ ")"

        method of_binding_mode : binding_mode -> string =
          fun v ->
            match v with
            | ByValue -> "ByValue"
            | ByRef (x0, x1) ->
                "ByRef" ^ "(" ^ self#of_borrow_kind x0 ^ ", "
                ^ self#of_F__reference x1 ^ ")"

        method of_ty : ty -> string =
          fun v ->
            match v with
            | TBool -> "TBool"
            | TChar -> "TChar"
            | TInt x0 -> "TInt" ^ "(" ^ self#of_int_kind x0 ^ ")"
            | TFloat x0 -> "TFloat" ^ "(" ^ self#of_float_kind x0 ^ ")"
            | TStr -> "TStr"
            | TApp payload ->
                "TApp" ^ "{ " ^ "ident = "
                ^ self#of_global_ident payload.ident
                ^ "; " ^ "args = "
                ^ (self#of_list self#of_generic_value) payload.args
                ^ "; " ^ " }"
            | TArray payload ->
                "TArray" ^ "{ " ^ "typ = " ^ self#of_ty payload.typ ^ "; "
                ^ "length = "
                ^ self#of_expr payload.length
                ^ "; " ^ " }"
            | TSlice payload ->
                "TSlice" ^ "{ " ^ "witness = "
                ^ self#of_F__slice payload.witness
                ^ "; " ^ "ty = " ^ self#of_ty payload.ty ^ "; " ^ " }"
            | TRawPointer payload ->
                "TRawPointer" ^ "{ " ^ "witness = "
                ^ self#of_F__raw_pointer payload.witness
                ^ "; " ^ " }"
            | TRef payload ->
                "TRef" ^ "{ " ^ "witness = "
                ^ self#of_F__reference payload.witness
                ^ "; " ^ "region = "
                ^ self#of_todo payload.region
                ^ "; " ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ "mut = "
                ^ (self#of_mutability self#of_F__mutable_reference) payload.mut
                ^ "; " ^ " }"
            | TParam x0 -> "TParam" ^ "(" ^ self#of_local_ident x0 ^ ")"
            | TArrow (x0, x1) ->
                "TArrow" ^ "("
                ^ (self#of_list self#of_ty) x0
                ^ ", " ^ self#of_ty x1 ^ ")"
            | TAssociatedType payload ->
                "TAssociatedType" ^ "{ " ^ "impl = "
                ^ self#of_impl_expr payload.impl
                ^ "; " ^ "item = "
                ^ self#of_concrete_ident payload.item
                ^ "; " ^ " }"
            | TOpaque x0 -> "TOpaque" ^ "(" ^ self#of_concrete_ident x0 ^ ")"

        method of_generic_value : generic_value -> string =
          fun v ->
            match v with
            | GLifetime payload ->
                "GLifetime" ^ "{ " ^ "lt = " ^ self#of_todo payload.lt ^ "; "
                ^ "witness = "
                ^ self#of_F__lifetime payload.witness
                ^ "; " ^ " }"
            | GType x0 -> "GType" ^ "(" ^ self#of_ty x0 ^ ")"
            | GConst x0 -> "GConst" ^ "(" ^ self#of_expr x0 ^ ")"

        method of_impl_expr : impl_expr -> string =
          fun v ->
            match v with
            | Self -> "Self"
            | Concrete x0 -> "Concrete" ^ "(" ^ self#of_trait_goal x0 ^ ")"
            | LocalBound payload ->
                "LocalBound" ^ "{ " ^ "id = " ^ self#of_string payload.id ^ "; "
                ^ " }"
            | Parent payload ->
                "Parent" ^ "{ " ^ "impl = "
                ^ self#of_impl_expr payload.impl
                ^ "; " ^ "ident = "
                ^ self#of_impl_ident payload.ident
                ^ "; " ^ " }"
            | Projection payload ->
                "Projection" ^ "{ " ^ "impl = "
                ^ self#of_impl_expr payload.impl
                ^ "; " ^ "item = "
                ^ self#of_concrete_ident payload.item
                ^ "; " ^ "ident = "
                ^ self#of_impl_ident payload.ident
                ^ "; " ^ " }"
            | ImplApp payload ->
                "ImplApp" ^ "{ " ^ "impl = "
                ^ self#of_impl_expr payload.impl
                ^ "; " ^ "args = "
                ^ (self#of_list self#of_impl_expr) payload.args
                ^ "; " ^ " }"
            | Dyn -> "Dyn"
            | Builtin x0 -> "Builtin" ^ "(" ^ self#of_trait_goal x0 ^ ")"

        method of_trait_goal : trait_goal -> string =
          fun v ->
            "{ " ^ "trait = "
            ^ self#of_concrete_ident v.trait
            ^ "; " ^ "args = "
            ^ (self#of_list self#of_generic_value) v.args
            ^ "; " ^ " }"

        method of_impl_ident : impl_ident -> string =
          fun v ->
            "{ " ^ "goal = " ^ self#of_trait_goal v.goal ^ "; " ^ "name = "
            ^ self#of_string v.name ^ "; " ^ " }"

        method of_pat' : pat' -> string =
          fun v ->
            match v with
            | PWild -> "PWild"
            | PAscription payload ->
                "PAscription" ^ "{ " ^ "typ = " ^ self#of_ty payload.typ ^ "; "
                ^ "typ_span = "
                ^ self#of_span payload.typ_span
                ^ "; " ^ "pat = " ^ self#of_pat payload.pat ^ "; " ^ " }"
            | PConstruct payload ->
                "PConstruct" ^ "{ " ^ "name = "
                ^ self#of_global_ident payload.name
                ^ "; " ^ "args = "
                ^ (self#of_list self#of_field_pat) payload.args
                ^ "; " ^ "is_record = "
                ^ self#of_bool payload.is_record
                ^ "; " ^ "is_struct = "
                ^ self#of_bool payload.is_struct
                ^ "; " ^ " }"
            | POr payload ->
                "POr" ^ "{ " ^ "subpats = "
                ^ (self#of_list self#of_pat) payload.subpats
                ^ "; " ^ " }"
            | PArray payload ->
                "PArray" ^ "{ " ^ "args = "
                ^ (self#of_list self#of_pat) payload.args
                ^ "; " ^ " }"
            | PDeref payload ->
                "PDeref" ^ "{ " ^ "subpat = " ^ self#of_pat payload.subpat
                ^ "; " ^ "witness = "
                ^ self#of_F__reference payload.witness
                ^ "; " ^ " }"
            | PConstant payload ->
                "PConstant" ^ "{ " ^ "lit = "
                ^ self#of_literal payload.lit
                ^ "; " ^ " }"
            | PBinding payload ->
                "PBinding" ^ "{ " ^ "mut = "
                ^ (self#of_mutability self#of_F__mutable_variable) payload.mut
                ^ "; " ^ "mode = "
                ^ self#of_binding_mode payload.mode
                ^ "; " ^ "var = "
                ^ self#of_local_ident payload.var
                ^ "; " ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ "subpat = "
                ^ (self#of_option
                     (self#of_prim___tuple_2 self#of_pat self#of_F__as_pattern))
                    payload.subpat
                ^ "; " ^ " }"

        method of_pat : pat -> string =
          fun v ->
            "{ " ^ "p = " ^ self#of_pat' v.p ^ "; " ^ "span = "
            ^ self#of_span v.span ^ "; " ^ "typ = " ^ self#of_ty v.typ ^ "; "
            ^ " }"

        method of_field_pat : field_pat -> string =
          fun v ->
            "{ " ^ "field = "
            ^ self#of_global_ident v.field
            ^ "; " ^ "pat = " ^ self#of_pat v.pat ^ "; " ^ " }"

        method of_expr' : expr' -> string =
          fun v ->
            match v with
            | If payload ->
                "If" ^ "{ " ^ "cond = " ^ self#of_expr payload.cond ^ "; "
                ^ "then_ = " ^ self#of_expr payload.then_ ^ "; " ^ "else_ = "
                ^ (self#of_option self#of_expr) payload.else_
                ^ "; " ^ " }"
            | App payload ->
                "App" ^ "{ " ^ "f = " ^ self#of_expr payload.f ^ "; "
                ^ "args = "
                ^ (self#of_list self#of_expr) payload.args
                ^ "; " ^ "generic_args = "
                ^ (self#of_list self#of_generic_value) payload.generic_args
                ^ "; " ^ "bounds_impls = "
                ^ (self#of_list self#of_impl_expr) payload.bounds_impls
                ^ "; " ^ "impl = "
                ^ (self#of_option self#of_impl_expr) payload.impl
                ^ "; " ^ " }"
            | Literal x0 -> "Literal" ^ "(" ^ self#of_literal x0 ^ ")"
            | Array x0 -> "Array" ^ "(" ^ (self#of_list self#of_expr) x0 ^ ")"
            | Construct payload ->
                "Construct" ^ "{ " ^ "constructor = "
                ^ self#of_global_ident payload.constructor
                ^ "; " ^ "is_record = "
                ^ self#of_bool payload.is_record
                ^ "; " ^ "is_struct = "
                ^ self#of_bool payload.is_struct
                ^ "; " ^ "fields = "
                ^ (self#of_list
                     (self#of_prim___tuple_2 self#of_global_ident self#of_expr))
                    payload.fields
                ^ "; " ^ "base = "
                ^ (self#of_option
                     (self#of_prim___tuple_2 self#of_expr
                        self#of_F__construct_base))
                    payload.base
                ^ "; " ^ " }"
            | Match payload ->
                "Match" ^ "{ " ^ "scrutinee = "
                ^ self#of_expr payload.scrutinee
                ^ "; " ^ "arms = "
                ^ (self#of_list self#of_arm) payload.arms
                ^ "; " ^ " }"
            | Let payload ->
                "Let" ^ "{ " ^ "monadic = "
                ^ (self#of_option
                     (self#of_prim___tuple_2 self#of_supported_monads
                        self#of_F__monadic_binding))
                    payload.monadic
                ^ "; " ^ "lhs = " ^ self#of_pat payload.lhs ^ "; " ^ "rhs = "
                ^ self#of_expr payload.rhs ^ "; " ^ "body = "
                ^ self#of_expr payload.body ^ "; " ^ " }"
            | Block (x0, x1) ->
                "Block" ^ "(" ^ self#of_expr x0 ^ ", " ^ self#of_F__block x1
                ^ ")"
            | LocalVar x0 -> "LocalVar" ^ "(" ^ self#of_local_ident x0 ^ ")"
            | GlobalVar x0 -> "GlobalVar" ^ "(" ^ self#of_global_ident x0 ^ ")"
            | Ascription payload ->
                "Ascription" ^ "{ " ^ "e = " ^ self#of_expr payload.e ^ "; "
                ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ " }"
            | MacroInvokation payload ->
                "MacroInvokation" ^ "{ " ^ "macro = "
                ^ self#of_global_ident payload.macro
                ^ "; " ^ "args = "
                ^ self#of_string payload.args
                ^ "; " ^ "witness = "
                ^ self#of_F__macro payload.witness
                ^ "; " ^ " }"
            | Assign payload ->
                "Assign" ^ "{ " ^ "lhs = " ^ self#of_lhs payload.lhs ^ "; "
                ^ "e = " ^ self#of_expr payload.e ^ "; " ^ "witness = "
                ^ self#of_F__mutable_variable payload.witness
                ^ "; " ^ " }"
            | Loop payload ->
                "Loop" ^ "{ " ^ "body = " ^ self#of_expr payload.body ^ "; "
                ^ "kind = "
                ^ self#of_loop_kind payload.kind
                ^ "; " ^ "state = "
                ^ (self#of_option self#of_loop_state) payload.state
                ^ "; " ^ "label = "
                ^ (self#of_option self#of_string) payload.label
                ^ "; " ^ "witness = "
                ^ self#of_F__loop payload.witness
                ^ "; " ^ " }"
            | Break payload ->
                "Break" ^ "{ " ^ "e = " ^ self#of_expr payload.e ^ "; "
                ^ "label = "
                ^ (self#of_option self#of_string) payload.label
                ^ "; " ^ "witness = "
                ^ (self#of_prim___tuple_2 self#of_F__break self#of_F__loop)
                    payload.witness
                ^ "; " ^ " }"
            | Return payload ->
                "Return" ^ "{ " ^ "e = " ^ self#of_expr payload.e ^ "; "
                ^ "witness = "
                ^ self#of_F__early_exit payload.witness
                ^ "; " ^ " }"
            | QuestionMark payload ->
                "QuestionMark" ^ "{ " ^ "e = " ^ self#of_expr payload.e ^ "; "
                ^ "return_typ = "
                ^ self#of_ty payload.return_typ
                ^ "; " ^ "witness = "
                ^ self#of_F__question_mark payload.witness
                ^ "; " ^ " }"
            | Continue payload ->
                "Continue" ^ "{ " ^ "e = "
                ^ (self#of_option
                     (self#of_prim___tuple_2 self#of_F__state_passing_loop
                        self#of_expr))
                    payload.e
                ^ "; " ^ "label = "
                ^ (self#of_option self#of_string) payload.label
                ^ "; " ^ "witness = "
                ^ (self#of_prim___tuple_2 self#of_F__continue self#of_F__loop)
                    payload.witness
                ^ "; " ^ " }"
            | Borrow payload ->
                "Borrow" ^ "{ " ^ "kind = "
                ^ self#of_borrow_kind payload.kind
                ^ "; " ^ "e = " ^ self#of_expr payload.e ^ "; " ^ "witness = "
                ^ self#of_F__reference payload.witness
                ^ "; " ^ " }"
            | AddressOf payload ->
                "AddressOf" ^ "{ " ^ "mut = "
                ^ (self#of_mutability self#of_F__mutable_pointer) payload.mut
                ^ "; " ^ "e = " ^ self#of_expr payload.e ^ "; " ^ "witness = "
                ^ self#of_F__raw_pointer payload.witness
                ^ "; " ^ " }"
            | Closure payload ->
                "Closure" ^ "{ " ^ "params = "
                ^ (self#of_list self#of_pat) payload.params
                ^ "; " ^ "body = " ^ self#of_expr payload.body ^ "; "
                ^ "captures = "
                ^ (self#of_list self#of_expr) payload.captures
                ^ "; " ^ " }"
            | EffectAction payload ->
                "EffectAction" ^ "{ " ^ "action = "
                ^ self#of_F__monadic_action payload.action
                ^ "; " ^ "argument = "
                ^ self#of_expr payload.argument
                ^ "; " ^ " }"
            | Quote x0 -> "Quote" ^ "(" ^ self#of_quote x0 ^ ")"

        method of_expr : expr -> string =
          fun v ->
            "{ " ^ "e = " ^ self#of_expr' v.e ^ "; " ^ "span = "
            ^ self#of_span v.span ^ "; " ^ "typ = " ^ self#of_ty v.typ ^ "; "
            ^ " }"

        method of_supported_monads : supported_monads -> string =
          fun v ->
            match v with
            | MException x0 -> "MException" ^ "(" ^ self#of_ty x0 ^ ")"
            | MResult x0 -> "MResult" ^ "(" ^ self#of_ty x0 ^ ")"
            | MOption -> "MOption"

        method of_loop_kind : loop_kind -> string =
          fun v ->
            match v with
            | UnconditionalLoop -> "UnconditionalLoop"
            | WhileLoop payload ->
                "WhileLoop" ^ "{ " ^ "condition = "
                ^ self#of_expr payload.condition
                ^ "; " ^ "witness = "
                ^ self#of_F__while_loop payload.witness
                ^ "; " ^ " }"
            | ForLoop payload ->
                "ForLoop" ^ "{ " ^ "pat = " ^ self#of_pat payload.pat ^ "; "
                ^ "it = " ^ self#of_expr payload.it ^ "; " ^ "witness = "
                ^ self#of_F__for_loop payload.witness
                ^ "; " ^ " }"
            | ForIndexLoop payload ->
                "ForIndexLoop" ^ "{ " ^ "start = " ^ self#of_expr payload.start
                ^ "; " ^ "end_ = " ^ self#of_expr payload.end_ ^ "; " ^ "var = "
                ^ self#of_local_ident payload.var
                ^ "; " ^ "var_typ = " ^ self#of_ty payload.var_typ ^ "; "
                ^ "witness = "
                ^ self#of_F__for_index_loop payload.witness
                ^ "; " ^ " }"

        method of_loop_state : loop_state -> string =
          fun v ->
            "{ " ^ "init = " ^ self#of_expr v.init ^ "; " ^ "bpat = "
            ^ self#of_pat v.bpat ^ "; " ^ "witness = "
            ^ self#of_F__state_passing_loop v.witness
            ^ "; " ^ " }"

        method of_lhs : lhs -> string =
          fun v ->
            match v with
            | LhsLocalVar payload ->
                "LhsLocalVar" ^ "{ " ^ "var = "
                ^ self#of_Local_ident__t payload.var
                ^ "; " ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ " }"
            | LhsArbitraryExpr payload ->
                "LhsArbitraryExpr" ^ "{ " ^ "e = " ^ self#of_expr payload.e
                ^ "; " ^ "witness = "
                ^ self#of_F__arbitrary_lhs payload.witness
                ^ "; " ^ " }"
            | LhsFieldAccessor payload ->
                "LhsFieldAccessor" ^ "{ " ^ "e = " ^ self#of_lhs payload.e
                ^ "; " ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ "field = "
                ^ self#of_global_ident payload.field
                ^ "; " ^ "witness = "
                ^ self#of_F__nontrivial_lhs payload.witness
                ^ "; " ^ " }"
            | LhsArrayAccessor payload ->
                "LhsArrayAccessor" ^ "{ " ^ "e = " ^ self#of_lhs payload.e
                ^ "; " ^ "typ = " ^ self#of_ty payload.typ ^ "; " ^ "index = "
                ^ self#of_expr payload.index ^ "; " ^ "witness = "
                ^ self#of_F__nontrivial_lhs payload.witness
                ^ "; " ^ " }"

        method of_arm' : arm' -> string =
          fun v ->
            "{ " ^ "arm_pat = " ^ self#of_pat v.arm_pat ^ "; " ^ "body = "
            ^ self#of_expr v.body ^ "; " ^ " }"

        method of_arm : arm -> string =
          fun v ->
            "{ " ^ "arm = " ^ self#of_arm' v.arm ^ "; " ^ "span = "
            ^ self#of_span v.span ^ "; " ^ " }"

        method of_generic_param : generic_param -> string =
          fun v ->
            "{ " ^ "ident = "
            ^ self#of_local_ident v.ident
            ^ "; " ^ "span = " ^ self#of_span v.span ^ "; " ^ "attrs = "
            ^ self#of_attrs v.attrs ^ "; " ^ "kind = "
            ^ self#of_generic_param_kind v.kind
            ^ "; " ^ " }"

        method of_generic_param_kind : generic_param_kind -> string =
          fun v ->
            match v with
            | GPLifetime payload ->
                "GPLifetime" ^ "{ " ^ "witness = "
                ^ self#of_F__lifetime payload.witness
                ^ "; " ^ " }"
            | GPType payload ->
                "GPType" ^ "{ " ^ "default = "
                ^ (self#of_option self#of_ty) payload.default
                ^ "; " ^ " }"
            | GPConst payload ->
                "GPConst" ^ "{ " ^ "typ = " ^ self#of_ty payload.typ ^ "; "
                ^ " }"

        method of_generic_constraint : generic_constraint -> string =
          fun v ->
            match v with
            | GCLifetime (x0, x1) ->
                "GCLifetime" ^ "(" ^ self#of_todo x0 ^ ", "
                ^ self#of_F__lifetime x1 ^ ")"
            | GCType x0 -> "GCType" ^ "(" ^ self#of_impl_ident x0 ^ ")"

        method of_param : param -> string =
          fun v ->
            "{ " ^ "pat = " ^ self#of_pat v.pat ^ "; " ^ "typ = "
            ^ self#of_ty v.typ ^ "; " ^ "typ_span = "
            ^ (self#of_option self#of_span) v.typ_span
            ^ "; " ^ "attrs = " ^ self#of_attrs v.attrs ^ "; " ^ " }"

        method of_generics : generics -> string =
          fun v ->
            "{ " ^ "params = "
            ^ (self#of_list self#of_generic_param) v.params
            ^ "; " ^ "constraints = "
            ^ (self#of_list self#of_generic_constraint) v.constraints
            ^ "; " ^ " }"

        method of_variant : variant -> string =
          fun v ->
            "{ " ^ "name = "
            ^ self#of_concrete_ident v.name
            ^ "; " ^ "arguments = "
            ^ (self#of_list
                 (self#of_prim___tuple_3 self#of_concrete_ident self#of_ty
                    self#of_attrs))
                v.arguments
            ^ "; " ^ "is_record = " ^ self#of_bool v.is_record ^ "; "
            ^ "attrs = " ^ self#of_attrs v.attrs ^ "; " ^ " }"

        method of_item' : item' -> string =
          fun v ->
            match v with
            | Fn payload ->
                "Fn" ^ "{ " ^ "name = "
                ^ self#of_concrete_ident payload.name
                ^ "; " ^ "generics = "
                ^ self#of_generics payload.generics
                ^ "; " ^ "body = " ^ self#of_expr payload.body ^ "; "
                ^ "params = "
                ^ (self#of_list self#of_param) payload.params
                ^ "; " ^ " }"
            | TyAlias payload ->
                "TyAlias" ^ "{ " ^ "name = "
                ^ self#of_concrete_ident payload.name
                ^ "; " ^ "generics = "
                ^ self#of_generics payload.generics
                ^ "; " ^ "ty = " ^ self#of_ty payload.ty ^ "; " ^ " }"
            | Type payload ->
                "Type" ^ "{ " ^ "name = "
                ^ self#of_concrete_ident payload.name
                ^ "; " ^ "generics = "
                ^ self#of_generics payload.generics
                ^ "; " ^ "variants = "
                ^ (self#of_list self#of_variant) payload.variants
                ^ "; " ^ "is_struct = "
                ^ self#of_bool payload.is_struct
                ^ "; " ^ " }"
            | IMacroInvokation payload ->
                "IMacroInvokation" ^ "{ " ^ "macro = "
                ^ self#of_concrete_ident payload.macro
                ^ "; " ^ "argument = "
                ^ self#of_string payload.argument
                ^ "; " ^ "span = " ^ self#of_span payload.span ^ "; "
                ^ "witness = "
                ^ self#of_F__macro payload.witness
                ^ "; " ^ " }"
            | Trait payload ->
                "Trait" ^ "{ " ^ "name = "
                ^ self#of_concrete_ident payload.name
                ^ "; " ^ "generics = "
                ^ self#of_generics payload.generics
                ^ "; " ^ "items = "
                ^ (self#of_list self#of_trait_item) payload.items
                ^ "; " ^ " }"
            | Impl payload ->
                "Impl" ^ "{ " ^ "generics = "
                ^ self#of_generics payload.generics
                ^ "; " ^ "self_ty = " ^ self#of_ty payload.self_ty ^ "; "
                ^ "of_trait = "
                ^ (self#of_prim___tuple_2 self#of_global_ident
                     (self#of_list self#of_generic_value))
                    payload.of_trait
                ^ "; " ^ "items = "
                ^ (self#of_list self#of_impl_item) payload.items
                ^ "; " ^ "parent_bounds = "
                ^ (self#of_list
                     (self#of_prim___tuple_2 self#of_impl_expr
                        self#of_impl_ident))
                    payload.parent_bounds
                ^ "; " ^ " }"
            | Alias payload ->
                "Alias" ^ "{ " ^ "name = "
                ^ self#of_concrete_ident payload.name
                ^ "; " ^ "item = "
                ^ self#of_concrete_ident payload.item
                ^ "; " ^ " }"
            | Use payload ->
                "Use" ^ "{ " ^ "path = "
                ^ (self#of_list self#of_string) payload.path
                ^ "; " ^ "is_external = "
                ^ self#of_bool payload.is_external
                ^ "; " ^ "rename = "
                ^ (self#of_option self#of_string) payload.rename
                ^ "; " ^ " }"
            | Quote x0 -> "Quote" ^ "(" ^ self#of_quote x0 ^ ")"
            | HaxError x0 -> "HaxError" ^ "(" ^ self#of_string x0 ^ ")"
            | NotImplementedYet -> "NotImplementedYet"

        method of_item : item -> string =
          fun v ->
            "{ " ^ "v = " ^ self#of_item' v.v ^ "; " ^ "span = "
            ^ self#of_span v.span ^ "; " ^ "ident = "
            ^ self#of_concrete_ident v.ident
            ^ "; " ^ "attrs = " ^ self#of_attrs v.attrs ^ "; " ^ " }"

        method of_impl_item' : impl_item' -> string =
          fun v ->
            match v with
            | IIType payload ->
                "IIType" ^ "{ " ^ "typ = " ^ self#of_ty payload.typ ^ "; "
                ^ "parent_bounds = "
                ^ (self#of_list
                     (self#of_prim___tuple_2 self#of_impl_expr
                        self#of_impl_ident))
                    payload.parent_bounds
                ^ "; " ^ " }"
            | IIFn payload ->
                "IIFn" ^ "{ " ^ "body = " ^ self#of_expr payload.body ^ "; "
                ^ "params = "
                ^ (self#of_list self#of_param) payload.params
                ^ "; " ^ " }"

        method of_impl_item : impl_item -> string =
          fun v ->
            "{ " ^ "ii_span = " ^ self#of_span v.ii_span ^ "; "
            ^ "ii_generics = "
            ^ self#of_generics v.ii_generics
            ^ "; " ^ "ii_v = " ^ self#of_impl_item' v.ii_v ^ "; "
            ^ "ii_ident = "
            ^ self#of_concrete_ident v.ii_ident
            ^ "; " ^ "ii_attrs = " ^ self#of_attrs v.ii_attrs ^ "; " ^ " }"

        method of_trait_item' : trait_item' -> string =
          fun v ->
            match v with
            | TIType x0 ->
                "TIType" ^ "(" ^ (self#of_list self#of_impl_ident) x0 ^ ")"
            | TIFn x0 -> "TIFn" ^ "(" ^ self#of_ty x0 ^ ")"

        method of_trait_item : trait_item -> string =
          fun v ->
            "{ " ^ "ti_span = " ^ self#of_span v.ti_span ^ "; "
            ^ "ti_generics = "
            ^ self#of_generics v.ti_generics
            ^ "; " ^ "ti_v = " ^ self#of_trait_item' v.ti_v ^ "; "
            ^ "ti_ident = "
            ^ self#of_concrete_ident v.ti_ident
            ^ "; " ^ "ti_attrs = " ^ self#of_attrs v.ti_attrs ^ "; " ^ " }"

        method of_modul : modul -> string =
          fun v -> (self#of_list self#of_item) v

        method of_F__arbitrary_lhs : F.arbitrary_lhs -> string =
          fun v -> self#generic_of_feature "arbitrary_lhs"

        method of_F__as_pattern : F.as_pattern -> string =
          fun v -> self#generic_of_feature "as_pattern"

        method of_F__block : F.block -> string =
          fun v -> self#generic_of_feature "block"

        method of_F__break : F.break -> string =
          fun v -> self#generic_of_feature "break"

        method of_F__construct_base : F.construct_base -> string =
          fun v -> self#generic_of_feature "construct_base"

        method of_F__continue : F.continue -> string =
          fun v -> self#generic_of_feature "continue"

        method of_F__early_exit : F.early_exit -> string =
          fun v -> self#generic_of_feature "early_exit"

        method of_F__for_index_loop : F.for_index_loop -> string =
          fun v -> self#generic_of_feature "for_index_loop"

        method of_F__for_loop : F.for_loop -> string =
          fun v -> self#generic_of_feature "for_loop"

        method of_F__lifetime : F.lifetime -> string =
          fun v -> self#generic_of_feature "lifetime"

        method of_F__loop : F.loop -> string =
          fun v -> self#generic_of_feature "loop"

        method of_F__macro : F.macro -> string =
          fun v -> self#generic_of_feature "macro"

        method of_F__monadic_action : F.monadic_action -> string =
          fun v -> self#generic_of_feature "monadic_action"

        method of_F__monadic_binding : F.monadic_binding -> string =
          fun v -> self#generic_of_feature "monadic_binding"

        method of_F__mutable_pointer : F.mutable_pointer -> string =
          fun v -> self#generic_of_feature "mutable_pointer"

        method of_F__mutable_reference : F.mutable_reference -> string =
          fun v -> self#generic_of_feature "mutable_reference"

        method of_F__mutable_variable : F.mutable_variable -> string =
          fun v -> self#generic_of_feature "mutable_variable"

        method of_F__nontrivial_lhs : F.nontrivial_lhs -> string =
          fun v -> self#generic_of_feature "nontrivial_lhs"

        method of_F__question_mark : F.question_mark -> string =
          fun v -> self#generic_of_feature "question_mark"

        method of_F__raw_pointer : F.raw_pointer -> string =
          fun v -> self#generic_of_feature "raw_pointer"

        method of_F__reference : F.reference -> string =
          fun v -> self#generic_of_feature "reference"

        method of_F__slice : F.slice -> string =
          fun v -> self#generic_of_feature "slice"

        method of_F__state_passing_loop : F.state_passing_loop -> string =
          fun v -> self#generic_of_feature "state_passing_loop"

        method of_F__while_loop : F.while_loop -> string =
          fun v -> self#generic_of_feature "while_loop"

        method of_Local_ident__t : Local_ident.t -> string =
          fun v -> self#mk_unique_wildcard "of_Local_ident__t"

        method of_concrete_ident : concrete_ident -> string =
          fun v -> self#mk_unique_wildcard "of_concrete_ident"

        method of_global_ident : global_ident -> string =
          fun v -> self#mk_unique_wildcard "of_global_ident"

        method of_local_ident : local_ident -> string =
          fun v -> self#mk_unique_wildcard "of_local_ident"

        method of_quote : quote -> string =
          fun v -> self#mk_unique_wildcard "of_quote"

        method of_span : span -> string =
          fun v -> self#mk_unique_wildcard "of_span"

        method of_list : 'a. ('a -> string) -> 'a list -> string =
          fun f args -> "[" ^ String.concat ~sep:"; " (List.map ~f args) ^ "]"

        val mutable wildcards_state = Base.Hashtbl.create (module String)

        method mk_unique_wildcard (hint : string) : string =
          let f = Option.value ~default:0 >> ( + ) 1 in
          let n = Hashtbl.update_and_return wildcards_state hint ~f in
          "_" ^ hint ^ "_" ^ Int.to_string n

        method generic_of_feature name = "_ (* matches feature " ^ name ^ " *)"
        method of_bool = function true -> "true" | false -> "false"
        method of_char c = Base.String.of_char_list [ '\''; c; '\'' ]

        method of_string s =
          let rec h level =
            let l, r =
              if level < 0 then ("\"", "\"")
              else
                let tag = String.make level 's' in
                ("{" ^ tag ^ "|", "|" ^ tag ^ "}")
            in
            if String.is_substring s ~substring:r then h (level + 1)
            else l ^ s ^ r
          in
          h (-1)

        method of_todo = self#of_string
      end
  end
