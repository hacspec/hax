open! Prelude
open! Ast

module Make (F : Features.T) (View : Concrete_ident.VIEW_API) = struct
  open Generic_printer_base
  open Generic_printer_base.Make (F)

  module Class = struct
    module U = Ast_utils.Make (F)
    open! AST
    open PPrint

    let iblock f = group >> jump 2 0 >> terminate (break 0) >> f >> group

    class print =
      object (print)
        inherit print_base as super
        method printer_name = "Generic"

        method par_state : ast_position -> par_state =
          function
          | Lhs_LhsArrayAccessor | Ty_Tuple | Ty_TSlice | Ty_TArray_length
          | Expr_If_cond | Expr_If_then | Expr_If_else | Expr_Array
          | Expr_Assign | Expr_Closure_param | Expr_Closure_body
          | Expr_Ascription_e | Expr_Let_lhs | Expr_Let_rhs | Expr_Let_body
          | Expr_App_arg | Expr_ConstructTuple | Pat_ConstructTuple | Pat_PArray
          | Pat_Ascription_pat | Param_pat | Item_Fn_body | GenericParam_GPConst
            ->
              AlreadyPar
          | _ -> NeedsPar

        method namespace_of_concrete_ident
            : concrete_ident -> string * string list =
          fun i -> View.to_namespace i

        method concrete_ident' ~(under_current_ns : bool) : concrete_ident fn =
          fun id ->
            let id = View.to_view id in
            let chunks =
              if under_current_ns then [ id.definition ]
              else id.crate :: (id.path @ [ id.definition ])
            in
            separate_map (colon ^^ colon) utf8string chunks

        method name_of_concrete_ident : concrete_ident fn =
          View.to_definition_name >> utf8string

        method mutability : 'a. 'a mutability fn = fun _ -> empty

        method primitive_ident : primitive_ident fn =
          function
          | Deref -> string "deref"
          | Cast -> string "cast"
          | LogicalOp And -> string "and"
          | LogicalOp Or -> string "or"

        method local_ident : local_ident fn = View.local_ident >> utf8string

        method literal : literal_ctx -> literal fn =
          (* TODO : escape *)
          fun _ctx -> function
            | String s -> utf8string s |> dquotes
            | Char c -> char c |> bquotes
            | Int { value; negative; _ } ->
                string value |> precede (if negative then minus else empty)
            | Float { value; kind; negative } ->
                string value
                |> precede (if negative then minus else empty)
                |> terminate
                     (string (match kind with F32 -> "f32" | F64 -> "f64"))
            | Bool b -> OCaml.bool b

        method generic_value : generic_value fn =
          function
          | GLifetime _ -> string "Lifetime"
          | GType ty -> print#ty_at GenericValue_GType ty
          | GConst expr -> print#expr_at GenericValue_GConst expr

        method lhs : lhs fn =
          function
          | LhsLocalVar { var; _ } -> print#local_ident var
          | LhsArbitraryExpr { e; _ } -> print#expr_at Lhs_LhsArbitraryExpr e
          | LhsFieldAccessor { e; field; _ } ->
              print#lhs e |> parens
              |> terminate (dot ^^ print#global_ident_projector field)
          | LhsArrayAccessor { e; index; _ } ->
              print#lhs e |> parens
              |> terminate (print#expr_at Lhs_LhsArrayAccessor index |> brackets)

        method ty_bool : document = string "bool"
        method ty_char : document = string "char"
        method ty_str : document = string "str"

        method ty_int : int_kind fn =
          fun { size; signedness } ->
            let signedness = match signedness with Signed -> "i" | _ -> "u" in
            let size =
              match int_of_size size with
              | Some n -> OCaml.int n
              | None -> string "size"
            in
            string signedness ^^ size

        method ty_float : float_kind fn =
          (function F32 -> "f32" | F64 -> "f64") >> string

        method generic_values : generic_value list fn =
          function
          | [] -> empty
          | values -> separate_map comma print#generic_value values |> angles

        method ty_app : concrete_ident -> generic_value list fn =
          fun f args -> print#concrete_ident f ^^ print#generic_values args

        method ty_tuple : int -> ty list fn =
          fun _n ->
            separate_map (comma ^^ break 1) (print#ty_at Ty_Tuple)
            >> iblock parens

        method! ty : par_state -> ty fn =
          fun ctx ty ->
            match ty with
            | TBool -> string "bool"
            | TChar -> string "char"
            | TInt kind -> print#ty_int kind
            | TFloat kind -> print#ty_float kind
            | TStr -> string "String"
            | TArrow (inputs, output) ->
                separate_map (string "->") (print#ty_at Ty_TArrow)
                  (inputs @ [ output ])
                |> parens
                |> precede (string "arrow!")
            | TRef { typ; mut; _ } ->
                ampersand ^^ print#mutability mut ^^ print#ty_at Ty_TRef typ
            | TParam i -> print#local_ident i
            | TSlice { ty; _ } -> print#ty_at Ty_TSlice ty |> brackets
            | TRawPointer _ -> string "raw_pointer!()"
            | TArray { typ; length } ->
                print#ty_at Ty_TArray_length typ
                ^/^ semi
                ^/^ print#expr_at Ty_TArray_length length
                |> brackets
            | TAssociatedType _ -> string "assoc_type!()"
            | TOpaque _ -> string "opaque_type!()"
            | TApp _ -> super#ty ctx ty

        method! expr' : par_state -> expr' fn =
          fun ctx e ->
            let wrap_parens =
              group
              >>
              match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock braces
            in
            match e with
            | If { cond; then_; else_ } ->
                let if_then =
                  (string "if" ^//^ nest 2 (print#expr_at Expr_If_cond cond))
                  ^/^ string "then"
                  ^//^ (print#expr_at Expr_If_then then_ |> braces |> nest 1)
                in
                (match else_ with
                | None -> if_then
                | Some else_ ->
                    if_then ^^ break 1 ^^ string "else" ^^ space
                    ^^ (print#expr_at Expr_If_else else_ |> iblock braces))
                |> wrap_parens
            | Match { scrutinee; arms } ->
                let header =
                  string "match" ^^ space
                  ^^ (print#expr_at Expr_Match_scrutinee scrutinee
                     |> terminate space |> iblock Fn.id)
                  |> group
                in
                let arms =
                  separate_map hardline
                    (print#arm >> group >> nest 2
                    >> precede (bar ^^ space)
                    >> group)
                    arms
                in
                header ^^ iblock braces arms
            | Let { monadic; lhs; rhs; body } ->
                (Option.map
                   ~f:(fun monad -> print#expr_monadic_let ~monad)
                   monadic
                |> Option.value ~default:print#expr_let)
                  ~lhs ~rhs body
                |> wrap_parens
            | Literal l -> print#literal Expr l
            | Block (e, _) -> print#expr ctx e
            | Array l ->
                separate_map comma (print#expr_at Expr_Array) l
                |> group |> brackets
            | LocalVar i -> print#local_ident i
            | GlobalVar (`Concrete i) -> print#concrete_ident i
            | GlobalVar (`Primitive p) -> print#primitive_ident p
            | GlobalVar (`TupleCons 0) -> print#expr_construct_tuple []
            | GlobalVar
                (`TupleType _ | `TupleField _ | `Projector _ | `TupleCons _) ->
                print#assertion_failure "GlobalVar"
            | Assign { lhs; e; _ } ->
                group (print#lhs lhs)
                ^^ space ^^ equals
                ^/^ group (print#expr_at Expr_Assign e)
                ^^ semi
            | Loop _ -> string "todo loop;"
            | Break _ -> string "todo break;"
            | Return _ -> string "todo return;"
            | Continue _ -> string "todo continue;"
            | QuestionMark { e; _ } ->
                print#expr_at Expr_QuestionMark e |> terminate qmark
            | Borrow { kind; e; _ } ->
                string (match kind with Mut _ -> "&mut " | _ -> "&")
                ^^ print#expr_at Expr_Borrow e
            | AddressOf _ -> string "todo address of;"
            | Closure { params; body; _ } ->
                separate_map comma (print#pat_at Expr_Closure_param) params
                |> group |> enclose bar bar
                |> terminate (print#expr_at Expr_Closure_body body |> group)
                |> wrap_parens
            | Ascription { e; typ } ->
                print#expr_at Expr_Ascription_e e
                ^^ string "as"
                ^/^ print#ty_at Expr_Ascription_typ typ
                |> wrap_parens
            | MacroInvokation _ -> print#assertion_failure "MacroInvokation"
            | EffectAction _ -> print#assertion_failure "EffectAction"
            | Quote { contents; _ } ->
                List.map
                  ~f:(function
                    | `Verbatim code -> string code
                    | `Expr e -> print#expr_at Expr_Quote e
                    | `Pat p -> print#pat_at Expr_Quote p)
                  contents
                |> concat
            | App _ | Construct _ -> super#expr' ctx e

        method expr_monadic_let
            : monad:supported_monads * F.monadic_binding ->
              lhs:pat ->
              rhs:expr ->
              expr fn =
          fun ~monad:_ ~lhs ~rhs body -> print#expr_let ~lhs ~rhs body

        method expr_let : lhs:pat -> rhs:expr -> expr fn =
          fun ~lhs ~rhs body ->
            string "let"
            ^/^ iblock Fn.id (print#pat_at Expr_Let_lhs lhs)
            ^/^ equals
            ^/^ iblock Fn.id (print#expr_at Expr_Let_rhs rhs)
            ^^ semi
            ^/^ (print#expr_at Expr_Let_body body |> group)

        method tuple_projection : size:int -> nth:int -> expr fn =
          fun ~size:_ ~nth e ->
            print#expr_at Expr_TupleProjection e
            |> terminate (dot ^^ OCaml.int nth)

        method field_projection : concrete_ident -> expr fn =
          fun i e ->
            print#expr_at Expr_FieldProjection e
            |> terminate (dot ^^ print#name_of_concrete_ident i)

        method expr_app : expr -> expr list -> generic_value list fn =
          fun f args _generic_args ->
            let args =
              separate_map
                (comma ^^ break 1)
                (print#expr_at Expr_App_arg >> group)
                args
            in
            let f = print#expr_at Expr_App_f f |> group in
            f ^^ iblock parens args

        method doc_construct_tuple : document list fn =
          separate (comma ^^ break 1) >> iblock parens

        method expr_construct_tuple : expr list fn =
          List.map ~f:(print#expr_at Expr_ConstructTuple)
          >> print#doc_construct_tuple

        method pat_construct_tuple : pat list fn =
          List.map ~f:(print#pat_at Pat_ConstructTuple)
          >> print#doc_construct_tuple

        method global_ident_projector : global_ident fn =
          function
          | `Projector (`Concrete i) | `Concrete i -> print#concrete_ident i
          | _ ->
              print#assertion_failure "global_ident_projector: not a projector"

        method doc_construct_inductive
            : is_record:bool ->
              is_struct:bool ->
              constructor:concrete_ident ->
              base:document option ->
              (global_ident * document) list fn =
          fun ~is_record ~is_struct:_ ~constructor ~base:_ args ->
            if is_record then
              print#concrete_ident constructor
              ^^ space
              ^^ iblock parens
                   (separate_map (break 0)
                      (fun (field, body) ->
                        (print#global_ident_projector field
                        |> terminate comma |> group)
                        ^^ colon ^^ space ^^ iblock Fn.id body)
                      args)
            else
              print#concrete_ident constructor
              ^^ space
              ^^ iblock parens (separate_map (break 0) snd args)

        method expr_construct_inductive
            : is_record:bool ->
              is_struct:bool ->
              constructor:concrete_ident ->
              base:(expr * F.construct_base) option ->
              (global_ident * expr) list fn =
          fun ~is_record ~is_struct ~constructor ~base ->
            let base =
              Option.map
                ~f:(fst >> print#expr_at Expr_ConcreteInductive_base)
                base
            in
            List.map ~f:(print#expr_at Expr_ConcreteInductive_field |> map_snd)
            >> print#doc_construct_inductive ~is_record ~is_struct ~constructor
                 ~base

        method attr : attr fn = fun _ -> empty

        method! pat' : par_state -> pat' fn =
          fun ctx ->
            let wrap_parens =
              group
              >>
              match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock braces
            in
            function
            | PWild -> underscore
            | PAscription { typ; typ_span; pat } ->
                print#pat_ascription ~typ ~typ_span pat |> wrap_parens
            | PBinding { mut; mode; var; typ = _; subpat } -> (
                let p =
                  (match mode with ByRef _ -> string "&" | _ -> empty)
                  ^^ (match mut with Mutable _ -> string "mut " | _ -> empty)
                  ^^ print#local_ident var
                in
                match subpat with
                | Some (subpat, _) ->
                    p ^^ space ^^ at ^^ space
                    ^^ print#pat_at Pat_PBinding_subpat subpat
                    |> wrap_parens
                | None -> p)
            | PArray { args } ->
                separate_map (break 0)
                  (print#pat_at Pat_PArray >> terminate comma >> group)
                  args
                |> iblock brackets
            | PDeref { subpat; _ } ->
                ampersand ^^ print#pat_at Pat_PDeref subpat
            | (PConstruct _ | PConstant _) as pat -> super#pat' ctx pat
            | POr { subpats } ->
                separate_map (bar ^^ break 1) (print#pat_at Pat_Or) subpats

        method pat_ascription : typ:ty -> typ_span:span -> pat fn =
          fun ~typ ~typ_span pat ->
            print#pat_at Pat_Ascription_pat pat
            ^^ colon
            ^^ print#with_span ~span:typ_span (fun () ->
                   print#ty_at Pat_Ascription_typ typ)

        method expr_unwrapped : par_state -> expr fn =
          fun ctx { e; _ } -> print#expr' ctx e

        method param : param fn =
          fun { pat; typ; typ_span; attrs } ->
            let typ =
              match typ_span with
              | Some span ->
                  print#with_span ~span (fun _ -> print#ty_at Param_typ typ)
              | None -> print#ty_at Param_typ typ
            in
            print#attrs attrs ^^ print#pat_at Param_pat pat ^^ space ^^ colon
            ^^ space ^^ typ

        method item' : item' fn =
          function
          | Fn { name; generics; body; params } ->
              let params =
                iblock parens
                  (separate_map (comma ^^ break 1) print#param params)
              in
              let generics = print#generic_params generics.params in
              string "fn" ^^ space ^^ print#concrete_ident name ^^ generics
              ^^ params
              ^^ iblock braces (print#expr_at Item_Fn_body body)
          | _ -> string "item not implemented"

        method generic_param' : generic_param fn =
          fun { ident; attrs; kind; _ } ->
            let suffix =
              match kind with
              | GPLifetime _ -> space ^^ colon ^^ space ^^ string "'unk"
              | GPType { default = None } -> empty
              | GPType { default = Some default } ->
                  space ^^ equals ^^ space
                  ^^ print#ty_at GenericParam_GPType default
              | GPConst { typ } ->
                  space ^^ colon ^^ space
                  ^^ print#ty_at GenericParam_GPConst typ
            in
            let prefix =
              match kind with
              | GPConst _ -> string "const" ^^ space
              | _ -> empty
            in
            let ident =
              let name =
                if String.(ident.name = "_") then "Anonymous" else ident.name
              in
              { ident with name }
            in
            prefix ^^ print#attrs attrs ^^ print#local_ident ident ^^ suffix

        method generic_params : generic_param list fn =
          separate_map comma print#generic_param >> group >> angles

        method arm' : arm' fn =
          fun { arm_pat; body } ->
            let pat = print#pat_at Arm_pat arm_pat |> group in
            let body = print#expr_at Arm_body body in
            pat ^^ string " => " ^^ body ^^ comma
      end
  end

  include Class

  include Api (struct
    type aux_info = unit

    let new_print () = (new Class.print :> print_object)
  end)
end
