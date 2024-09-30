open Prelude

module Make (F : Features.T) = struct
  module AST = Ast.Make (F)
  open Ast.Make (F)
  open New_generic_printer_base
  module P = New_generic_printer_base.Make (F)
  open PPrint

  let unimplemented s = string ("unimplemented: " ^ s)

  module View = Concrete_ident.DefaultViewAPI

  let iblock f = group >> jump 2 0 >> terminate (break 0) >> f >> group
  let call = ( !: )

  class print =
    object (print)
      inherit P.base as _super
      method ty_TApp_tuple ~full:_ _args = unimplemented "ty_TApp_tuple"

      method ty_TApp_application ~full:_ _f _args =
        unimplemented "ty_TApp_application"

      method expr_App_constant ~full:_ _ident _generic_values =
        unimplemented "expr_App_constant"

      method expr_App_application ~full:_ f _args _generics =
        print#expr_at Expr_App_f f
      (* print#expr_at Expr_App_f f ^/^ separate_map space (print#expr_at Expr_App_arg) args *)
      (* unimplemented "expr_App_application" *)

      method expr_App_tuple_projection ~full:_ ~size:_ ~nth:_ _tuple =
        unimplemented "expr_App_tuple_projection"

      method expr_App_field_projection ~full:_ _ident _data =
        unimplemented "expr_App_field_projection"

      method expr_Construct_inductive ~full:_ ~is_record:_ ~is_struct:_
          ~constructor:_ ~base:_ _fields =
        unimplemented "expr_Construct_inductive"

      method expr_Construct_tuple ~full:_ _components =
        unimplemented "expr_Construct_tuple"

      method expr_ _ ctx expr =
        let wrap_parens =
          group
          >> match ctx with AlreadyPar -> Fn.id | NeedsPar -> iblock braces
        in
        match expr.e with
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
                (call print#arm >> group >> nest 2
                >> precede (bar ^^ space)
                >> group)
                arms
            in
            header ^^ iblock braces arms
        | Let { monadic; lhs; rhs; body } ->
            (Option.map ~f:(fun monad -> print#expr_monadic_let ~monad) monadic
            |> Option.value ~default:print#expr_let)
              ~lhs ~rhs body
            |> wrap_parens
        | Literal l -> print#literal l
        | Block { e; _ } -> call print#expr ctx e
        | _ -> unimplemented "expr_todo"

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

      method literal =
        function
        | String s -> utf8string s |> dquotes
        | Char c -> char c |> bquotes
        | Int { value; negative; _ } ->
            string value |> precede (if negative then minus else empty)
        | Float { value; kind; negative } ->
            string value
            |> precede (if negative then minus else empty)
            |> terminate (string (Ast.show_float_kind kind))
        | Bool b -> OCaml.bool b

      method ty_ _ _ctx _typ = unimplemented "ty_"
      method pat_ _ _ctx _pat = unimplemented "pat_"

      method item_ _ item =
        match item.v with
        | Fn { name; generics; body; params; _ } ->
            let params =
              iblock parens (separate_map (comma ^^ break 1) print#param params)
            in
            let generics =
              separate_map comma (call print#generic_param) generics.params
            in
            string "fn" ^^ space
            ^^ call print#concrete_ident name
            ^^ generics ^^ params
            ^^ iblock braces (print#expr_at Item_Fn_body body)
        | _ -> string "item not implemented"

      method param_ty_ _ _param_ty = unimplemented "param_ty_"

      method param (param : param) =
        let { pat; typ = _; typ_span = _; attrs } = param in
        print#attrs attrs ^^ print#pat_at Param_pat pat ^^ space ^^ colon
        ^^ space ^^ !:(print#param_ty) param

      method arm_ _ _arm = unimplemented "arm_"
      method generic_param_ _ _gp = unimplemented "generic_param_"
      method impl_item_ _ _ii = unimplemented "impl_item_"
      method trait_item_ _ _ti = unimplemented "trait_item_"
      method attr_ _ _attr = unimplemented "attr_"

      method namespace_of_concrete_ident =
        Concrete_ident.DefaultViewAPI.to_namespace

      method printer_name = "blank-template"
      method par_state _ = AlreadyPar

      method concrete_ident_ _ ~under_current_ns id =
        let id = View.to_view id in
        let chunks =
          if under_current_ns then [ id.definition ]
          else id.crate :: (id.path @ [ id.definition ])
        in
        separate_map (colon ^^ colon) utf8string chunks
    end

  open New_generic_printer_api.Make (F)

  include Api (struct
    type aux_info = unit

    let new_print _ = (new print :> print_object)
  end)
end
