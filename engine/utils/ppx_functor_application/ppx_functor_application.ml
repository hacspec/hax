open Base
open Ppxlib
module Format = Stdlib.Format

let name = "functor_application"

type longident = Longident.t

let show_longident = Longident.name

let pp_longident (fmt : Format.formatter) (s : longident) : unit =
  Format.pp_print_string fmt @@ show_longident s

let string_of_pattern p =
  let s = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer s in
  Pprintast.pattern fmt p;
  Format.pp_print_flush fmt ();
  Buffer.contents s

let string_of_module_expr p =
  let s = Buffer.create 0 in
  let fmt = Format.formatter_of_buffer s in
  Pprintast.module_expr fmt p;
  Format.pp_print_flush fmt ();
  Buffer.contents s

let show_module_expr = string_of_module_expr

let pp_module_expr (fmt : Format.formatter) (s : module_expr) : unit =
  Format.pp_print_string fmt @@ string_of_module_expr s

(** Defines a DSL for functor application. *)
type module_dsl =
  | Var of longident
  | App of module_dsl * module_dsl
  | ModExpr of module_expr
  | Abs of string * module_dsl
  | Pipe of module_dsl list
  | Meta of module_dsl * (location[@opaque])
[@@deriving show]

let var_of_string s = Var (Longident.Lident s)

(** Elaborate a OCaml module expression from a `module_dsl` *)
let rec elab ~loc (t : module_dsl) : module_expr =
  let (module E) = Ast_builder.make loc in
  let h = elab ~loc in
  match t with
  | Meta (x, loc) -> elab ~loc x
  | Var x -> E.pmod_ident { txt = x; loc }
  | ModExpr m -> m
  | App ((Abs (arg, m) | Meta (Abs (arg, m), _)), x) ->
      E.pmod_structure
        [
          E.pstr_module
          @@ E.module_binding ~name:{ loc; txt = Some arg } ~expr:(h x);
          E.pstr_include @@ E.include_infos @@ h m;
        ]
  | App (f, x) -> E.pmod_apply (h f) (h x)
  | Pipe (x :: funs) ->
      let x = h x in
      let nth_arg nth = "ARG" ^ Int.to_string nth in
      let arg0 = E.pmod_ident { loc; txt = Lident (nth_arg 0) } in
      let binds =
        List.mapi
          ~f:(fun i _ ->
            E.pmod_ident { txt = Lident (nth_arg @@ (i + 1)); loc })
          funs
        |> List.fold_left ~init:arg0 ~f:(fun x y ->
               let bind = E.pmod_ident { loc; txt = Lident "BindPhase" } in
               let ( <| ) = E.pmod_apply in
               bind <| x <| y)
      in
      E.pmod_structure
      @@ [%stri module ARG0 = [%m x]]
         :: List.concat_mapi
              ~f:(fun nth fn ->
                let nth_var = Var (Ldot (Lident (nth_arg nth), "FB")) in
                let new_arg = App (fn, nth_var) in
                [
                  E.pstr_module
                  @@ E.module_binding
                       ~name:{ loc; txt = Some (nth_arg @@ (nth + 1)) }
                       ~expr:(h new_arg);
                ])
              funs
      @ [%str include [%m binds]]
  | Pipe _ -> failwith "Illegal pipe: singleton or empty"
  | Abs _ -> failwith "Top-level abstraction"

let rec collect_pipes (t : module_dsl) : module_dsl list =
  match t with
  | Meta (Pipe l, _) | Pipe l -> List.concat_map ~f:collect_pipes l
  | _ -> [ t ]

(** Get rid of extra `Pipe` nodes *)
let rec normalize (t : module_dsl) : module_dsl =
  match t with
  | App (f, x) -> App (normalize f, normalize x)
  | Abs (x, body) -> Abs (x, normalize body)
  | ModExpr _ | Var _ -> t
  | Meta (x, loc) -> Meta (normalize x, loc)
  | Pipe _ -> (
      match collect_pipes t with
      | [] -> failwith "Empty pipe"
      | [ t ] -> t
      | l -> Pipe l)

(** Recognize a small language embedded in OCaml syntax for applying
functors in chain. *)
let rec parse expr =
  let r =
    match expr with
    | { pexp_desc = Pexp_construct ({ txt; _ }, None); _ } ->
        (* Parses variables (module names are uppercase, since we are looking at OCaml expressions, so we match on constructors)  *)
        Var txt
    | { pexp_desc = Pexp_construct ({ txt; _ }, Some arg); _ } ->
        (* Parses module applcations (same as above: in expressions, module applications are parsed as constructor applications) *)
        App (Var txt, parse arg)
    | [%expr [%e? m1] |> [%e? m2]] ->
        (* Parses `... |> ...` infix module application *)
        Pipe [ parse m1; parse m2 ]
    | [%expr (module [%m? m])] ->
        (* Parses module expressions (in this case, that corresponds to OCaml module expression) *)
        ModExpr m
    | [%expr [%e? f] [%e? x]] ->
        (* Parses module applications (e.g. `(fun x -> ...) (module YXZ)`) *)
        App (parse f, parse x)
    | [%expr fun [%p? x] -> [%e? body]] -> (
        (* Parses module abstractions (e.g. `fun X -> Z(X)`) *)
        match x with
        | { ppat_desc = Ppat_construct ({ txt = Lident x; _ }, None); _ } ->
            Abs (x, parse body)
        | _ -> failwith @@ "Out of language: " ^ string_of_pattern x)
    | _ -> failwith @@ "Out of language: " ^ Pprintast.string_of_expression expr
  in
  Meta (r, expr.pexp_loc)

let expand ~(ctxt : Expansion_context.Extension.t) (e : expression) :
    module_expr =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let e = parse e |> normalize in
  elab ~loc e

let ext =
  Extension.V3.declare name Extension.Context.module_expr
    Ast_pattern.(pstr (pstr_eval __ drop ^:: nil))
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
