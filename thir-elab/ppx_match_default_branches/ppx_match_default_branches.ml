open Base
open Ppxlib

let name_def_brs  = "def_brs"

let subtype_module = Core.In_channel.read_all "/home/lucas/repos/thir-export/main/thir-elab/lib/subtype.ml"
let subtype_module_ast = Parse.implementation (Lexing.from_string subtype_module)

let cases_of =
  object
    inherit [_] Ast_traverse.fold as super

    method! expression e acc =
      let acc = super#expression e acc in
      match e.pexp_desc with
      | Pexp_match (scrut, cases) -> List.map ~f:(fun case -> scrut, case) cases @ acc
      | _ -> acc
  end
  
let set_locations loc =
  object
    inherit Ast_traverse.map as super

    method! location _ = loc
  end

let string_of_longident = Longident.last_exn

let subtype_module_cases =
  cases_of#structure subtype_module_ast []
  |> List.filter_map ~f:(fun (scrut, case) ->
      let kind = match scrut.pexp_desc with
        | Pexp_ident {txt} -> string_of_longident txt
        | _ -> failwith ("Maching over something which is not an ident in Subtype.ml: " ^ Pprintast.string_of_expression scrut)
      in
      match case.pc_lhs.ppat_desc with
      | Ppat_construct ({txt = construct}, _) -> Some (kind, string_of_longident construct, case)
      | _ -> None
    )
  (* |> Map.of_alist (module String) *)

let find_cases_by_regexp (needle: ((string * Re.re), string) Either.t): (string * case) list =
  let nstr = match needle with
    | Either.First (s, _)
    | Either.Second s -> s in
  let results = List.filter ~f:(fun (scrut, cons, case) ->
      match needle with
      | Either.First (_, re) -> Re.execp re (scrut ^ ":" ^ cons)
      | Either.Second c -> String.equal c cons
    ) subtype_module_cases in
  let names =
    List.map ~f:(fun (_, x, _) -> x) results
    |> List.sort ~compare:String.compare
    |> List.find_consecutive_duplicate ~equal:String.equal
    |> Option.map ~f:(fun (x, _) -> "Constructor "^x^" is ambiguous (matched by " ^ nstr ^ ")")
  in
  if List.is_empty results
  then failwith @@ "'" ^ nstr ^ " matched nothing";
  List.map ~f:(fun (_, c, x) -> (c, x)) results

let expand_def_brs ~(ctxt : Expansion_context.Extension.t)
    (scrutinee: expression)
    (cases: cases): expression =
  let cases = List.concat_map ~f:(fun case ->
      match case.pc_lhs.ppat_desc with
      | Ppat_extension ({txt = "auto"}, str) ->
        let err (type a) (): a = failwith "Expected a list of comma separated constructor names" in
        let as_string = function
          | {pexp_desc = Pexp_construct ({txt = c}, None)} ->
            let c = string_of_longident c in
            Either.Second c
          | {pexp_desc = Pexp_constant (Pconst_string (s, _, _))} ->
            Either.First (s,
                          Re.(
                            seq [
                              Re.bol;
                              Re_posix.re @@ String.chop_prefix_if_exists ~prefix:"!" s;
                              Re.eol
                            ]
                          ) |> Re.compile
                         )
          | _ -> err ()
        in
        let is_negative = function
          | {pexp_desc = Pexp_constant (Pconst_string (s, _, _))} ->
            Option.is_some @@ String.chop_prefix ~prefix:"!" s
          | _ -> false
        in
        let mk s = as_string s |> find_cases_by_regexp |> List.map ~f:(fun (a, b) -> a, (set_locations case.pc_lhs.ppat_loc)#case b) in
        (* let mk l = List.map ~f:as_string l |> List.concat_map ~f:find_cases_by_regexp |> List.map ~f:(fun (a, b) -> a, (set_locations case.pc_lhs.ppat_loc)#case b) in *)
        begin match str with
          | PStr ([{pstr_desc = Pstr_eval ({pexp_desc = Pexp_tuple n}, _)}] as s) ->
            List.fold_left n ~init:[] ~f:(fun acc x ->
                let r = mk x in
                if is_negative x
                then List.filter ~f:(fun (k, _) -> List.for_all ~f:(fun (k', _) -> not @@ String.equal k' k) r) acc
                else acc @ r
              ) 
            |> List.map ~f:snd
            (* List.map ~f:mk n *)
            (* |> List.concat_map ~f:Fn.id *)
          | PStr ([{pstr_desc = Pstr_eval (e, _)}] as s) -> List.map ~f:snd @@ mk e
          | _ -> err ()
        end
      | _ -> [case]
    ) cases
  in {
    pexp_desc = Pexp_match (scrutinee, cases);
    pexp_loc = Expansion_context.Extension.extension_point_loc ctxt;
    pexp_loc_stack  = [];
    pexp_attributes = [];
  }

let ext_def_match =
  Extension.V3.declare "def_match" Extension.Context.expression
    Ast_pattern.(single_expr_payload (pexp_ident __))
    (fun ~ctxt lid ->
       let loc = Expansion_context.Extension.extension_point_loc ctxt in
       let (module M) = Ast_builder.make loc in
       let lid_str = string_of_longident lid in
       let lid = M.evar lid_str in
       let payload = PStr [M.pstr_eval (M.pexp_constant (Pconst_string (lid_str ^ ":.*", M.loc, None))) []] in
       let p = M.ppat_extension ({txt = "auto"; loc = M.loc}, payload) in
       expand_def_brs ~ctxt lid [{
           pc_lhs = p;
           pc_guard = None;
           pc_rhs = [%expr ()]
         }]
    )

let ext_def_brs =
  Extension.V3.declare name_def_brs Extension.Context.expression
    Ast_pattern.(single_expr_payload (pexp_match __ __))
    expand_def_brs
    
let () = Ppxlib.Driver.register_transformation ~rules:[
    Ppxlib.Context_free.Rule.extension ext_def_brs;
    Ppxlib.Context_free.Rule.extension ext_def_match
  ] name_def_brs
    
(* let () = Ppxlib.Driver.register_transformation ~rules:[ *)
  (* ] "def_match" *)
