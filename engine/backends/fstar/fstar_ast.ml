open Hax_engine.Utils
open Base
module Util = FStar_Parser_Util
module AST = FStar_Parser_AST
module Const = FStar_Const
module Range = FStar_Compiler_Range
module Char = FStar_Char
module Ident = FStar_Ident

let dummyRange = Range.dummyRange
let id ident = Ident.mk_ident (ident, dummyRange)

let lid path =
  let init, last = List.(drop_last_exn path, last_exn path) in
  let last = if String.(last = "new") then "new_" else last in
  let init = List.map ~f:(map_first_letter String.uppercase) init in
  let path = init @ [ last ] in
  Ident.lid_of_path path dummyRange

let lid_of_id id = Ident.lid_of_ids [ id ]
let term (tm : AST.term') = AST.{ tm; range = dummyRange; level = Expr }
let generate_fresh_ident () = Ident.gen dummyRange

let decl ?(quals = []) ?(attrs = []) (d : AST.decl') =
  `Item AST.{ d; drange = dummyRange; quals; attrs }

let decls ?(quals = []) ?(attrs = []) x = [ decl ~quals ~attrs x ]
let pat (pat : AST.pattern') = AST.{ pat; prange = dummyRange }

module Attrs = struct
  let no_method = term @@ AST.Var FStar_Parser_Const.no_method_lid
end

let pat_var_tcresolve (var : string option) =
  let tcresolve =
    Some (AST.Meta (term @@ AST.Var FStar_Parser_Const.tcresolve_lid))
  in
  pat
  @@
  match var with
  | Some var -> AST.PatVar (id var, tcresolve, [])
  | _ -> AST.PatWild (tcresolve, [])

let pat_app name l = pat @@ AST.PatApp (name, l)
let wild = pat @@ AST.PatWild (None, [])

let mk_e_abs args body =
  if List.is_empty args then body else term (AST.Abs (args, body))

let mk_e_app base args =
  AST.mkApp base (List.map ~f:(fun arg -> (arg, AST.Nothing)) args) dummyRange

let mk_binder ?(aqual : FStar_Parser_AST.arg_qualifier option = Some Implicit) b
    =
  AST.{ b; brange = dummyRange; blevel = Un; aqual; battributes = [] }

let mk_e_binder b = mk_binder ~aqual:None b
let term_of_lid path = term @@ AST.Name (lid path)
let binder_of_term (t : AST.term) : AST.binder = mk_e_binder @@ AST.NoName t
let unit = term AST.(Const Const_unit)

let mk_e_arrow inputs output =
  term @@ AST.Product (List.map ~f:binder_of_term inputs, output)

let mk_e_arrow' types =
  let inputs, output = (List.drop_last_exn types, List.last_exn types) in
  mk_e_arrow inputs output

let mk_refined (x : string) (typ : AST.term) (phi : x:AST.term -> AST.term) =
  let x = id x in
  let x_bd = mk_e_binder @@ AST.Annotated (x, typ) in
  term @@ AST.Refine (x_bd, phi (term @@ AST.Var (lid_of_id x)))

let parse_string f s =
  let open FStar_Parser_ParseIt in
  let frag_of_text s =
    {
      frag_fname = "<string_of_term>";
      frag_line = Z.of_int 1;
      frag_col = Z.of_int 0;
      frag_text = s;
    }
  in
  match parse (f (frag_of_text s)) with
  | ParseError (_, err, _) -> failwith ("string_of_term: got error " ^ err)
  | x -> x

let term_of_string s =
  match parse_string (fun x -> Fragment x) s with
  | Term t -> t
  | _ -> failwith "parse failed"

let decls_of_string s =
  match parse_string (fun x -> Toplevel x) s with
  | ASTFragment (Inr l, _) -> List.map ~f:(fun i -> `Item i) l
  | _ -> failwith "parse failed"

let decl_of_string s =
  match decls_of_string s with [ d ] -> d | _ -> failwith "decl_of_string"

let ascribe t e = term @@ AST.Ascribed (e, t, None, false)
