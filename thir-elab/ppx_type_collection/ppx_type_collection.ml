open Base
open Ppxlib

let name = "type_collection"

let expand ~(ctxt : Expansion_context.Extension.t) (main_attrs, main)
    (ids : (attributes * string) list) : structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let mk ?(attrs = []) ptyp_desc =
    { ptyp_desc; ptyp_loc = loc; ptyp_loc_stack = []; ptyp_attributes = attrs }
  in
  let mk_tick name = mk (Ptyp_var name) in
  let bundle : core_type = mk_tick "bundle" in
  let bundle' : core_type = mk_tick "bundle_bis" in
  let mk_object_field name tick_name =
    {
      pof_desc = Otag ({ txt = name; loc }, mk_tick tick_name);
      pof_loc = loc;
      pof_attributes = [];
    }
  in
  let mk_obj f_tick_name =
    mk
      (Ptyp_object
         ( List.map ~f:(fun (_, id) -> mk_object_field id (f_tick_name id)) ids,
           Closed ))
  in
  let mk_overrider_type overrides attrs id def =
    {
      ptype_name = { txt = id; loc };
      ptype_params =
        List.map
          ~f:(fun x -> (x, (NoVariance, NoInjectivity)))
          ([ bundle; bundle' ]
          @ List.map ~f:(fun x -> mk_tick ("i_" ^ x)) overrides);
      ptype_cstrs =
        [
          (bundle, mk_obj (fun x -> "t_" ^ x), loc);
          ( bundle,
            mk_obj (fun x ->
                if List.mem ~equal:String.( = ) overrides x then "i_" ^ x
                else "t_" ^ x),
            loc );
        ];
      ptype_kind = Ptype_abstract;
      ptype_private = Public;
      ptype_manifest = Some bundle';
      ptype_attributes = attrs;
      ptype_loc = loc;
    }
  in
  let sorted_ids = List.map ~f:snd ids |> List.sort ~compare:String.compare in
  let mk_projector_type (attrs : attributes) (id : string) (def : core_type) =
    {
      ptype_name = { txt = id; loc };
      ptype_params = [ (bundle, (NoVariance, NoInjectivity)) ];
      ptype_cstrs = [ (bundle, mk_obj (fun x -> x), loc) ];
      ptype_kind = Ptype_abstract;
      ptype_private = Public;
      ptype_manifest = Some def;
      ptype_attributes = attrs;
      ptype_loc = loc;
    }
  in
  let types =
    [
      mk_projector_type main_attrs main bundle;
      mk_projector_type [] (main ^ "_phantom")
        (mk @@ Ptyp_constr ({ txt = Lident "unit"; loc }, []));
    ]
    @ List.map
        ~f:(fun (attrs, id) -> mk_projector_type attrs id (mk_tick id))
        ids
  in
  { pstr_loc = loc; pstr_desc = Pstr_type (Recursive, types) }
(* failwith (Ppxlib.Ast_pattern.stri x) *)
(* Ast_builder.Default.( *)
(*   (\* pstr_ loc false  *\) *)
(* ); *)
(* Obj.magic () *)

(* Ast_builder.Default.( *)
(*     pexp_function ~loc [ *)
(*         case *)
(*             ~lhs:pat *)
(*             ~guard *)
(*             ~rhs:(pexp_construct ~loc (Located.lident ~loc "true") None); *)
(*         case *)
(*             ~lhs:(ppat_any ~loc) *)
(*             ~guard:None *)
(*             ~rhs:(pexp_construct ~loc (Located.lident ~loc "false") None) *)
(*     ]) *)

let ext =
  Extension.V3.declare name Extension.Context.structure_item
    Ast_pattern.(
      pstr
        (pstr_eval
           (pexp_apply
              (pack2 (pexp_attributes (many __) (pexp_ident (lident __))))
              (pair drop
                 (pexp_tuple
                    (many
                       (pack2
                          (pexp_attributes (many __) (pexp_ident (lident __))))))
              ^:: nil))
           nil
        ^:: nil))
    expand

(* let ext = *)
(*     Extension.V3.declare *)
(*         name *)
(*         Extension.Context.structure_item *)
(*         Ast_pattern.(ptyp (ptyp_tuple (many (ptyp_constr (lident __) drop)))) *)
(*         expand *)

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
