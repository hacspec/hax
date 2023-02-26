open Base
open Ppxlib

let name = "ast"

let include_strs loc strs =
  {
    pstr_loc = loc;
    pstr_desc =
      Pstr_include
        {
          pincl_mod =
            {
              pmod_desc = Pmod_structure strs;
              pmod_loc = loc;
              pmod_attributes = [];
            };
          pincl_loc = loc;
          pincl_attributes = [];
        };
  }

let pack_module_expr loc functor_name (mod_expr : module_expr) =
  {
    pstr_loc = loc;
    pstr_desc =
      Pstr_module
        {
          pmb_name = { txt = functor_name; loc };
          pmb_expr = mod_expr;
          pmb_attributes = [];
          pmb_loc = loc;
        };
  }

let pack_module_type loc functor_name (mod_type : module_type) =
  {
    pstr_loc = loc;
    pstr_desc =
      Pstr_modtype
        {
          pmtd_name = { txt = functor_name; loc };
          pmtd_type = Some mod_type;
          pmtd_attributes = [];
          pmtd_loc = loc;
        };
  }

let mk_functor_typ' loc (functor_body : module_type)
    (arg : string * module_type) : module_type =
  let x_name, x_type = arg in
  {
    pmty_desc =
      Pmty_functor (Named ({ txt = Some x_name; loc }, x_type), functor_body);
    pmty_loc = loc;
    pmty_attributes = [];
  }

let mk_functor_typ loc functor_body args =
  List.fold ~init:functor_body ~f:(mk_functor_typ' loc) @@ args

let mk_functorized_module_type ~loc ~name ~body args =
  mk_functor_typ loc body (List.rev args) |> pack_module_type loc name

let mod_type_of_name loc name =
  {
    pmty_desc = Pmty_ident { txt = Lident name; loc };
    pmty_loc = loc;
    pmty_attributes = [];
  }

let mk_functor_expr' loc (functor_body : module_expr)
    (arg : string * module_type) : module_expr =
  let x_name, x_type = arg in
  {
    pmod_desc =
      Pmod_functor (Named ({ txt = Some x_name; loc }, x_type), functor_body);
    pmod_loc = loc;
    pmod_attributes = [];
  }

let mk_functor_expr loc functor_body args =
  List.fold ~init:functor_body ~f:(mk_functor_expr' loc) @@ args

let mk_functorized_module ~loc ~name ~body args =
  mk_functor_expr loc body (List.rev args) |> pack_module_expr loc (Some name)

let mod_type_of_name loc name =
  {
    pmty_desc = Pmty_ident { txt = Lident name; loc };
    pmty_loc = loc;
    pmty_attributes = [];
  }

let signature_of_module_type (mtyp : module_type) : signature =
  match mtyp.pmty_desc with
  | Pmty_signature l -> l
  | _ -> failwith "types_of_module_type: expected a Pmty_signature"

let psig_type_of_signature_item (si : signature_item) :
    (Asttypes.rec_flag * type_declaration list) option =
  match si.psig_desc with Psig_type (r, l) -> Some (r, l) | _ -> None

let types_of_module_type (mtyp : module_type) =
  mtyp |> signature_of_module_type
  |> List.map ~f:psig_type_of_signature_item
  |> List.filter_opt

let type_decls_of_structure :
    structure -> (rec_flag * type_declaration list) list =
  List.filter_map ~f:(function
    | { pstr_desc = Pstr_type (r, l) } -> Some (r, l)
    | _ -> None)

let nonrec_types_of_module_type (mtyp : module_type) : type_declaration list =
  mtyp |> types_of_module_type |> List.concat_map ~f:(fun (_, l) -> l)

let mk_core_type ptyp_loc ptyp_desc =
  { ptyp_desc; ptyp_loc; ptyp_loc_stack = []; ptyp_attributes = [] }

let mk_ptyp_constr loc ident =
  mk_core_type loc @@ Ptyp_constr ({ txt = ident; loc }, [])

let mk_longident1 a = Lident a
let mk_longident2 a b = Ldot (Lident a, b)

let mk_ptyp_arrow loc (types : core_type list) : core_type =
  let types = List.rev types in
  let init, tl = (List.hd_exn types, List.tl_exn types) in
  let tl = List.rev tl in
  let wrap t =
    { ptyp_desc = t; ptyp_loc = loc; ptyp_loc_stack = []; ptyp_attributes = [] }
    (* in List.fold ~init ~f:(fun a b -> wrap @@ Ptyp_arrow (Nolabel, a, b))  *)
  in
  List.fold_right ~init ~f:(fun a b -> wrap @@ Ptyp_arrow (Nolabel, a, b)) tl

let expand ~(ctxt : Expansion_context.Extension.t) (self_name : string)
    (features_name : string) (features_mod_type : module_type)
    (self : module_expr) : structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let mk_si pstr_desc = { pstr_desc; pstr_loc = loc } in
  let feature_type =
    {
      pstr_loc = loc;
      pstr_desc =
        Pstr_modtype
          {
            pmtd_name = { txt = features_name; loc };
            pmtd_type = Some features_mod_type;
            pmtd_attributes = [];
            pmtd_loc = loc (* todo use proper loc *);
          };
    }
  in
  let feature_subtype_name = features_name ^ "_subtype" in
  let feature_subtype_sig =
    mk_functorized_module_type ~loc ~name:feature_subtype_name
      ~body:
        {
          pmty_desc =
            Pmty_signature
              (nonrec_types_of_module_type features_mod_type
              |> List.map ~f:(fun typ ->
                     let h n =
                       mk_ptyp_constr loc (mk_longident2 n typ.ptype_name.txt)
                     in
                     let typ_decl =
                       {
                         ptype_name = typ.ptype_name;
                         ptype_params = [];
                         ptype_cstrs = [];
                         ptype_kind = Ptype_abstract;
                         ptype_private = Public;
                         ptype_manifest =
                           Some
                             (mk_core_type loc
                             @@ Ptyp_arrow (Nolabel, h "A", h "B"));
                         ptype_attributes = [];
                         ptype_loc = typ.ptype_loc;
                       }
                     in
                     {
                       psig_desc = Psig_type (Recursive, [ typ_decl ]);
                       psig_loc = typ.ptype_loc;
                     }));
          pmty_loc = loc;
          pmty_attributes = [];
        }
      [
        ("A", mod_type_of_name loc features_name);
        ("B", mod_type_of_name loc features_name);
      ]
  in
  let self_str =
    match self.pmod_desc with
    | Pmod_structure s -> s
    | _ -> failwith "module as expected to be a [struct .. end]"
  in
  let self =
    mk_functorized_module ~loc ~name:self_name ~body:self
      [ (features_name, mod_type_of_name loc features_name) ]
    (* { *)
    (*   pstr_desc = *)
    (*     Pstr_module { *)
    (*         pmb_name = {loc; txt = Some self_name}; *)
    (*         pmb_expr = self; *)
    (*         pmb_attributes = []; *)
    (*         pmb_loc = loc; *)
    (*       }; *)
    (*   pstr_loc = loc; *)
    (* } *)
  in
  let subtype =
    let items =
      type_decls_of_structure self_str
      |> List.map ~f:(fun (r, l) ->
             Pstr_value
               ( r,
                 List.map
                   ~f:(fun decl ->
                     let mk =
                       let name =
                         {
                           ppat_desc = Ppat_var decl.ptype_name;
                           ppat_loc = decl.ptype_loc;
                           ppat_loc_stack = [];
                           ppat_attributes = [];
                         }
                       in
                       let typs =
                         let typs = List.map ~f:fst decl.ptype_params in
                         typs
                         @
                         let applied n =
                           {
                             ptyp_desc =
                               Ptyp_constr
                                 ( {
                                     txt = mk_longident2 n decl.ptype_name.txt;
                                     loc = decl.ptype_loc;
                                   },
                                   typs );
                             ptyp_loc = decl.ptype_loc;
                             ptyp_loc_stack = [];
                             ptyp_attributes = [];
                           }
                         in
                         [ applied "MA"; applied "MB" ]
                       in
                       {
                         pvb_pat =
                           [%pat?
                             ([%p name] :
                               [%t mk_ptyp_arrow decl.ptype_loc typs])];
                         (* pvb_pat = { *)
                         (*   ppat_desc = Ppat_var decl.ptype_name; *)
                         (*   ppat_loc = decl.ptype_loc; *)
                         (*   ppat_loc_stack = []; *)
                         (*   ppat_attributes = []; *)
                         (* }; *)
                         pvb_expr = [%expr failwith "todo"];
                         pvb_attributes = [];
                         pvb_loc = decl.ptype_loc;
                       }
                     in
                     match decl.ptype_kind with
                     | Ptype_abstract ->
                         failwith "cannot deal with abstract type definitions"
                     | Ptype_open -> failwith "cannot deal with open"
                     | Ptype_record _ -> mk
                     | Ptype_variant cl -> mk)
                   l ))
      |> List.map ~f:(fun pstr_desc -> { pstr_desc; pstr_loc = loc })
      (* |> (fun s -> ) *)
    in
    mk_functorized_module ~loc ~name:"Subtype"
      ~body:
        {
          pmod_desc =
            Pmod_structure
              ([ [%stri module MA = Hello (A)]; [%stri module MB = Hello (B)] ]
              @ items);
          pmod_loc = loc;
          pmod_attributes = [];
        }
      [
        ("A", mod_type_of_name loc features_name);
        ("B", mod_type_of_name loc features_name);
        ("Sub", mod_type_of_name loc feature_subtype_name);
      ]
  in
  include_strs loc [ feature_type; feature_subtype_sig; self ]

let ext =
  Extension.V3.declare name Extension.Context.structure_item
    Ast_pattern.(
      pstr
        (pstr_module
           (module_binding (some __)
              (pmod_functor
                 (named (some __)
                    __
                    (* pmty_signature ( *)
                    (*     many __ *)
                    (*   ) *))
                 (* (pmod_structure (many __)) *)
                 __))
        ^:: nil))
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
