open Base
open Ppxlib

let name = "declare_features"  

let uppercase_first_char (s : string) : string =
  String.(uppercase (prefix s 1) ^ drop_prefix s 1)

let expand ~(ctxt : Expansion_context.Extension.t)
    (features: string list):
    structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  (* let add_derivings t = [%type: [%t t] [@deriving show, yojson, eq]] in *)
  let (module B) = Ast_builder.make loc in
  (* let template = [%sigi: type name [@@deriving show, yojson, eq] ] in *)
  let rename_type txt =
    let h n =
      if String.(n = "placeholder")
      then txt
      else if String.(lowercase n = "placeholder")
      then uppercase_first_char txt
      else n
    in
    object
      inherit Ast_traverse.map as super
      method! type_declaration decl =
        { decl with ptype_name = {decl.ptype_name with txt = h decl.ptype_name.txt} }
      method! module_binding mb =
        let mb = super#module_binding mb in
        match mb.pmb_name with
        | {txt = Some txt} as l -> {mb with pmb_name = {l with txt = Some (h txt)}}
        | _ -> mb
    end
  in
  [%stri include struct
    module type FEATURES = sig
      include [%m
        List.map ~f:(fun txt ->
            (rename_type txt)#signature_item
              [%sigi: type placeholder [@@deriving show, yojson, eq]]
          ) features
        |> B.pmty_signature
      ]
    end
    module type T = FEATURES

    module MapFeatureTypes (T: sig type t [@@deriving show, yojson, eq] end) = struct
      include T
      include [%m
        List.concat_map ~f:(fun txt ->
            (rename_type txt)#structure
              [%str
                module Placeholder = struct
                  type placeholder = T.t [@@deriving show, yojson, eq]
                end
                type placeholder = T.t [@@deriving show, yojson, eq]
              ]
          ) features
        |> B.pmod_structure
      ]
    end

    module On  = MapFeatureTypes(struct type t = on  [@@deriving show, yojson, eq] end)
    module Off = MapFeatureTypes(struct type t = off [@@deriving show, yojson, eq] end)

    module SUBTYPE = struct
      module type T = sig
        module A : FEATURES
        module B : FEATURES

        include [%m
          List.map ~f:(fun txt ->
              let path modul = Longident.(Ldot (Lident modul, txt)) in
              let h m = B.ptyp_constr {loc; txt = path m} [] in
              B.psig_value (
                B.value_description
                  ~name:{loc; txt}
                  ~type_:(B.ptyp_arrow Nolabel (h "A") (h "B"))
                  ~prim:[]
              )
            ) features
          |> B.pmty_signature
        ]
      end

      module Id = [%m
        List.map ~f:(fun txt -> 
            [%stri let [%p B.ppat_var {loc; txt}] = Base.Fn.id]
          ) features
        |> B.pmod_structure
      ]
    end
  end]
  (* let attrs = *)
  (*   attributes_of_structure_item str *)
  (*   |> List.filter_map ~f:(fun attr -> *)
  (*          match string_of_payload ~loc attr.attr_payload with *)
  (*          | Result.Ok payload -> Some (attr.attr_name.txt, payload) *)
  (*          | _ -> None) *)
  (* in *)
  (* let opens = *)
  (*   List.filter_map *)
  (*     ~f:(fun (name, path) -> *)
  (*       if String.equal name "add" then Some path else None) *)
  (*     attrs *)
  (* in *)
  (* (map_inline_nodes opens loc)#structure_item str *)

let ext =
  Extension.V3.declare name Extension.Context.structure_item
    (* Ast_pattern.(pstr ((pstr_eval (pexp_tuple (many __) drop) ^:: nil))) *)
    Ast_pattern.(pstr ((pstr_eval (pexp_tuple (many (pexp_ident @@ lident __))) drop) ^:: nil))
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
