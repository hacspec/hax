open Base
open Utils

module Make (FA : Features.T) = struct
  module FB = struct
    include FA
    include Features.Off.Record_variants
  end

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let record_variants = reject

        let metadata =
          Phase_utils.Metadata.make Diagnostics.Phase.RecordVariants
      end)

  let rec ditem (item : A.item) : B.item list =
    match item.v with
    | Type { name; generics; variants; is_struct = false } ->
        let variants', type_defs =
          List.unzip
            (List.map ~f:(flatten_variants item.span generics) variants)
        in
        List.filter_opt type_defs
        @ [
            {
              v =
                B.Type
                  {
                    name;
                    generics = dgenerics item.span generics;
                    variants = variants';
                    is_struct = false;
                  };
              span = item.span;
              ident = item.ident;
            };
          ]
    | _ ->
        [
          { v = ditem' item.span item.v; span = item.span; ident = item.ident };
        ]

  and flatten_variants span generics (v : A.variant) : B.variant * B.item option
      =
    let b_v = dvariant span v in
    if b_v.is_record then
      let new_name : Ast.concrete_ident =
        Concrete_ident.of_def_id Type
          {
            krate = "temp_name";
            path = [ { data = TypeNs "my_temp_name"; disambiguator = 0 } ];
          }
      in
      let b_v' : B.variant =
        {
          name = b_v.name;
          arguments =
            [
              ( new_name,
                B.TParam
                  {
                    name = "my_temp_name";
                    id = Ast.LocalIdent.ty_param_id_of_int 0;
                  } );
            ];
          is_record = false;
        }
      in
      let temp n : B.variant =
        {
          name = n;
          arguments = [];
          is_record = true;
          (* F.record_variants option; *)
        }
      in
      ( b_v',
        Some
          {
            v =
              B.Type
                {
                  name = new_name;
                  generics = dgenerics span generics;
                  variants = List.map ~f:(fun (n, _) -> temp n) b_v.arguments;
                  is_struct = true;
                };
            span;
            ident = b_v.name;
          } )
    else (b_v, None)
end

module _ (FA : Features.T) : Phase_utils.PHASE = Make (FA)
