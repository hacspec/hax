let xx (x : Ast.Rust.item) =
  match x with
  | {
   v =
     Fn
       {
         name =
           {
             def_id =
               {
                 Concrete_ident_inner_types.Imported.krate = "literals";
                 path =
                   [
                     {
                       Concrete_ident_inner_types.Imported.data =
                         Concrete_ident_inner_types.Imported.ValueNs "f";
                       disambiguator = 0;
                     };
                   ];
               };
             kind = Concrete_ident_inner_types.Kind.Value;
           };
         generics =
           {
             params =
               [
                 {
                   ident = _of_local_ident_1;
                   span = _;
                   attrs = [];
                   kind = GPType { default = None };
                 };
               ];
             constraints = [ GCType _ ];
           };
         body =
           {
             e =
               Block
                 ( {
                     e =
                       Construct
                         {
                           constructor = _of_global_ident_4;
                           is_record = false;
                           is_struct = false;
                           fields = [ (_of_global_ident_3, a) ];
                           base = None;
                         };
                     span = _;
                     typ =
                       TApp { ident = _of_global_ident_2; args = [ GType _ ] };
                   },
                   _ (* matches feature block *) );
             span = _;
             typ = TApp { ident = _of_global_ident_1; args = [ GType _ ] };
           };
         params = [ { pat = a; typ = _; typ_span = Some _; attrs = [] } ];
       };
   span = _;
   ident =
     {
       def_id =
         {
           Concrete_ident_inner_types.Imported.krate = "literals";
           path =
             [
               {
                 Concrete_ident_inner_types.Imported.data =
                   Concrete_ident_inner_types.Imported.ValueNs "f";
                 disambiguator = 0;
               };
             ];
         };
       kind = Concrete_ident_inner_types.Kind.Value;
     };
   attrs =
     [
       { kind = Tool { path = "feature"; tokens = "register_tool" }; span = _ };
       { kind = Tool { path = "register_tool"; tokens = "_hax" }; span = _ };
     ];
  } ->
      0
  | _ -> 1
