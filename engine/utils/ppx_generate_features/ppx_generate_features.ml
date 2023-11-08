open Base
open Ppxlib

let name = "declare_features"

let uppercase_first_char (s : string) : string =
  String.(uppercase (prefix s 1) ^ drop_prefix s 1)

let rename (l : (string * string) list) =
  let h (s : string) =
    List.find_map
      ~f:(fun (s', replace) -> if String.equal s s' then Some replace else None)
      l
    |> Option.value ~default:s
  in
  object
    inherit Ast_traverse.map
    method! string = h
    method! label = h

    method! longident =
      let rec r = function
        | Lapply (x, y) -> Lapply (r x, r y)
        | Ldot (x, y) -> Ldot (r x, h y)
        | Lident x -> Lident (h x)
      in
      r
  end

let expand ~(ctxt : Expansion_context.Extension.t) (features : string list) :
    structure_item =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let (module B) = Ast_builder.make loc in
  [%stri
    include struct
      module type FEATURES = sig
        include
          [%m
        List.map
          ~f:(fun txt ->
            (rename [ ("placeholder", txt) ])#signature_item
              [%sigi: type placeholder [@@deriving show, yojson, hash, eq]])
          features
        |> B.pmty_signature]
      end

      module type T = FEATURES

      module Enumeration = struct
        [%%i
        let decl =
          B.type_declaration ~name:{ loc; txt = "t" } ~params:[] ~cstrs:[]
            ~kind:
              (Ptype_variant
                 (List.map
                    ~f:(fun txt ->
                      B.constructor_declaration
                        ~name:{ loc; txt = uppercase_first_char txt }
                        ~args:(Pcstr_tuple []) ~res:None)
                    features))
            ~private_:Public ~manifest:None
        in
        B.pstr_type Recursive
          [
            {
              decl with
              ptype_attributes =
                [
                  B.attribute ~name:{ loc; txt = "deriving" }
                    ~payload:(PStr [%str show, yojson, hash, eq, enumerate]);
                ];
            };
          ]]
      end

      module DefaultClasses (F : T) = struct
        [%%i
        B.pstr_class
          [
            B.class_infos ~virt:Virtual
              ~params:[ ([%type: 'self], (NoVariance, NoInjectivity)) ]
              ~name:{ loc; txt = "default_reduce_features" }
              ~expr:
                (B.pcl_structure
                @@ B.class_structure
                     ~self:[%pat? (self : 'self)]
                     ~fields:
                       (B.pcf_inherit Fresh
                          (B.pcl_constr
                             {
                               txt = Ldot (Lident "VisitorsRuntime", "reduce");
                               loc;
                             }
                             [ [%type: _] ])
                          None
                       :: List.map
                            ~f:(fun txt ->
                              B.pcf_method
                                ( { loc; txt = "visit_" ^ txt },
                                  Public,
                                  Cfk_concrete
                                    ( Fresh,
                                      (rename [ ("placeholder", txt) ])
                                        #expression
                                        [%expr
                                          fun (_env : 'env) (_ : F.placeholder) ->
                                            self#zero] ) ))
                            features));
          ]]

        [%%i
        B.pstr_class
          [
            B.class_infos ~virt:Virtual
              ~params:[ ([%type: 'self], (NoVariance, NoInjectivity)) ]
              ~name:{ loc; txt = "default_mapreduce_features" }
              ~expr:
                (B.pcl_structure
                @@ B.class_structure
                     ~self:[%pat? (self : 'self)]
                     ~fields:
                       (B.pcf_inherit Fresh
                          (B.pcl_constr
                             {
                               txt = Ldot (Lident "VisitorsRuntime", "mapreduce");
                               loc;
                             }
                             [ [%type: _] ])
                          None
                       :: List.map
                            ~f:(fun txt ->
                              B.pcf_method
                                ( { loc; txt = "visit_" ^ txt },
                                  Public,
                                  Cfk_concrete
                                    ( Fresh,
                                      (rename [ ("placeholder", txt) ])
                                        #expression
                                        [%expr
                                          fun (_env : 'env) (x : F.placeholder) ->
                                            (x, self#zero)] ) ))
                            features));
          ]]

        [%%i
        B.pstr_class
          [
            B.class_infos ~virt:Virtual
              ~params:[ ([%type: 'self], (NoVariance, NoInjectivity)) ]
              ~name:{ loc; txt = "default_map_features" }
              ~expr:
                (B.pcl_structure
                @@ B.class_structure
                     ~self:[%pat? (_self : 'self)]
                     ~fields:
                       (B.pcf_inherit Fresh
                          (B.pcl_constr
                             {
                               txt = Ldot (Lident "VisitorsRuntime", "map");
                               loc;
                             }
                             [ [%type: 'env] ])
                          None
                       :: List.map
                            ~f:(fun txt ->
                              B.pcf_method
                                ( { loc; txt = "visit_" ^ txt },
                                  Public,
                                  Cfk_concrete
                                    ( Fresh,
                                      (rename [ ("placeholder", txt) ])
                                        #expression
                                        [%expr
                                          fun (_ : 'env) (x : F.placeholder) ->
                                            x] ) ))
                            features));
          ]]
      end

      (*
      module MapFeatureTypes (T : sig
        type t [@@deriving show, yojson, hash, eq]
      end) =
      struct
        include T

        include
          [%m
          List.concat_map
            ~f:(fun txt ->
              (rename
                 [
                   ("placeholder", txt);
                   ("Placeholder", uppercase_first_char txt);
                 ])
                #structure
                [%str
                  module Placeholder = struct
                    type placeholder = Placeholder of T.t [@@deriving show, yojson, hash, eq]
                  end
                      
                  include Placeholder])
            features
          |> B.pmod_structure]
      end

      module On = MapFeatureTypes (struct
        type t = on [@@deriving show, yojson, hash, eq]
      end)

      module Off = MapFeatureTypes (struct
        type t = off [@@deriving show, yojson, hash, eq]
            end)
            *)

      module On =
      [%m
      List.concat_map
        ~f:(fun txt ->
          (rename
             [ ("placeholder", txt); ("Placeholder", uppercase_first_char txt) ])
            #structure
            [%str
              module Placeholder : sig
                type placeholder [@@deriving show, yojson, hash, eq]

                val placeholder : placeholder
              end = struct
                type placeholder = Placeholder
                [@@deriving show, yojson, hash, eq]

                let placeholder = Placeholder
              end

              include Placeholder])
        features
      |> B.pmod_structure]

      module ToFull =
      [%m
      List.concat_map
        ~f:(fun txt ->
          (rename
             [ ("placeholder", txt); ("Placeholder", uppercase_first_char txt) ])
            #structure
            [%str let placeholder _ = On.placeholder])
        features
      |> B.pmod_structure]

      module Off =
      [%m
      List.concat_map
        ~f:(fun txt ->
          (rename
             [ ("placeholder", txt); ("Placeholder", uppercase_first_char txt) ])
            #structure
            [%str
              module Placeholder = struct
                type placeholder = | [@@deriving show, yojson, hash, eq]
              end

              include Placeholder])
        features
      |> B.pmod_structure]

      module SUBTYPE = struct
        module type T = sig
          module A : FEATURES
          module B : FEATURES

          include
            [%m
          List.map
            ~f:(fun txt ->
              (rename [ ("placeholder", txt) ])#signature_item
                [%sigi: val placeholder : A.placeholder -> B.placeholder])
            features
          |> B.pmty_signature]
        end

        module type MAPPER = sig
          val map : 'a 'b. ('a -> 'b) -> Enumeration.t -> 'a -> 'b
        end

        module Map (S : T) (Mapper : MAPPER) =
        [%m
        let f txt =
          [%stri
            let [%p B.ppat_var { loc; txt }] =
              let kind =
                [%e
                  B.pexp_construct
                    {
                      loc;
                      txt = Ldot (Lident "Enumeration", uppercase_first_char txt);
                    }
                    None]
              in
              let f = [%e B.pexp_ident { loc; txt = Ldot (Lident "S", txt) }] in
              Mapper.map f kind]
        in
        B.pmod_structure @@ ([%stri include S] :: List.map ~f features)]

        module On =
        [%m
        List.concat_map
          ~f:(fun txt ->
            (rename
               [
                 ("placeholder", txt); ("Placeholder", uppercase_first_char txt);
               ])
              #structure
              [%str
                module Placeholder = struct
                  let placeholder _ = On.placeholder
                end

                include Placeholder])
          features
        |> B.pmod_structure]

        module Reject (R : sig
          val reject : 'a. unit -> 'a
        end) =
        [%m
        List.concat_map
          ~f:(fun txt ->
            (rename
               [
                 ("placeholder", txt); ("Placeholder", uppercase_first_char txt);
               ])
              #structure
              [%str
                module Placeholder = struct
                  let placeholder _ = R.reject
                end

                include Placeholder])
          features
        |> B.pmod_structure]

        module Id =
        [%m
        List.map
          ~f:(fun txt -> [%stri let [%p B.ppat_var { loc; txt }] = Base.Fn.id])
          features
        |> B.pmod_structure]
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
    Ast_pattern.(
      pstr (pstr_eval (pexp_tuple (many (pexp_ident @@ lident __))) drop ^:: nil))
    expand

let rule = Ppxlib.Context_free.Rule.extension ext
let () = Ppxlib.Driver.register_transformation ~rules:[ rule ] name
