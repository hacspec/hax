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
    inherit Ast_traverse.map as super
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
  (* let add_derivings t = [%type: [%t t] [@deriving show, yojson, eq]] in *)
  let (module B) = Ast_builder.make loc in
  (* let template = [%sigi: type name [@@deriving show, yojson, eq] ] in *)
  [%stri
    include struct
      module type FEATURES = sig
        include
          [%m
        List.map
          ~f:(fun txt ->
            (rename [ ("placeholder", txt) ])#signature_item
              [%sigi: type placeholder [@@deriving show, yojson, eq]])
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
                    ~payload:(PStr [%str show, yojson, eq]);
                ];
            };
          ]]
      end

      module DefaultClasses (F : T) = struct
        open Base

        (*   (\* TODO: generate those classes automatically *\) *)
        class virtual ['self] default_reduce_features =
          object (self : 'self)
            (* [%m inherit [_] VisitorsRuntime.reduce] *)
            (*       inherit [_] VisitorsRuntime.reduce *)

            (*       (\* todo: here I force unit to get rid of generalization issues *)
            (*          Instead, TODO: split this class into multiple *)
            (*       *\) *)
            (*       method visit_loop () (_ : F.loop) = self#zero *)
            (*       method visit_continue () (_ : F.continue) = self#zero *)
            (*       method visit_mutable_variable () (_ : F.mutable_variable) = self#zero *)
            (*       method visit_mutable_reference () (_ : F.mutable_reference) = self#zero *)
            (*       method visit_mutable_pointer () (_ : F.mutable_pointer) = self#zero *)
            (*       method visit_reference () (_ : F.reference) = self#zero *)
            (*       method visit_slice () (_ : F.slice) = self#zero *)
            (*       method visit_raw_pointer () (_ : F.raw_pointer) = self#zero *)
            (*       method visit_early_exit () (_ : F.early_exit) = self#zero *)
            (*       method visit_macro () (_ : F.macro) = self#zero *)
            (*       method visit_as_pattern () (_ : F.as_pattern) = self#zero *)
            (*       method visit_lifetime () (_ : F.lifetime) = self#zero *)
            (*       method visit_monadic_action () (_ : F.monadic_action) = self#zero *)
            (*       method visit_monadic_binding () (_ : F.monadic_binding) = self#zero *)
            
          end

        (*   class virtual ['self] default_map_features = *)
        (*     object (self : 'self) *)
        (*       inherit ['env] VisitorsRuntime.map *)

        (*       (\* todo: here I force unit to get rid of generalization issues *)
        (*          Instead, TODO: split this class into multiple *)
        (*       *\) *)
        (*       method visit_loop: 'env -> F.loop -> F.loop = Fn.const Fn.id *)
        (*       method visit_continue: 'env -> F.continue -> F.continue = Fn.const Fn.id *)
        (*       method visit_mutable_variable: 'env -> F.mutable_variable -> F.mutable_variable = Fn.const Fn.id *)
        (*       method visit_mutable_reference: 'env -> F.mutable_reference -> F.mutable_reference = Fn.const Fn.id *)
        (*       method visit_mutable_pointer: 'env -> F.mutable_pointer -> F.mutable_pointer = Fn.const Fn.id *)
        (*       method visit_reference: 'env -> F.reference -> F.reference = Fn.const Fn.id *)
        (*       method visit_slice: 'env -> F.slice -> F.slice = Fn.const Fn.id *)
        (*       method visit_raw_pointer: 'env -> F.raw_pointer -> F.raw_pointer = Fn.const Fn.id *)
        (*       method visit_early_exit: 'env -> F.early_exit -> F.early_exit = Fn.const Fn.id *)
        (*       method visit_macro: 'env -> F.macro -> F.macro = Fn.const Fn.id *)
        (*       method visit_as_pattern: 'env -> F.as_pattern -> F.as_pattern = Fn.const Fn.id *)
        (*       method visit_lifetime: 'env -> F.lifetime -> F.lifetime = Fn.const Fn.id *)
        (*       method visit_monadic_action: 'env -> F.monadic_action -> F.monadic_action = Fn.const Fn.id *)
        (*       method visit_monadic_binding: 'env -> F.monadic_binding -> F.monadic_binding = Fn.const Fn.id *)
        (*     end *)
      end

      module MapFeatureTypes (T : sig
        type t [@@deriving show, yojson, eq]
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
                    type placeholder = T.t [@@deriving show, yojson, eq]
                  end

                  include Placeholder])
            features
          |> B.pmod_structure]
      end

      module On = MapFeatureTypes (struct
        type t = on [@@deriving show, yojson, eq]
      end)

      module Off = MapFeatureTypes (struct
        type t = off [@@deriving show, yojson, eq]
      end)

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

        module type T_Exn = sig
          include T

          type error [@@deriving show, yojson, eq]

          exception E of error
        end

        module WrapExns (S : T_Exn) =
        [%m
        B.pmod_structure
        @@ [%str
             type error = S.error * Enumeration.t [@@deriving show, yojson, eq]

             exception E of error]
        @ List.map
            ~f:(fun txt ->
              [%stri
                let [%p B.ppat_var { loc; txt }] =
                 fun x ->
                  try
                    [%e B.pexp_ident @@ { loc; txt = Ldot (Lident "S", txt) }] x
                  with S.E err ->
                    raise
                    @@ E
                         ( err,
                           [%e
                             B.pexp_construct
                               {
                                 loc;
                                 txt =
                                   Ldot
                                     ( Lident "Enumeration",
                                       uppercase_first_char txt );
                               }
                               None] )])
            features]

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
