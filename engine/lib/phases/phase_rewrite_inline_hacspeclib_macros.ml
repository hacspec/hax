open Base
open Utils

module%inlined_contents Make (F : Features.T) = struct
  open Ast
  module FA = F

  module FB = struct
    include F
  end

  module A = Ast.Make (F)
  module B = Ast.Make (FB)
  module ImplemT = Phase_utils.MakePhaseImplemT (A) (B)

  module Implem : ImplemT.T = struct
    module UA = Ast_utils.Make (F)
    module UB = Ast_utils.Make (FB)
    include Phase_utils.DefaultError

    module S = struct
      include Features.SUBTYPE.Id
    end

    let metadata = Phase_utils.Metadata.make CfIntoMonads

    [%%inline_defs dmutability + dty + dborrow_kind + dpat]

    open Hacspeclib_macro_parser
    (* module SecretArray = Hacspeclib_macro_parser.SecretArray *)

    let rec dexpr (expr : A.expr) : B.expr =
      let span = expr.span in
      match expr.e with
      | A.MacroInvokation { macro; args; witness } -> (
          let parsing_error details =
            raise
            @@ Diagnostics.Error
                 {
                   context = Backend FStar;
                   kind =
                     ErrorParsingMacroInvocation
                       { macro_id = [%show: global_ident] macro; details };
                   span = Diagnostics.to_thir_span span;
                 }
          in
          let unwrap_or_parse_err (type a) : (a, string) Result.t -> a =
            function
            | Ok x -> x
            | Error e -> parsing_error e
          in
          let expand_secret_array int_typ_size array_values =
            (* unwrapped, public, integers *)
            let array_values =
              List.map
                ~f:(fun (value, kind) ->
                  B.
                    {
                      e = B.Literal (Ast.Int { value; kind });
                      typ = B.TInt kind;
                      span;
                    })
                array_values
            in
            let str_size =
              Ast.string_of_size int_typ_size
              |> Option.value_or_thunk ~default:(fun _ ->
                     parsing_error "Got USize")
            in
            let secret_typ =
              let ident =
                let path = Non_empty_list.[ "U" ^ str_size ] in
                `Concrete Ast.{ crate = "dummy"; path }
              in
              B.TApp { ident; args = [] }
            in
            let array_values =
              List.map
                ~f:(fun v ->
                  UB.call "dummy" ("U" ^ str_size) [] [ v ] span secret_typ)
                array_values
            in
            let e = B.Array array_values in
            let length = List.length array_values in
            B.{ e; span; typ = B.TArray { typ = secret_typ; length } }
          in
          match macro with
          | `Concrete
              Non_empty_list.
                { crate = "hacspec_lib"; path = [ "array"; "secret_array" ] } ->
              let SecretArray.{ int_typ_size; array_values } =
                SecretArray.parse args |> unwrap_or_parse_err
              in
              expand_secret_array int_typ_size array_values
          | `Concrete
              Non_empty_list.
                { crate = "hacspec_lib"; path = [ "array"; "secret_bytes" ] } ->
              let array_values =
                SecretBytes.parse args |> unwrap_or_parse_err
              in
              let int_typ_size = Ast.S8 in
              expand_secret_array int_typ_size array_values
          | _ ->
              B.
                {
                  e = MacroInvokation { macro; args; witness };
                  typ = dty span expr.typ;
                  span;
                })
      | [%inline_arms "dexpr'.*" - MacroInvokation] ->
          map (fun e -> B.{ e; typ = dty expr.span expr.typ; span = expr.span })

    and dloop_kind = [%inline_body dloop_kind]
    and dloop_state = [%inline_body dloop_state]
    and darm = [%inline_body darm]
    and darm' = [%inline_body darm']
    and dlhs = [%inline_body dlhs]
    and dsupported_monads = [%inline_body dsupported_monads]

    [%%inline_defs "Item.*"]
  end

  include Implem
end
[@@add "subtype.ml"]
