open Base
open Utils

module%inlined_contents Make (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.Off.Macro
  end

  module A = Ast.Make (FA)
  module B = Ast.Make (FB)

  module S = struct
    include Features.SUBTYPE.Id

    let macro _ = failwith "macro in expression"
  end

  let metadata = Desugar_utils.Metadata.make "desugar_legacy_hacspec_lib"

  module UA = Ast_utils.Make (FA)
  module UB = Ast_utils.Make (FB)

  [%%inline_defs "*" - ditem - ditem']

  let ns_gident (n : string * string list) (last_chunk : string) : global_ident
      =
    let path = Non_empty_list.of_list_exn (snd n @ [ last_chunk ]) in
    `Concrete { crate = fst n; path }

  let empty_generics = B.{ params = []; constraints = [] }

  let hacspec_lib_item s =
    `Concrete { crate = "hacspec"; path = Non_empty_list.[ "lib"; s ] }

  let mk_ty_alias ~name ty = B.TyAlias { name; generics = empty_generics; ty }

  let mk_tapp ~name args =
    B.TApp
      {
        ident = hacspec_lib_item name;
        args = List.map ~f:(fun x -> B.GType x) args;
      }

  let mk_ty_name ~name = mk_tapp ~name []

  let rec ditem (item : A.item) : B.item list =
    match item.v with
    | [%inline_arms "ditem'.*"] ->
        map (fun v ->
            [
              B.
                {
                  v;
                  span = item.span;
                  parent_namespace = item.parent_namespace;
                };
            ])
  (* | IMacroInvokation { macro = `Concrete c; argument; span } -> *)
  (*     failwith @@ [%show: concrete_ident] c *)
  (* | IMacroInvokation *)
  (*     { *)
  (*       macro = *)
  (*         `Concrete *)
  (*           Non_empty_list. *)
  (*             { crate = "hacspec_lib"; path = [ "array"; "array" ] }; *)
  (*       argument; *)
  (*       span; *)
  (*     } -> *)
  (*     let open Hacspeclib_macro_parser in *)
  (*     let o : Array.t = Array.parse argument |> Result.ok_or_failwith in *)
  (*     [ *)
  (*       B. *)
  (*         { *)
  (*           parent_namespace = item.parent_namespace; *)
  (*           span = item.span; *)
  (*           v = *)
  (*             mk_ty_alias ~name:(ns_gident item.parent_namespace o.array_name) *)
  (*             @@ mk_tapp "lseq" *)
  (*                  [ mk_ty_name o.typ; mk_ty_name (string_of_int o.size) ]; *)
  (*         }; *)
  (*     ] *)
  (* | IMacroInvokation _ -> [] *)

  module FA = FA
end
[@@add "subtype.ml"]
