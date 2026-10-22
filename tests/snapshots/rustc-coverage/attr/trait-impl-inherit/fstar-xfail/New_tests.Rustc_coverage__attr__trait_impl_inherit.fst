module New_tests.Rustc_coverage__attr__trait_impl_inherit
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

(* [hax::excluded] t_T — Explicit rejection by a phase in the Hax engine: a node of kind [Trait_item_default] have been found in the AST *)

type t_S = | S : t_S

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_T t_S =
  {
    f_f_pre = (fun (self: t_S) -> true);
    f_f_post = (fun (self: t_S) (out: Prims.unit) -> true);
    f_f
    =
    fun (self: t_S) ->
      let _:Prims.unit =
        Std.Io.Stdio.e_print (Core_models.Fmt.Rt.impl_1__new_const (mk_usize 1)
              (let list = ["impl S\n"] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
            <:
            Core_models.Fmt.t_Arguments)
      in
      let _:Prims.unit = () in
      ()
  }

let main (_: Prims.unit) : Prims.unit =
  let _:Prims.unit = f_f #t_S #FStar.Tactics.Typeclasses.solve (S <: t_S) in
  ()
