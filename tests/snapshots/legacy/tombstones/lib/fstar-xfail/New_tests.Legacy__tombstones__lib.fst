module New_tests.Legacy__tombstones__lib
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Core_models

let clean_add (a b: u8) : u8 = a +! b

(* [hax::excluded] t_RawHolder — Explicit rejection by a phase in the Hax engine: a node of kind [Raw_pointer] have been found in the AST *)

class t_Speak (v_Self: Type0) = {
  f_hello_pre:v_Self -> Type0;
  f_hello_post:v_Self -> u8 -> Type0;
  f_hello:x0: v_Self -> Prims.Pure u8 (f_hello_pre x0) (fun result -> f_hello_post x0 result)
}

type t_Cat = | Cat : t_Cat

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Speak t_Cat =
  {
    f_hello_pre = (fun (self: t_Cat) -> true);
    f_hello_post = (fun (self: t_Cat) (out: u8) -> true);
    f_hello = fun (self: t_Cat) -> mk_u8 1
  }

/// @fail(extraction): ssprove(HAX0008), proverif(HAX0008), coq(HAX0008)
let dyn_in_sig (x: dyn 1 (fun z -> t_Speak z)) : u8 =
  f_hello #(dyn 1 (fun z -> t_Speak z)) #FStar.Tactics.Typeclasses.solve x

/// @fail(extraction): proverif(HAX0008, HAX0008, HAX0008), coq(HAX0008, HAX0008, HAX0008), ssprove(HAX0008, HAX0008, HAX0008)
let dyn_in_body (_: Prims.unit) : u8 =
  let c:t_Cat = Cat <: t_Cat in
  let (d: dyn 1 (fun z -> t_Speak z)):dyn 1 (fun z -> t_Speak z) = Rust_primitives.unsize c in
  f_hello #(dyn 1 (fun z -> t_Speak z)) #FStar.Tactics.Typeclasses.solve d

/// @fail(extraction): coq(HAX0010, HAX0003), ssprove(HAX0003, HAX0010), legacy-lean(HAX0010, HAX0003), fstar(HAX0010, HAX0003), proverif(HAX0010, HAX0003)
let mut_ref_return (x: u8) : Rust_primitives.Hax.t_Failure "" =
  Rust_primitives.Hax.failure "[hax::opaque] The mutation of this &mut is not allowed here." ""

/// @fail(extraction): proverif(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), legacy-lean(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), ssprove(HAX0003, HAX0003, HAX0003, HAX0010, HAX0010, HAX0010), coq(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003), fstar(HAX0010, HAX0010, HAX0010, HAX0003, HAX0003, HAX0003)
let body_split (buf: t_Slice u8) : u8 =
  Rust_primitives.Hax.failure "[hax::opaque] The mutation of this &mut is not allowed here." ""
