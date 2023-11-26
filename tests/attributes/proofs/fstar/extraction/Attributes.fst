module Attributes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

inline_for_extraction
let hello (x: t_Slice u8) : FStar.HyperStack.ST.St Prims.unit =
  let y:t_Array u8 (sz 4) =
    [@inline_let]
    let list = [10uy; 20uy; 30uy; 40uy] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list list
  in
  let aa:i32 = 3l in
  let aa:i32 = aa +! 1l in
  Rust_primitives.f_for_loop (sz 0)
    (Core.Slice.impl__len x <: usize)
    (fun i ->
        let i:usize = i in
        let lhs:u8 = x.[ i ] in
        let rhs:u8 = y.[ i ] in
        let _:Prims.unit =
          Rust_primitives.Hax.Monomorphized_update_at.update_slice_at_usize x i (lhs +! rhs <: u8)
        in
        ())


inline_for_extraction
let main (): FStar.HyperStack.ST.St u8 =
  let (x: t_Array u8 (sz 4)):t_Array u8 (sz 4) =
    [@inline_let]
    let list = [1uy; 2uy; 3uy; 4uy] in
    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
    Rust_primitives.Hax.array_of_list list
  in
  let _:Prims.unit = hello (Rust_primitives.unsize x <: t_Slice u8) in
  let x1:u8 = x.[ sz 1 ] in
  let x0:u8 = x.[ sz 0 ] in
  let _:Prims.unit =
    Rust_primitives.Hax.Monomorphized_update_at.update_array_at_usize x (sz 0) (x1 +! x0 <: u8)
  in
  x.[ sz 0 ]
