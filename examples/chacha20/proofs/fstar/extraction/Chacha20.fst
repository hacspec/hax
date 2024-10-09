module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_bounded_integers in
  ()

let chacha20_line
      (a b d:
          Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
            (Rust_primitives.mk_usize 15))
      (s: u32)
      (m: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) = m in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.update_at state
      a
      (Core.Num.impl__u32__wrapping_add (state.[ a ] <: u32) (state.[ b ] <: u32) <: u32)
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.update_at state d ((state.[ d ] <: u32) ^. (state.[ a ] <: u32) <: u32)
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.update_at state
      d
      (Core.Num.impl__u32__rotate_left (state.[ d ] <: u32) s <: u32)
  in
  state

let chacha20_quarter_round
      (a b c d:
          Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
            (Rust_primitives.mk_usize 15))
      (state: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_line a b d (Rust_primitives.mk_u32 16) state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_line c d b (Rust_primitives.mk_u32 12) state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_line a b d (Rust_primitives.mk_u32 8) state
  in
  chacha20_line c d b (Rust_primitives.mk_u32 7) state

let chacha20_double_round (state: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 0
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 4
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 8
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 12
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 1
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 5
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 9
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 13
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 2
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 6
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 10
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 14
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 3
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 7
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 11
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 15
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 0
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 5
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 10
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 15
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 1
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 6
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 11
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 12
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_quarter_round (Rust_primitives.mk_usize 2
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 7
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 8
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      (Rust_primitives.mk_usize 13
        <:
        Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0)
          (Rust_primitives.mk_usize 15))
      state
  in
  chacha20_quarter_round (Rust_primitives.mk_usize 3
      <:
      Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0) (Rust_primitives.mk_usize 15)
    )
    (Rust_primitives.mk_usize 4
      <:
      Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0) (Rust_primitives.mk_usize 15)
    )
    (Rust_primitives.mk_usize 9
      <:
      Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0) (Rust_primitives.mk_usize 15)
    )
    (Rust_primitives.mk_usize 14
      <:
      Hax_bounded_integers.t_BoundedUsize (Rust_primitives.mk_usize 0) (Rust_primitives.mk_usize 15)
    )
    state

let chacha20_rounds (state: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let st:t_Array u32 (Rust_primitives.mk_usize 16) = state in
  let st:t_Array u32 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_i32 0)
      (Rust_primitives.mk_i32 10)
      (fun st temp_1_ ->
          let st:t_Array u32 (Rust_primitives.mk_usize 16) = st in
          let _:i32 = temp_1_ in
          true)
      st
      (fun st v__i ->
          let st:t_Array u32 (Rust_primitives.mk_usize 16) = st in
          let v__i:i32 = v__i in
          chacha20_double_round st <: t_Array u32 (Rust_primitives.mk_usize 16))
  in
  st

let chacha20_core (ctr: u32) (st0: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) = st0 in
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
      (Rust_primitives.mk_usize 12)
      (Core.Num.impl__u32__wrapping_add (state.[ Rust_primitives.mk_usize 12 ] <: u32) ctr <: u32)
  in
  let k:t_Array u32 (Rust_primitives.mk_usize 16) = chacha20_rounds state in
  Chacha20.Hacspec_helper.add_state state k

let chacha20_encrypt_block
      (st0: t_Array u32 (Rust_primitives.mk_usize 16))
      (ctr: u32)
      (plain: t_Array u8 (Rust_primitives.mk_usize 64))
    : t_Array u8 (Rust_primitives.mk_usize 64) =
  let st:t_Array u32 (Rust_primitives.mk_usize 16) = chacha20_core ctr st0 in
  let (pl: t_Array u32 (Rust_primitives.mk_usize 16)):t_Array u32 (Rust_primitives.mk_usize 16) =
    Chacha20.Hacspec_helper.to_le_u32s_16_ (plain <: t_Slice u8)
  in
  let encrypted:t_Array u32 (Rust_primitives.mk_usize 16) =
    Chacha20.Hacspec_helper.xor_state st pl
  in
  Chacha20.Hacspec_helper.u32s_to_le_bytes encrypted

let chacha20_encrypt_last
      (st0: t_Array u32 (Rust_primitives.mk_usize 16))
      (ctr: u32)
      (plain: t_Slice u8)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (requires (Core.Slice.impl__len #u8 plain <: usize) <=. Rust_primitives.mk_usize 64)
      (fun _ -> Prims.l_True) =
  let (b: t_Array u8 (Rust_primitives.mk_usize 64)):t_Array u8 (Rust_primitives.mk_usize 64) =
    Rust_primitives.Hax.repeat (Rust_primitives.mk_u8 0) (Rust_primitives.mk_usize 64)
  in
  let b:t_Array u8 (Rust_primitives.mk_usize 64) = Chacha20.Hacspec_helper.update_array b plain in
  let b:t_Array u8 (Rust_primitives.mk_usize 64) = chacha20_encrypt_block st0 ctr b in
  Alloc.Slice.impl__to_vec #u8
    (b.[ {
          Core.Ops.Range.f_start = Rust_primitives.mk_usize 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 plain <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)

let chacha20_init
      (key: t_Array u8 (Rust_primitives.mk_usize 32))
      (iv: t_Array u8 (Rust_primitives.mk_usize 12))
      (ctr: u32)
    : t_Array u32 (Rust_primitives.mk_usize 16) =
  let (key_u32: t_Array u32 (Rust_primitives.mk_usize 8)):t_Array u32 (Rust_primitives.mk_usize 8) =
    Chacha20.Hacspec_helper.to_le_u32s_8_ (key <: t_Slice u8)
  in
  let (iv_u32: t_Array u32 (Rust_primitives.mk_usize 3)):t_Array u32 (Rust_primitives.mk_usize 3) =
    Chacha20.Hacspec_helper.to_le_u32s_3_ (iv <: t_Slice u8)
  in
  let list =
    [
      Rust_primitives.mk_u32 1634760805; Rust_primitives.mk_u32 857760878;
      Rust_primitives.mk_u32 2036477234; Rust_primitives.mk_u32 1797285236;
      key_u32.[ Rust_primitives.mk_usize 0 ]; key_u32.[ Rust_primitives.mk_usize 1 ];
      key_u32.[ Rust_primitives.mk_usize 2 ]; key_u32.[ Rust_primitives.mk_usize 3 ];
      key_u32.[ Rust_primitives.mk_usize 4 ]; key_u32.[ Rust_primitives.mk_usize 5 ];
      key_u32.[ Rust_primitives.mk_usize 6 ]; key_u32.[ Rust_primitives.mk_usize 7 ]; ctr;
      iv_u32.[ Rust_primitives.mk_usize 0 ]; iv_u32.[ Rust_primitives.mk_usize 1 ];
      iv_u32.[ Rust_primitives.mk_usize 2 ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
  Rust_primitives.Hax.array_of_list 16 list

let chacha20_key_block (state: t_Array u32 (Rust_primitives.mk_usize 16))
    : t_Array u8 (Rust_primitives.mk_usize 64) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_core (Rust_primitives.mk_u32 0) state
  in
  Chacha20.Hacspec_helper.u32s_to_le_bytes state

let chacha20_key_block0
      (key: t_Array u8 (Rust_primitives.mk_usize 32))
      (iv: t_Array u8 (Rust_primitives.mk_usize 12))
    : t_Array u8 (Rust_primitives.mk_usize 64) =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) =
    chacha20_init key iv (Rust_primitives.mk_u32 0)
  in
  chacha20_key_block state

let chacha20_update (st0: t_Array u32 (Rust_primitives.mk_usize 16)) (m: t_Slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let num_blocks:usize = (Core.Slice.impl__len #u8 m <: usize) /! Rust_primitives.mk_usize 64 in
  let remainder_len:usize = (Core.Slice.impl__len #u8 m <: usize) %! Rust_primitives.mk_usize 64 in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Rust_primitives.Hax.Folds.fold_range (Rust_primitives.mk_usize 0)
      num_blocks
      (fun blocks_out temp_1_ ->
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = blocks_out in
          let _:usize = temp_1_ in
          true)
      blocks_out
      (fun blocks_out i ->
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = blocks_out in
          let i:usize = i in
          let b:t_Array u8 (Rust_primitives.mk_usize 64) =
            chacha20_encrypt_block st0
              (cast (i <: usize) <: u32)
              (Core.Result.impl__unwrap #(t_Array u8 (Rust_primitives.mk_usize 64))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (Rust_primitives.mk_usize 64))
                      #FStar.Tactics.Typeclasses.solve
                      (m.[ {
                            Core.Ops.Range.f_start = Rust_primitives.mk_usize 64 *! i <: usize;
                            Core.Ops.Range.f_end
                            =
                            (Rust_primitives.mk_usize 64 *! i <: usize) +!
                            Rust_primitives.mk_usize 64
                            <:
                            usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result (t_Array u8 (Rust_primitives.mk_usize 64))
                      Core.Array.t_TryFromSliceError)
                <:
                t_Array u8 (Rust_primitives.mk_usize 64))
          in
          let _:Prims.unit =
            Hax_lib.v_assume ((Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global blocks_out <: usize) =.
                (i *! Rust_primitives.mk_usize 64 <: usize)
                <:
                bool)
          in
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_2__extend_from_slice #u8
              #Alloc.Alloc.t_Global
              blocks_out
              (b <: t_Slice u8)
          in
          blocks_out)
  in
  let _:Prims.unit =
    Hax_lib.v_assume ((Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global blocks_out <: usize) =.
        (num_blocks *! Rust_primitives.mk_usize 64 <: usize)
        <:
        bool)
  in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if remainder_len <>. Rust_primitives.mk_usize 0
    then
      let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        chacha20_encrypt_last st0
          (cast (num_blocks <: usize) <: u32)
          (m.[ {
                Core.Ops.Range.f_start = Rust_primitives.mk_usize 64 *! num_blocks <: usize;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 m <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
      in
      let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        Alloc.Vec.impl_2__extend_from_slice #u8
          #Alloc.Alloc.t_Global
          blocks_out
          (Core.Ops.Deref.f_deref #(Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
              #FStar.Tactics.Typeclasses.solve
              b
            <:
            t_Slice u8)
      in
      blocks_out
    else blocks_out
  in
  blocks_out

let chacha20
      (m: t_Slice u8)
      (key: t_Array u8 (Rust_primitives.mk_usize 32))
      (iv: t_Array u8 (Rust_primitives.mk_usize 12))
      (ctr: u32)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let state:t_Array u32 (Rust_primitives.mk_usize 16) = chacha20_init key iv ctr in
  chacha20_update state m
