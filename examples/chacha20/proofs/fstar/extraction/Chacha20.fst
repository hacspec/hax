module Chacha20
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_secret_integers.Public_integers in
  ()

let chacha20_line (a b d: usize) (s: u32) (m: t_Array u32 (sz 16))
    : Prims.Pure (t_Array u32 (sz 16))
      (requires a <. sz 16 && b <. sz 16 && d <. sz 16)
      (fun _ -> Prims.l_True) =
  let state:t_Array u32 (sz 16) = m in
  let state:t_Array u32 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
      a
      (Core.Num.impl__u32__wrapping_add (state.[ a ] <: u32) (state.[ b ] <: u32) <: u32)
  in
  let state:t_Array u32 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
      d
      ((state.[ d ] <: u32) ^. (state.[ a ] <: u32) <: u32)
  in
  let state:t_Array u32 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
      d
      (Core.Num.impl__u32__rotate_left (state.[ d ] <: u32) s <: u32)
  in
  state

let chacha20_quarter_round (a b c d: usize) (state: t_Array u32 (sz 16))
    : Prims.Pure (t_Array u32 (sz 16))
      (requires a <. sz 16 && b <. sz 16 && c <. sz 16 && d <. sz 16)
      (fun _ -> Prims.l_True) =
  let state:t_Array u32 (sz 16) = chacha20_line a b d 16ul state in
  let state:t_Array u32 (sz 16) = chacha20_line c d b 12ul state in
  let state:t_Array u32 (sz 16) = chacha20_line a b d 8ul state in
  chacha20_line c d b 7ul state

let chacha20_double_round (state: t_Array u32 (sz 16)) : t_Array u32 (sz 16) =
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 0) (sz 4) (sz 8) (sz 12) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 1) (sz 5) (sz 9) (sz 13) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 2) (sz 6) (sz 10) (sz 14) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 3) (sz 7) (sz 11) (sz 15) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 0) (sz 5) (sz 10) (sz 15) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 1) (sz 6) (sz 11) (sz 12) state in
  let state:t_Array u32 (sz 16) = chacha20_quarter_round (sz 2) (sz 7) (sz 8) (sz 13) state in
  chacha20_quarter_round (sz 3) (sz 4) (sz 9) (sz 14) state

let chacha20_rounds (state: t_Array u32 (sz 16)) : t_Array u32 (sz 16) =
  let st:t_Array u32 (sz 16) = state in
  let st:t_Array u32 (sz 16) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            i32)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = 0l; Core.Ops.Range.f_end = 10l } <: Core.Ops.Range.t_Range i32
          )
        <:
        Core.Ops.Range.t_Range i32)
      st
      (fun st v__i ->
          let st:t_Array u32 (sz 16) = st in
          let v__i:i32 = v__i in
          chacha20_double_round st <: t_Array u32 (sz 16))
  in
  st

let chacha20_core (ctr: u32) (st0: t_Array u32 (sz 16)) : t_Array u32 (sz 16) =
  let state:t_Array u32 (sz 16) = st0 in
  let state:t_Array u32 (sz 16) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
      (sz 12)
      (Core.Num.impl__u32__wrapping_add (state.[ sz 12 ] <: u32) ctr <: u32)
  in
  let k:t_Array u32 (sz 16) = chacha20_rounds state in
  Core.Array.from_fn #u32
    (sz 16)
    (fun i ->
        let i:usize = i in
        Core.Num.impl__u32__wrapping_add (state.[ i ] <: u32) (k.[ i ] <: u32) <: u32)

let chacha20_key_block (state: t_Array u32 (sz 16)) : t_Array u8 (sz 64) =
  let state:t_Array u32 (sz 16) = chacha20_core 0ul state in
  Core.Result.impl__unwrap #(t_Array u8 (sz 64))
    #Prims.unit
    (Hax_secret_integers.Traits.f_try_to_le_bytes #(t_Array u32 (sz 16))
        #u8
        #(sz 64)
        #FStar.Tactics.Typeclasses.solve
        state
      <:
      Core.Result.t_Result (t_Array u8 (sz 64)) Prims.unit)

let chacha20_encrypt_block (st0: t_Array u32 (sz 16)) (ctr: u32) (plain: t_Array u8 (sz 64))
    : t_Array u8 (sz 64) =
  let st:t_Array u32 (sz 16) = chacha20_core ctr st0 in
  let (pl: t_Array u32 (sz 16)):t_Array u32 (sz 16) =
    Core.Result.impl__unwrap #(t_Array u32 (sz 16))
      #Prims.unit
      (Hax_secret_integers.Traits.f_try_from_le_bytes #(t_Array u32 (sz 16))
          #u8
          #FStar.Tactics.Typeclasses.solve
          (Rust_primitives.unsize plain <: t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u32 (sz 16)) Prims.unit)
  in
  let (encrypted: t_Array u32 (sz 16)):t_Array u32 (sz 16) =
    Core.Array.from_fn #u32
      (sz 16)
      (fun i ->
          let i:usize = i in
          (st.[ i ] <: u32) ^. (pl.[ i ] <: u32) <: u32)
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 64))
    #Prims.unit
    (Hax_secret_integers.Traits.f_try_to_le_bytes #(t_Array u32 (sz 16))
        #u8
        #(sz 64)
        #FStar.Tactics.Typeclasses.solve
        encrypted
      <:
      Core.Result.t_Result (t_Array u8 (sz 64)) Prims.unit)

let chacha20_encrypt_last (st0: t_Array u32 (sz 16)) (ctr: u32) (plain: t_Slice u8)
    : Prims.Pure (Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
      (requires (Core.Slice.impl__len #u8 plain <: usize) <=. sz 64)
      (fun _ -> Prims.l_True) =
  let (b: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Rust_primitives.Hax.repeat (Hax_secret_integers.Traits.f_classify #u8
          #FStar.Tactics.Typeclasses.solve
          0uy
        <:
        u8)
      (sz 64)
  in
  let b:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_range b
      ({
          Core.Ops.Range.f_start = sz 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 plain <: usize
        }
        <:
        Core.Ops.Range.t_Range usize)
      (Core.Slice.impl__copy_from_slice #u8
          (b.[ {
                Core.Ops.Range.f_start = sz 0;
                Core.Ops.Range.f_end = Core.Slice.impl__len #u8 plain <: usize
              }
              <:
              Core.Ops.Range.t_Range usize ]
            <:
            t_Slice u8)
          plain
        <:
        t_Slice u8)
  in
  let b:t_Array u8 (sz 64) = chacha20_encrypt_block st0 ctr b in
  Alloc.Slice.impl__to_vec #u8
    (b.[ {
          Core.Ops.Range.f_start = sz 0;
          Core.Ops.Range.f_end = Core.Slice.impl__len #u8 plain <: usize
        }
        <:
        Core.Ops.Range.t_Range usize ]
      <:
      t_Slice u8)

let chacha20_init (key: t_Array u8 (sz 32)) (iv: t_Array u8 (sz 12)) (ctr: u32)
    : t_Array u32 (sz 16) =
  let (key_u32: t_Array u32 (sz 8)):t_Array u32 (sz 8) =
    Core.Result.impl__unwrap #(t_Array u32 (sz 8))
      #Prims.unit
      (Hax_secret_integers.Traits.f_try_from_le_bytes #(t_Array u32 (sz 8))
          #u8
          #FStar.Tactics.Typeclasses.solve
          (Rust_primitives.unsize key <: t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u32 (sz 8)) Prims.unit)
  in
  let (iv_u32: t_Array u32 (sz 3)):t_Array u32 (sz 3) =
    Core.Result.impl__unwrap #(t_Array u32 (sz 3))
      #Prims.unit
      (Hax_secret_integers.Traits.f_try_from_le_bytes #(t_Array u32 (sz 3))
          #u8
          #FStar.Tactics.Typeclasses.solve
          (Rust_primitives.unsize iv <: t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u32 (sz 3)) Prims.unit)
  in
  let list =
    [
      Hax_secret_integers.Traits.f_classify #u32 #FStar.Tactics.Typeclasses.solve 1634760805ul;
      Hax_secret_integers.Traits.f_classify #u32 #FStar.Tactics.Typeclasses.solve 857760878ul;
      Hax_secret_integers.Traits.f_classify #u32 #FStar.Tactics.Typeclasses.solve 2036477234ul;
      Hax_secret_integers.Traits.f_classify #u32 #FStar.Tactics.Typeclasses.solve 1797285236ul;
      key_u32.[ sz 0 ]; key_u32.[ sz 1 ]; key_u32.[ sz 2 ]; key_u32.[ sz 3 ]; key_u32.[ sz 4 ];
      key_u32.[ sz 5 ]; key_u32.[ sz 6 ]; key_u32.[ sz 7 ];
      Hax_secret_integers.Traits.f_classify #u32 #FStar.Tactics.Typeclasses.solve ctr;
      iv_u32.[ sz 0 ]; iv_u32.[ sz 1 ]; iv_u32.[ sz 2 ]
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
  Rust_primitives.Hax.array_of_list 16 list

let chacha20_key_block0 (key: t_Array u8 (sz 32)) (iv: t_Array u8 (sz 12)) : t_Array u8 (sz 64) =
  let state:t_Array u32 (sz 16) = chacha20_init key iv 0ul in
  chacha20_key_block state

let chacha20_update (st0: t_Array u32 (sz 16)) (m: t_Slice u8)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.impl__new #u8 () in
  let num_blocks:usize = (Core.Slice.impl__len #u8 m <: usize) /! sz 64 in
  let remainder_len:usize = (Core.Slice.impl__len #u8 m <: usize) %! sz 64 in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = num_blocks }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      blocks_out
      (fun blocks_out i ->
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = blocks_out in
          let i:usize = i in
          let b:t_Array u8 (sz 64) =
            chacha20_encrypt_block st0
              (cast (i <: usize) <: u32)
              (Core.Result.impl__unwrap #(t_Array u8 (sz 64))
                  #Core.Array.t_TryFromSliceError
                  (Core.Convert.f_try_into #(t_Slice u8)
                      #(t_Array u8 (sz 64))
                      #FStar.Tactics.Typeclasses.solve
                      (m.[ {
                            Core.Ops.Range.f_start = sz 64 *! i <: usize;
                            Core.Ops.Range.f_end = (sz 64 *! i <: usize) +! sz 64 <: usize
                          }
                          <:
                          Core.Ops.Range.t_Range usize ]
                        <:
                        t_Slice u8)
                    <:
                    Core.Result.t_Result (t_Array u8 (sz 64)) Core.Array.t_TryFromSliceError)
                <:
                t_Array u8 (sz 64))
          in
          let _:Prims.unit =
            Hax_lib.v_assume ((Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global blocks_out <: usize) =.
                (i *! sz 64 <: usize)
                <:
                bool)
          in
          let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_2__extend_from_slice #u8
              #Alloc.Alloc.t_Global
              blocks_out
              (Rust_primitives.unsize b <: t_Slice u8)
          in
          blocks_out)
  in
  let _:Prims.unit =
    Hax_lib.v_assume ((Alloc.Vec.impl_1__len #u8 #Alloc.Alloc.t_Global blocks_out <: usize) =.
        (num_blocks *! sz 64 <: usize)
        <:
        bool)
  in
  let blocks_out:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    if remainder_len <>. sz 0
    then
      let b:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
        chacha20_encrypt_last st0
          (cast (num_blocks <: usize) <: u32)
          (m.[ {
                Core.Ops.Range.f_start = sz 64 *! num_blocks <: usize;
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

let chacha20 (m: t_Slice u8) (key: t_Array u8 (sz 32)) (iv: t_Array u8 (sz 12)) (ctr: u32)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let state:t_Array u32 (sz 16) = chacha20_init key iv ctr in
  chacha20_update state m
