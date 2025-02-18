module Chacha20.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let to_le_u32s_3_ (bytes: t_Slice u8) : t_Array u32 (mk_usize 3) =
  let out:t_Array u32 (mk_usize 3) = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 3) in
  let out:t_Array u32 (mk_usize 3) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 3)
      (fun out temp_1_ ->
          let out:t_Array u32 (mk_usize 3) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u32 (mk_usize 3) = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Core.Num.impl_u32__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 4))
                    #Core.Array.t_TryFromSliceError
                    (Core.Convert.f_try_into #(t_Slice u8)
                        #(t_Array u8 (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        (bytes.[ {
                              Core.Ops.Range.f_start = mk_usize 4 *! i <: usize;
                              Core.Ops.Range.f_end
                              =
                              (mk_usize 4 *! i <: usize) +! mk_usize 4 <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (mk_usize 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (mk_usize 4))
              <:
              u32)
          <:
          t_Array u32 (mk_usize 3))
  in
  out

let to_le_u32s_8_ (bytes: t_Slice u8) : t_Array u32 (mk_usize 8) =
  let out:t_Array u32 (mk_usize 8) = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 8) in
  let out:t_Array u32 (mk_usize 8) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 8)
      (fun out temp_1_ ->
          let out:t_Array u32 (mk_usize 8) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u32 (mk_usize 8) = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Core.Num.impl_u32__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 4))
                    #Core.Array.t_TryFromSliceError
                    (Core.Convert.f_try_into #(t_Slice u8)
                        #(t_Array u8 (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        (bytes.[ {
                              Core.Ops.Range.f_start = mk_usize 4 *! i <: usize;
                              Core.Ops.Range.f_end
                              =
                              (mk_usize 4 *! i <: usize) +! mk_usize 4 <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (mk_usize 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (mk_usize 4))
              <:
              u32)
          <:
          t_Array u32 (mk_usize 8))
  in
  out

let to_le_u32s_16_ (bytes: t_Slice u8) : t_Array u32 (mk_usize 16) =
  let out:t_Array u32 (mk_usize 16) = Rust_primitives.Hax.repeat (mk_u32 0) (mk_usize 16) in
  let out:t_Array u32 (mk_usize 16) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun out temp_1_ ->
          let out:t_Array u32 (mk_usize 16) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u32 (mk_usize 16) = out in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
            i
            (Core.Num.impl_u32__from_le_bytes (Core.Result.impl__unwrap #(t_Array u8 (mk_usize 4))
                    #Core.Array.t_TryFromSliceError
                    (Core.Convert.f_try_into #(t_Slice u8)
                        #(t_Array u8 (mk_usize 4))
                        #FStar.Tactics.Typeclasses.solve
                        (bytes.[ {
                              Core.Ops.Range.f_start = mk_usize 4 *! i <: usize;
                              Core.Ops.Range.f_end
                              =
                              (mk_usize 4 *! i <: usize) +! mk_usize 4 <: usize
                            }
                            <:
                            Core.Ops.Range.t_Range usize ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (mk_usize 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (mk_usize 4))
              <:
              u32)
          <:
          t_Array u32 (mk_usize 16))
  in
  out

let u32s_to_le_bytes (state: t_Array u32 (mk_usize 16)) : t_Array u8 (mk_usize 64) =
  let out:t_Array u8 (mk_usize 64) = Rust_primitives.Hax.repeat (mk_u8 0) (mk_usize 64) in
  let out:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #u32 (state <: t_Slice u32) <: usize)
      (fun out temp_1_ ->
          let out:t_Array u8 (mk_usize 64) = out in
          let _:usize = temp_1_ in
          true)
      out
      (fun out i ->
          let out:t_Array u8 (mk_usize 64) = out in
          let i:usize = i in
          let tmp:t_Array u8 (mk_usize 4) = Core.Num.impl_u32__to_le_bytes (state.[ i ] <: u32) in
          Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
            (mk_usize 4)
            (fun out temp_1_ ->
                let out:t_Array u8 (mk_usize 64) = out in
                let _:usize = temp_1_ in
                true)
            out
            (fun out j ->
                let out:t_Array u8 (mk_usize 64) = out in
                let j:usize = j in
                Rust_primitives.Hax.Monomorphized_update_at.update_at_usize out
                  ((i *! mk_usize 4 <: usize) +! j <: usize)
                  (tmp.[ j ] <: u8)
                <:
                t_Array u8 (mk_usize 64)))
  in
  out

let xor_state (state other: t_Array u32 (mk_usize 16)) : t_Array u32 (mk_usize 16) =
  let state:t_Array u32 (mk_usize 16) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun state temp_1_ ->
          let state:t_Array u32 (mk_usize 16) = state in
          let _:usize = temp_1_ in
          true)
      state
      (fun state i ->
          let state:t_Array u32 (mk_usize 16) = state in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            i
            ((state.[ i ] <: u32) ^. (other.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (mk_usize 16))
  in
  state

let add_state (state other: t_Array u32 (mk_usize 16)) : t_Array u32 (mk_usize 16) =
  let state:t_Array u32 (mk_usize 16) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (mk_usize 16)
      (fun state temp_1_ ->
          let state:t_Array u32 (mk_usize 16) = state in
          let _:usize = temp_1_ in
          true)
      state
      (fun state i ->
          let state:t_Array u32 (mk_usize 16) = state in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize state
            i
            (Core.Num.impl_u32__wrapping_add (state.[ i ] <: u32) (other.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (mk_usize 16))
  in
  state

let update_array (array: t_Array u8 (mk_usize 64)) (v_val: t_Slice u8) : t_Array u8 (mk_usize 64) =
  let _:Prims.unit =
    Hax_lib.v_assert (mk_usize 64 >=. (Core.Slice.impl__len #u8 v_val <: usize) <: bool)
  in
  let array:t_Array u8 (mk_usize 64) =
    Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
      (Core.Slice.impl__len #u8 v_val <: usize)
      (fun array temp_1_ ->
          let array:t_Array u8 (mk_usize 64) = array in
          let _:usize = temp_1_ in
          true)
      array
      (fun array i ->
          let array:t_Array u8 (mk_usize 64) = array in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize array i (v_val.[ i ] <: u8)
          <:
          t_Array u8 (mk_usize 64))
  in
  array
