module Chacha20.Hacspec_helper
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let to_le_u32s_3_ (bytes: t_Slice u8) : t_Array u32 (sz 3) =
  let out:t_Array u32 (sz 3) = Rust_primitives.Hax.repeat 0ul (sz 3) in
  let out:t_Array u32 (sz 3) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 3
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            (Core.Num.impl__u32__from_le_bytes (Core.Result.impl__unwrap (Core.Convert.f_try_into (bytes.[
                            {
                              Core.Ops.Range.f_start = sz 4 *! i <: usize;
                              Core.Ops.Range.f_end = (sz 4 *! i <: usize) +! sz 4 <: usize
                            } ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (sz 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (sz 4))
              <:
              u32)
          <:
          t_Array u32 (sz 3))
  in
  out

let to_le_u32s_8_ (bytes: t_Slice u8) : t_Array u32 (sz 8) =
  let out:t_Array u32 (sz 8) = Rust_primitives.Hax.repeat 0ul (sz 8) in
  let out:t_Array u32 (sz 8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 8
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            (Core.Num.impl__u32__from_le_bytes (Core.Result.impl__unwrap (Core.Convert.f_try_into (bytes.[
                            {
                              Core.Ops.Range.f_start = sz 4 *! i <: usize;
                              Core.Ops.Range.f_end = (sz 4 *! i <: usize) +! sz 4 <: usize
                            } ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (sz 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (sz 4))
              <:
              u32)
          <:
          t_Array u32 (sz 8))
  in
  out

let to_le_u32s_16_ (bytes: t_Slice u8) : t_Array u32 (sz 16) =
  let out:t_Array u32 (sz 16) = Rust_primitives.Hax.repeat 0ul (sz 16) in
  let out:t_Array u32 (sz 16) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 16
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          Rust_primitives.Hax.update_at out
            i
            (Core.Num.impl__u32__from_le_bytes (Core.Result.impl__unwrap (Core.Convert.f_try_into (bytes.[
                            {
                              Core.Ops.Range.f_start = sz 4 *! i <: usize;
                              Core.Ops.Range.f_end = (sz 4 *! i <: usize) +! sz 4 <: usize
                            } ]
                          <:
                          t_Slice u8)
                      <:
                      Core.Result.t_Result (t_Array u8 (sz 4)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (sz 4))
              <:
              u32)
          <:
          t_Array u32 (sz 16))
  in
  out

let u32s_to_le_bytes (state: t_Array u32 (sz 16)) : t_Array u8 (sz 64) =
  let out:t_Array u8 (sz 64) = Rust_primitives.Hax.repeat 0uy (sz 64) in
  let out:t_Array u8 (sz 64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end
              =
              Core.Slice.impl__len (Rust_primitives.unsize state <: t_Slice u32) <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let tmp:t_Array u8 (sz 4) = Core.Num.impl__u32__to_le_bytes (state.[ i ] <: u32) in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 4
                  })
              <:
              Core.Ops.Range.t_Range usize)
            out
            (fun out j ->
                Rust_primitives.Hax.update_at out
                  ((i *! sz 4 <: usize) +! j <: usize)
                  (tmp.[ j ] <: u8)
                <:
                t_Array u8 (sz 64)))
  in
  out

let xor_state (state other: t_Array u32 (sz 16)) : t_Array u32 (sz 16) =
  let state:t_Array u32 (sz 16) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 16
            })
        <:
        Core.Ops.Range.t_Range usize)
      state
      (fun state i ->
          Rust_primitives.Hax.update_at state
            i
            ((state.[ i ] <: u32) ^. (other.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (sz 16))
  in
  state

let add_state (state other: t_Array u32 (sz 16)) : t_Array u32 (sz 16) =
  let state:t_Array u32 (sz 16) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 16
            })
        <:
        Core.Ops.Range.t_Range usize)
      state
      (fun state i ->
          Rust_primitives.Hax.update_at state
            i
            (Core.Num.impl__u32__wrapping_add (state.[ i ] <: u32) (other.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (sz 16))
  in
  state

let update_array (array: t_Array u8 (sz 64)) (v_val: t_Slice u8) : t_Array u8 (sz 64) =
  let _:Prims.unit =
    if ~.(sz 64 >=. (Core.Slice.impl__len v_val <: usize) <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: 64 >= val.len()"
          <:
          Rust_primitives.Hax.t_Never)
  in
  let array:t_Array u8 (sz 64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = Core.Slice.impl__len v_val <: usize
            })
        <:
        Core.Ops.Range.t_Range usize)
      array
      (fun array i ->
          Rust_primitives.Hax.update_at array i (v_val.[ i ] <: u8) <: t_Array u8 (sz 64))
  in
  array