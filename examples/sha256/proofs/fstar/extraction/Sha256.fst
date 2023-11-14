module Sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

unfold
let t_Block = t_Array u8 (sz 64)

unfold
let t_Hash = t_Array u32 (sz 8)

unfold
let t_OpTableType = t_Array u8 (sz 12)

unfold
let t_RoundConstantsTable = t_Array u32 (sz 64)

unfold
let t_Sha256Digest = t_Array u8 (sz 32)

let v_BLOCK_SIZE: usize = sz 64

let v_HASH_INIT: t_Array u32 (sz 8) =
  let list =
    [
      1779033703ul;
      3144134277ul;
      1013904242ul;
      2773480762ul;
      1359893119ul;
      2600822924ul;
      528734635ul;
      1541459225ul
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
  Rust_primitives.Hax.array_of_list list

let v_HASH_SIZE: usize = sz 256 /! sz 8

let v_K_SIZE: usize = sz 64

let v_K_TABLE: t_Array u32 (sz 64) =
  let list =
    [
      1116352408ul; 1899447441ul; 3049323471ul; 3921009573ul; 961987163ul; 1508970993ul;
      2453635748ul; 2870763221ul; 3624381080ul; 310598401ul; 607225278ul; 1426881987ul; 1925078388ul;
      2162078206ul; 2614888103ul; 3248222580ul; 3835390401ul; 4022224774ul; 264347078ul; 604807628ul;
      770255983ul; 1249150122ul; 1555081692ul; 1996064986ul; 2554220882ul; 2821834349ul;
      2952996808ul; 3210313671ul; 3336571891ul; 3584528711ul; 113926993ul; 338241895ul; 666307205ul;
      773529912ul; 1294757372ul; 1396182291ul; 1695183700ul; 1986661051ul; 2177026350ul;
      2456956037ul; 2730485921ul; 2820302411ul; 3259730800ul; 3345764771ul; 3516065817ul;
      3600352804ul; 4094571909ul; 275423344ul; 430227734ul; 506948616ul; 659060556ul; 883997877ul;
      958139571ul; 1322822218ul; 1537002063ul; 1747873779ul; 1955562222ul; 2024104815ul;
      2227730452ul; 2361852424ul; 2428436474ul; 2756734187ul; 3204031479ul; 3329325298ul
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 64);
  Rust_primitives.Hax.array_of_list list

let v_LEN_SIZE: usize = sz 8

let v_OP_TABLE: t_Array u8 (sz 12) =
  let list = [2uy; 13uy; 22uy; 6uy; 11uy; 25uy; 7uy; 18uy; 3uy; 17uy; 19uy; 10uy] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list list

let ch (x y z: u32) : u32 = (x &. y <: u32) ^. ((~.x <: u32) &. z <: u32)

let maj (x y z: u32) : u32 = (x &. y <: u32) ^. ((x &. z <: u32) ^. (y &. z <: u32) <: u32)

let sigma (x: u32) (i op: usize) : Prims.Pure u32 (requires i <. sz 4) (fun _ -> Prims.l_True) =
  let (tmp: u32):u32 =
    Core.Num.impl__u32__rotate_right x
      (Core.Convert.f_into (v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 2 <: usize ] <: u8) <: u32)
  in
  let tmp:u32 =
    if op =. sz 0 then x >>! (v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 2 <: usize ] <: u8) else tmp
  in
  let rot_val_1_:u32 = Core.Convert.f_into (v_OP_TABLE.[ sz 3 *! i <: usize ] <: u8) in
  let rot_val_2_:u32 =
    Core.Convert.f_into (v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 1 <: usize ] <: u8)
  in
  ((Core.Num.impl__u32__rotate_right x rot_val_1_ <: u32) ^.
    (Core.Num.impl__u32__rotate_right x rot_val_2_ <: u32)
    <:
    u32) ^.
  tmp

let shuffle (ws: t_Array u32 (sz 64)) (hashi: t_Array u32 (sz 8)) : t_Array u32 (sz 8) =
  let h:t_Array u32 (sz 8) = hashi in
  let h:t_Array u32 (sz 8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K_SIZE
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      h
      (fun h i ->
          let h:t_Array u32 (sz 8) = h in
          let i:usize = i in
          let a0:u32 = h.[ sz 0 ] in
          let b0:u32 = h.[ sz 1 ] in
          let c0:u32 = h.[ sz 2 ] in
          let d0:u32 = h.[ sz 3 ] in
          let e0:u32 = h.[ sz 4 ] in
          let f0:u32 = h.[ sz 5 ] in
          let g0:u32 = h.[ sz 6 ] in
          let (h0: u32):u32 = h.[ sz 7 ] in
          let t1:u32 =
            Core.Num.impl__u32__wrapping_add (Core.Num.impl__u32__wrapping_add (Core.Num.impl__u32__wrapping_add
                      (Core.Num.impl__u32__wrapping_add h0 (sigma e0 (sz 1) (sz 1) <: u32) <: u32)
                      (ch e0 f0 g0 <: u32)
                    <:
                    u32)
                  (v_K_TABLE.[ i ] <: u32)
                <:
                u32)
              (ws.[ i ] <: u32)
          in
          let t2:u32 =
            Core.Num.impl__u32__wrapping_add (sigma a0 (sz 0) (sz 1) <: u32) (maj a0 b0 c0 <: u32)
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.update_at h (sz 0) (Core.Num.impl__u32__wrapping_add t1 t2 <: u32)
          in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 1) a0 in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 2) b0 in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 3) c0 in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.update_at h (sz 4) (Core.Num.impl__u32__wrapping_add d0 t1 <: u32)
          in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 5) e0 in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 6) f0 in
          let h:t_Array u32 (sz 8) = Rust_primitives.Hax.update_at h (sz 7) g0 in
          h)
  in
  h

let to_be_u32s (block: t_Array u8 (sz 64)) : Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Alloc.Vec.impl__with_capacity (v_BLOCK_SIZE /! sz 4 <: usize)
  in
  let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks_exact
              (Rust_primitives.unsize block <: t_Slice u8)
              (sz 4)
            <:
            Core.Slice.Iter.t_ChunksExact u8)
        <:
        Core.Slice.Iter.t_ChunksExact u8)
      out
      (fun out block_chunk ->
          let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = out in
          let block_chunk:t_Slice u8 = block_chunk in
          let block_chunk_array:u32 =
            Core.Num.impl__u32__from_be_bytes (Core.Result.impl__unwrap (Core.Convert.f_try_into block_chunk

                    <:
                    Core.Result.t_Result (t_Array u8 (sz 4)) Core.Array.t_TryFromSliceError)
                <:
                t_Array u8 (sz 4))
          in
          let out:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global =
            Alloc.Vec.impl_1__push out block_chunk_array
          in
          out)
  in
  out

let schedule (block: t_Array u8 (sz 64)) : t_Array u32 (sz 64) =
  let b:Alloc.Vec.t_Vec u32 Alloc.Alloc.t_Global = to_be_u32s block in
  let s:t_Array u32 (sz 64) = Rust_primitives.Hax.repeat 0ul (sz 64) in
  let s:t_Array u32 (sz 64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_K_SIZE
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      s
      (fun s i ->
          let s:t_Array u32 (sz 64) = s in
          let i:usize = i in
          if i <. sz 16 <: bool
          then
            let s:t_Array u32 (sz 64) = Rust_primitives.Hax.update_at s i (b.[ i ] <: u32) in
            s
          else
            let t16:u32 = s.[ i -! sz 16 <: usize ] in
            let t15:u32 = s.[ i -! sz 15 <: usize ] in
            let t7:u32 = s.[ i -! sz 7 <: usize ] in
            let t2:u32 = s.[ i -! sz 2 <: usize ] in
            let s1:u32 = sigma t2 (sz 3) (sz 0) in
            let s0:u32 = sigma t15 (sz 2) (sz 0) in
            let s:t_Array u32 (sz 64) =
              Rust_primitives.Hax.update_at s
                i
                (Core.Num.impl__u32__wrapping_add (Core.Num.impl__u32__wrapping_add (Core.Num.impl__u32__wrapping_add
                            s1
                            t7
                          <:
                          u32)
                        s0
                      <:
                      u32)
                    t16
                  <:
                  u32)
            in
            s)
  in
  s

let compress (block: t_Array u8 (sz 64)) (h_in: t_Array u32 (sz 8)) : t_Array u32 (sz 8) =
  let s:t_Array u32 (sz 64) = schedule block in
  let h:t_Array u32 (sz 8) = shuffle s h_in in
  let h:t_Array u32 (sz 8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = sz 8
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      h
      (fun h i ->
          let h:t_Array u32 (sz 8) = h in
          let i:usize = i in
          Rust_primitives.Hax.update_at h
            i
            (Core.Num.impl__u32__wrapping_add (h.[ i ] <: u32) (h_in.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (sz 8))
  in
  h

let u32s_to_be_bytes (state: t_Array u32 (sz 8)) : t_Array u8 (sz 32) =
  let (out: t_Array u8 (sz 32)):t_Array u8 (sz 32) = Rust_primitives.Hax.repeat 0uy (sz 32) in
  let out:t_Array u8 (sz 32) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 0;
              Core.Ops.Range.f_end = v_LEN_SIZE
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      out
      (fun out i ->
          let out:t_Array u8 (sz 32) = out in
          let i:usize = i in
          let tmp:u32 = state.[ i ] in
          let tmp:t_Array u8 (sz 4) = Core.Num.impl__u32__to_be_bytes tmp in
          Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                    Core.Ops.Range.f_start = sz 0;
                    Core.Ops.Range.f_end = sz 4
                  }
                  <:
                  Core.Ops.Range.t_Range usize)
              <:
              Core.Ops.Range.t_Range usize)
            out
            (fun out j ->
                let out:t_Array u8 (sz 32) = out in
                let j:usize = j in
                Rust_primitives.Hax.update_at out
                  ((i *! sz 4 <: usize) +! j <: usize)
                  (tmp.[ j ] <: u8)
                <:
                t_Array u8 (sz 32)))
  in
  out

let hash (msg: t_Slice u8) : t_Array u8 (sz 32) =
  let h:t_Array u32 (sz 8) = v_HASH_INIT in
  let (last_block: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Rust_primitives.Hax.repeat 0uy (sz 64)
  in
  let last_block_len:usize = sz 0 in
  let h, last_block, last_block_len:(t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter (Core.Slice.impl__chunks msg
              v_BLOCK_SIZE
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize))
      (fun temp_0_ block ->
          let h, last_block, last_block_len:(t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize) =
            temp_0_
          in
          let block:t_Slice u8 = block in
          if (Core.Slice.impl__len block <: usize) <. v_BLOCK_SIZE <: bool
          then
            let last_block:t_Array u8 (sz 64) =
              Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Core.Slice.impl__len block <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Core.Ops.Range.t_Range usize)
                last_block
                (fun last_block i ->
                    let last_block:t_Array u8 (sz 64) = last_block in
                    let i:usize = i in
                    Rust_primitives.Hax.update_at last_block i (block.[ i ] <: u8)
                    <:
                    t_Array u8 (sz 64))
            in
            let last_block_len:usize = Core.Slice.impl__len block in
            h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize)
          else
            let h:t_Array u32 (sz 8) =
              compress (Core.Result.impl__unwrap (Core.Convert.f_try_into block
                      <:
                      Core.Result.t_Result (t_Array u8 (sz 64)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (sz 64))
                h
            in
            h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize))
  in
  let last_block:t_Array u8 (sz 64) =
    Rust_primitives.Hax.update_at last_block last_block_len 128uy
  in
  let len_bist:u64 = cast ((Core.Slice.impl__len msg <: usize) *! sz 8 <: usize) <: u64 in
  let len_bist_bytes:t_Array u8 (sz 8) = Core.Num.impl__u64__to_be_bytes len_bist in
  let h, last_block:(t_Array u32 (sz 8) & t_Array u8 (sz 64)) =
    if last_block_len <. (v_BLOCK_SIZE -! v_LEN_SIZE <: usize)
    then
      let last_block:t_Array u8 (sz 64) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = v_LEN_SIZE
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          last_block
          (fun last_block i ->
              let last_block:t_Array u8 (sz 64) = last_block in
              let i:usize = i in
              Rust_primitives.Hax.update_at last_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 (sz 64))
      in
      let h:t_Array u32 (sz 8) = compress last_block h in
      h, last_block <: (t_Array u32 (sz 8) & t_Array u8 (sz 64))
    else
      let (pad_block: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
        Rust_primitives.Hax.repeat 0uy (sz 64)
      in
      let pad_block:t_Array u8 (sz 64) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
                  Core.Ops.Range.f_start = sz 0;
                  Core.Ops.Range.f_end = v_LEN_SIZE
                }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          pad_block
          (fun pad_block i ->
              let pad_block:t_Array u8 (sz 64) = pad_block in
              let i:usize = i in
              Rust_primitives.Hax.update_at pad_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (len_bist_bytes.[ i ] <: u8)
              <:
              t_Array u8 (sz 64))
      in
      let h:t_Array u32 (sz 8) = compress last_block h in
      let h:t_Array u32 (sz 8) = compress pad_block h in
      h, last_block <: (t_Array u32 (sz 8) & t_Array u8 (sz 64))
  in
  u32s_to_be_bytes h

let sha256 (msg: t_Slice u8) : t_Array u8 (sz 32) = hash msg
