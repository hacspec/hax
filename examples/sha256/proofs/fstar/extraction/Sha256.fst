module Sha256
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let _ =
  (* This module has implicit dependencies, here we make them explicit. *)
  (* The implicit dependencies arise from typeclasses instances. *)
  let open Hax_secret_integers.Public_integers in
  ()

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
  Rust_primitives.Hax.array_of_list 8 list

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
  Rust_primitives.Hax.array_of_list 64 list

let v_LEN_SIZE: usize = sz 8

let v_OP_TABLE: t_Array u32 (sz 12) =
  let list = [2ul; 13ul; 22ul; 6ul; 11ul; 25ul; 7ul; 18ul; 3ul; 17ul; 19ul; 10ul] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 12);
  Rust_primitives.Hax.array_of_list 12 list

let ch (x y z: u32) : u32 = (x &. y <: u32) ^. ((~.x <: u32) &. z <: u32)

let maj (x y z: u32) : u32 = (x &. y <: u32) ^. ((x &. z <: u32) ^. (y &. z <: u32) <: u32)

let sigma (x: u32) (i op: usize) : Prims.Pure u32 (requires i <. sz 4) (fun _ -> Prims.l_True) =
  let (tmp: u32):u32 =
    Core.Num.impl__u32__rotate_right x
      (Core.Convert.f_into #u32
          #u32
          #FStar.Tactics.Typeclasses.solve
          (v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 2 <: usize ] <: u32)
        <:
        u32)
  in
  let tmp:u32 =
    if op =. sz 0 then x >>! (v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 2 <: usize ] <: u32) else tmp
  in
  let rot_val_1_:u32 = v_OP_TABLE.[ sz 3 *! i <: usize ] in
  let rot_val_2_:u32 = v_OP_TABLE.[ (sz 3 *! i <: usize) +! sz 1 <: usize ] in
  ((Core.Num.impl__u32__rotate_right x rot_val_1_ <: u32) ^.
    (Core.Num.impl__u32__rotate_right x rot_val_2_ <: u32)
    <:
    u32) ^.
  tmp

let schedule (block: t_Array u8 (sz 64)) : t_Array u32 (sz 64) =
  let b:t_Array u32 (sz 16) =
    Core.Result.impl__unwrap #(t_Array u32 (sz 16))
      #Prims.unit
      (Hax_secret_integers.Traits.f_try_from_be_bytes #(t_Array u32 (sz 16))
          #u8
          #FStar.Tactics.Typeclasses.solve
          (Rust_primitives.unsize block <: t_Slice u8)
        <:
        Core.Result.t_Result (t_Array u32 (sz 16)) Prims.unit)
  in
  let s:t_Array u32 (sz 64) =
    Rust_primitives.Hax.repeat (Core.Convert.f_into #u32 #u32 #FStar.Tactics.Typeclasses.solve 0ul
        <:
        u32)
      (sz 64)
  in
  let s:t_Array u32 (sz 64) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K_SIZE }
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
            let s:t_Array u32 (sz 64) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s i (b.[ i ] <: u32)
            in
            s
          else
            let t16:u32 = s.[ i -! sz 16 <: usize ] in
            let t15:u32 = s.[ i -! sz 15 <: usize ] in
            let t7:u32 = s.[ i -! sz 7 <: usize ] in
            let t2:u32 = s.[ i -! sz 2 <: usize ] in
            let s1:u32 = sigma t2 (sz 3) (sz 0) in
            let s0:u32 = sigma t15 (sz 2) (sz 0) in
            let s:t_Array u32 (sz 64) =
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize s
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

let shuffle (ws: t_Array u32 (sz 64)) (hashi: t_Array u32 (sz 8)) : t_Array u32 (sz 8) =
  let h:t_Array u32 (sz 8) = hashi in
  let h:t_Array u32 (sz 8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_K_SIZE }
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
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h
              (sz 0)
              (Core.Num.impl__u32__wrapping_add t1 t2 <: u32)
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 1) a0
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 2) b0
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 3) c0
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h
              (sz 4)
              (Core.Num.impl__u32__wrapping_add d0 t1 <: u32)
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 5) e0
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 6) f0
          in
          let h:t_Array u32 (sz 8) =
            Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h (sz 7) g0
          in
          h)
  in
  h

let compress (block: t_Array u8 (sz 64)) (h_in: t_Array u32 (sz 8)) : t_Array u32 (sz 8) =
  let s:t_Array u32 (sz 64) = schedule block in
  let h:t_Array u32 (sz 8) = shuffle s h_in in
  let h:t_Array u32 (sz 8) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
            usize)
          #FStar.Tactics.Typeclasses.solve
          ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = sz 8 }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      h
      (fun h i ->
          let h:t_Array u32 (sz 8) = h in
          let i:usize = i in
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize h
            i
            (Core.Num.impl__u32__wrapping_add (h.[ i ] <: u32) (h_in.[ i ] <: u32) <: u32)
          <:
          t_Array u32 (sz 8))
  in
  h

let hash (msg: t_Slice u8) : t_Array u8 (sz 32) =
  let h:t_Array u32 (sz 8) =
    Hax_secret_integers.Traits.f_classify_each #(t_Array u32 (sz 8))
      #FStar.Tactics.Typeclasses.solve
      v_HASH_INIT
  in
  let (last_block: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
    Rust_primitives.Hax.repeat (Core.Convert.f_into #u8 #u8 #FStar.Tactics.Typeclasses.solve 0uy
        <:
        u8)
      (sz 64)
  in
  let last_block_len:usize = sz 0 in
  let h, last_block, last_block_len:(t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Slice.Iter.t_Chunks
            u8)
          #FStar.Tactics.Typeclasses.solve
          (Core.Slice.impl__chunks #u8 msg v_BLOCK_SIZE <: Core.Slice.Iter.t_Chunks u8)
        <:
        Core.Slice.Iter.t_Chunks u8)
      (h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize))
      (fun temp_0_ block ->
          let h, last_block, last_block_len:(t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize) =
            temp_0_
          in
          let block:t_Slice u8 = block in
          if (Core.Slice.impl__len #u8 block <: usize) <. v_BLOCK_SIZE <: bool
          then
            let last_block:t_Array u8 (sz 64) =
              Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                      usize)
                    #FStar.Tactics.Typeclasses.solve
                    ({
                        Core.Ops.Range.f_start = sz 0;
                        Core.Ops.Range.f_end = Core.Slice.impl__len #u8 block <: usize
                      }
                      <:
                      Core.Ops.Range.t_Range usize)
                  <:
                  Core.Ops.Range.t_Range usize)
                last_block
                (fun last_block i ->
                    let last_block:t_Array u8 (sz 64) = last_block in
                    let i:usize = i in
                    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
                      i
                      (block.[ i ] <: u8)
                    <:
                    t_Array u8 (sz 64))
            in
            let last_block_len:usize = Core.Slice.impl__len #u8 block in
            h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize)
          else
            let h:t_Array u32 (sz 8) =
              compress (Core.Result.impl__unwrap #(t_Array u8 (sz 64))
                    #Core.Array.t_TryFromSliceError
                    (Core.Convert.f_try_into #(t_Slice u8)
                        #(t_Array u8 (sz 64))
                        #FStar.Tactics.Typeclasses.solve
                        block
                      <:
                      Core.Result.t_Result (t_Array u8 (sz 64)) Core.Array.t_TryFromSliceError)
                  <:
                  t_Array u8 (sz 64))
                h
            in
            h, last_block, last_block_len <: (t_Array u32 (sz 8) & t_Array u8 (sz 64) & usize))
  in
  let last_block:t_Array u8 (sz 64) =
    Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
      last_block_len
      (Core.Convert.f_into #u8 #u8 #FStar.Tactics.Typeclasses.solve 128uy <: u8)
  in
  let len_bist:u64 = cast ((Core.Slice.impl__len #u8 msg <: usize) *! sz 8 <: usize) <: u64 in
  let len_bist_bytes:t_Array u8 (sz 8) = Core.Num.impl__u64__to_be_bytes len_bist in
  let h, last_block:(t_Array u32 (sz 8) & t_Array u8 (sz 64)) =
    if last_block_len <. (v_BLOCK_SIZE -! v_LEN_SIZE <: usize)
    then
      let last_block:t_Array u8 (sz 64) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                usize)
              #FStar.Tactics.Typeclasses.solve
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_LEN_SIZE }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          last_block
          (fun last_block i ->
              let last_block:t_Array u8 (sz 64) = last_block in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize last_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (Core.Convert.f_into #u8
                    #u8
                    #FStar.Tactics.Typeclasses.solve
                    (len_bist_bytes.[ i ] <: u8)
                  <:
                  u8)
              <:
              t_Array u8 (sz 64))
      in
      let h:t_Array u32 (sz 8) = compress last_block h in
      h, last_block <: (t_Array u32 (sz 8) & t_Array u8 (sz 64))
    else
      let (pad_block: t_Array u8 (sz 64)):t_Array u8 (sz 64) =
        Rust_primitives.Hax.repeat (Core.Convert.f_into #u8 #u8 #FStar.Tactics.Typeclasses.solve 0uy
            <:
            u8)
          (sz 64)
      in
      let pad_block:t_Array u8 (sz 64) =
        Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter #(Core.Ops.Range.t_Range
                usize)
              #FStar.Tactics.Typeclasses.solve
              ({ Core.Ops.Range.f_start = sz 0; Core.Ops.Range.f_end = v_LEN_SIZE }
                <:
                Core.Ops.Range.t_Range usize)
            <:
            Core.Ops.Range.t_Range usize)
          pad_block
          (fun pad_block i ->
              let pad_block:t_Array u8 (sz 64) = pad_block in
              let i:usize = i in
              Rust_primitives.Hax.Monomorphized_update_at.update_at_usize pad_block
                ((v_BLOCK_SIZE -! v_LEN_SIZE <: usize) +! i <: usize)
                (Core.Convert.f_into #u8
                    #u8
                    #FStar.Tactics.Typeclasses.solve
                    (len_bist_bytes.[ i ] <: u8)
                  <:
                  u8)
              <:
              t_Array u8 (sz 64))
      in
      let h:t_Array u32 (sz 8) = compress last_block h in
      let h:t_Array u32 (sz 8) = compress pad_block h in
      h, last_block <: (t_Array u32 (sz 8) & t_Array u8 (sz 64))
  in
  Core.Result.impl__unwrap #(t_Array u8 (sz 32))
    #Prims.unit
    (Hax_secret_integers.Traits.f_try_to_be_bytes #(t_Array u32 (sz 8))
        #u8
        #(sz 32)
        #FStar.Tactics.Typeclasses.solve
        h
      <:
      Core.Result.t_Result (t_Array u8 (sz 32)) Prims.unit)

let sha256 (msg: t_Slice u8) : t_Array u8 (sz 32) = hash msg
