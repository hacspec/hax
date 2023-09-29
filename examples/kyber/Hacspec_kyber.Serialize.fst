module Hacspec_kyber.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let bits_to_bytes (bits: Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  admit ();
  let _:Prims.unit =
    if ~.(((Alloc.Vec.len_under_impl_1 bits <: usize) %. 8sz <: usize) =. 0sz <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits.len() % 8 == 0"
          <:
          Rust_primitives.Hax.t_Never)
  in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Slice.chunks_under_impl
              (Core.Ops.Deref.Deref.deref bits <: slice u8)
              8sz
            <:
            Core.Slice.Iter.t_Chunks u8)
        <:
        _)
      bytes
      (fun bytes (bit_chunk: slice u8) ->
          let byte_value:u8 = 0uy in
          let byte_value =
            Core.Iter.Traits.Iterator.Iterator.fold
              #(Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
              #(iterator_enumerate (slice u8))
                  ((Core.Iter.Traits.Iterator.Iterator.enumerate
                          bit_chunk
                    <: Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8)
                    )
                    )
              byte_value
              (fun (byte_value: u8) (i, bit) ->
                  byte_value +. (bit *. (Core.Num.pow_under_impl_6 2uy (cast i) <: u8) <: _)
                  )
          in
          let bytes:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
            Alloc.Vec.push_under_impl_1 bytes byte_value
          in
          bytes)
  in
  bytes

(*
let byte_encode
      (bits_per_coefficient: usize)
      (re:
          Hacspec_lib.Ring.t_PolynomialRingElement (Hacspec_lib.Field.t_PrimeFieldElement 3329us)
            256sz)
    : Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
  let _:Prims.unit =
    if ~.(bits_per_coefficient <=. Hacspec_kyber.Parameters.v_BITS_PER_COEFFICIENT <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: bits_per_coefficient <= BITS_PER_COEFFICIENT"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Hacspec_lib.Ring.coefficients_under_impl_2
              re
            <:
            array (Hacspec_lib.Field.t_PrimeFieldElement 3329us) 256sz)
        <:
        _)
      re_bits
      (fun re_bits coefficient ->
          let coefficient_value:u16 = coefficient.Hacspec_lib.Field.PrimeFieldElement.f_value in
          let coefficient_value, re_bits:(u16 & Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global) =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  ({
                      Core.Ops.Range.Range.f_start = 0sz;
                      Core.Ops.Range.Range.f_end = bits_per_coefficient
                    })
                <:
                _)
              (coefficient_value, re_bits)
              (fun (coefficient_value, re_bits) _ ->
                  let bit:u16 = coefficient_value %. 2us in
                  let re_bits:Alloc.Vec.t_Vec u8 Alloc.Alloc.t_Global =
                    Alloc.Vec.push_under_impl_1 re_bits (cast bit)
                  in
                  let coefficient_value:u16 = (coefficient_value -. bit <: u16) /. 2us in
                  coefficient_value, re_bits)
          in
          re_bits)
  in
  bits_to_bytes re_bits
*)
