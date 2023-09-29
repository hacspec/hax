module Libcrux.Kem.Kyber768.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let serialize_little_endian_1_ (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 32sz =
  let serialized:array u8 32sz = Rust_primitives.Hax.repeat 0uy 32sz in
  let serialized:array u8 32sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber768.Arithmetic.f_coefficients
                    <:
                    slice i32)
                  8sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized ((i, chunk): (usize * slice i32)) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
                    (Core.Slice.iter_under_impl chunk <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              _)
            serialized
            (fun serialized ((j, coefficient): (usize * i32)) ->
                Rust_primitives.Hax.update_at serialized
                  i
                  ((serialized.[ i ] <: u8) |. (cast coefficient >>. j <: u8)(* FIXME bug in engine <: Prims.unit*))
                <:
                array u8 32sz)
          <:
          array u8 32sz)
  in
  serialized
