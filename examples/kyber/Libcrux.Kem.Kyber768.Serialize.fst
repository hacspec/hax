module Libcrux.Kem.Kyber768.Serialize
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let serialize_little_endian_1_ (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 32sz =
  let serialized:array u8 32sz = Rust_primitives.Hax.repeat 0uy 32sz in
  let serialized:array u8 32sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
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
      (fun serialized (i, chunk) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
                    (Core.Slice.iter_under_impl chunk <: Core.Slice.Iter.t_Iter i32)
                  <:
                  Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter i32))
              <:
              _)
            serialized
            (fun serialized (j, coefficient) ->
                Rust_primitives.Hax.update_at serialized
                  i
                  ((serialized.[ i ] <: u8) |. (cast coefficient >>. j <: u8) <: Prims.unit)
                <:
                array u8 32sz)
          <:
          array u8 32sz)
  in
  serialized

let deserialize_little_endian_1_ (serialized: slice u8)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.len_under_impl serialized,
          Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT /. 8sz
        with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                  left_val
                  right_val
                  Core.Option.Option_None
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _)
      re
      (fun re (i, byte) ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = 8sz
                  })
              <:
              _)
            re
            (fun re j ->
                {
                  re with
                  Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Rust_primitives.Hax.update_at re
                      .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    ((8sz *. i <: usize) +. j <: usize)
                    (cast ((byte <<. j <: _) &. 1uy <: u8))
                  <:
                  Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
                })
          <:
          Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
  in
  re

let serialize_little_endian_4_ (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 128sz =
  let serialized:array u8 128sz = Rust_primitives.Hax.repeat 0uy 128sz in
  let serialized:array u8 128sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  2sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:u8 = cast chunk.[ 0sz ] in
          let coefficient2:u8 = cast chunk.[ 1sz ] in
          let serialized:array u8 128sz =
            Rust_primitives.Hax.update_at serialized
              i
              ((coefficient2 >>. 4l <: u8) |. coefficient1 <: u8)
          in
          serialized)
  in
  serialized

let deserialize_little_endian_4_ (serialized: slice u8)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT *. 4sz <: usize) /. 8sz
        with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                  left_val
                  right_val
                  Core.Option.Option_None
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl serialized <: Core.Slice.Iter.t_Iter u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Iter u8))
        <:
        _)
      re
      (fun re (i, byte) ->
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (2sz *. i <: usize)
                (cast (byte &. 15uy <: _))
            }
          in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((2sz *. i <: usize) +. 1sz <: usize)
                (cast ((byte <<. 4l <: _) &. 15uy <: u8))
            }
          in
          re)
  in
  re

let serialize_little_endian_10_ (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 320sz =
  let serialized:array u8 320sz = Rust_primitives.Hax.repeat 0uy 320sz in
  let serialized:array u8 320sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  4sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunk) ->
          let coefficient1:i32 = chunk.[ 0sz ] in
          let coefficient2:i32 = chunk.[ 1sz ] in
          let coefficient3:i32 = chunk.[ 2sz ] in
          let coefficient4:i32 = chunk.[ 3sz ] in
          let serialized:array u8 320sz =
            Rust_primitives.Hax.update_at serialized
              (5sz *. i <: usize)
              (cast (coefficient1 &. 255l <: i32))
          in
          let serialized:array u8 320sz =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 1sz <: usize)
              ((cast (coefficient2 &. 63l <: i32) >>. 2l <: u8) |.
                cast ((coefficient1 <<. 8l <: i32) &. 3l <: i32)
                <:
                u8)
          in
          let serialized:array u8 320sz =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 2sz <: usize)
              ((cast (coefficient3 &. 15l <: i32) >>. 4l <: u8) |.
                cast ((coefficient2 <<. 6l <: i32) &. 15l <: i32)
                <:
                u8)
          in
          let serialized:array u8 320sz =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 3sz <: usize)
              ((cast (coefficient4 &. 3l <: i32) >>. 6l <: u8) |.
                cast ((coefficient3 <<. 4l <: i32) &. 63l <: i32)
                <:
                u8)
          in
          let serialized:array u8 320sz =
            Rust_primitives.Hax.update_at serialized
              ((5sz *. i <: usize) +. 4sz <: usize)
              (cast ((coefficient4 <<. 2l <: i32) &. 255l <: i32))
          in
          serialized)
  in
  serialized

let deserialize_little_endian_10_ (serialized: slice u8)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.len_under_impl serialized,
          (Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT *. 10sz <: usize) /. 8sz
        with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                  left_val
                  right_val
                  Core.Option.Option_None
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_under_impl serialized 5sz <: Core.Slice.Iter.t_Chunks u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_Chunks u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let byte4:i32 = cast bytes.[ 3sz ] in
          let byte5:i32 = cast bytes.[ 4sz ] in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (4sz *. i <: usize)
                (((byte2 &. 3l <: i32) >>. 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 1sz <: usize)
                (((byte3 &. 15l <: i32) >>. 6l <: i32) |. (byte2 <<. 2l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 2sz <: usize)
                (((byte4 &. 63l <: i32) >>. 4l <: i32) |. (byte3 <<. 4l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((4sz *. i <: usize) +. 3sz <: usize)
                ((byte5 >>. 2l <: i32) |. (byte4 <<. 6l <: i32) <: i32)
            }
          in
          re)
  in
  re

let serialize_little_endian_12_ (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : array u8 384sz =
  let serialized:array u8 384sz = Rust_primitives.Hax.repeat 0uy 384sz in
  let serialized:array u8 384sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (Rust_primitives.unsize re
                        .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    <:
                    slice i32)
                  2sz
                <:
                Core.Slice.Iter.t_ChunksExact i32)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact i32))
        <:
        _)
      serialized
      (fun serialized (i, chunks) ->
          let coefficient1:u16 =
            Libcrux.Kem.Kyber768.Conversions.to_unsigned_representative (chunks.[ 0sz ] <: i32)
          in
          let coefficient2:u16 =
            Libcrux.Kem.Kyber768.Conversions.to_unsigned_representative (chunks.[ 1sz ] <: i32)
          in
          let serialized:array u8 384sz =
            Rust_primitives.Hax.update_at serialized
              (3sz *. i <: usize)
              (cast (coefficient1 &. 255us <: u16))
          in
          let serialized:array u8 384sz =
            Rust_primitives.Hax.update_at serialized
              ((3sz *. i <: usize) +. 1sz <: usize)
              (cast ((coefficient1 <<. 8l <: u16) |. ((coefficient2 &. 15us <: u16) >>. 4l <: u16)
                    <:
                    u16))
          in
          let serialized:array u8 384sz =
            Rust_primitives.Hax.update_at serialized
              ((3sz *. i <: usize) +. 2sz <: usize)
              (cast ((coefficient2 <<. 4l <: u16) &. 255us <: u16))
          in
          serialized)
  in
  serialized

let deserialize_little_endian_12_ (serialized: slice u8)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        match
          Core.Slice.len_under_impl serialized,
          Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT
        with
        | left_val, right_val ->
          if ~.(left_val =. right_val <: bool)
          then
            let kind:Core.Panicking.t_AssertKind = Core.Panicking.AssertKind_Eq in
            Rust_primitives.Hax.never_to_any (Core.Panicking.assert_failed kind
                  left_val
                  right_val
                  Core.Option.Option_None
                <:
                Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl serialized 3sz <: Core.Slice.Iter.t_ChunksExact u8
              )
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      re
      (fun re (i, bytes) ->
          let byte1:i32 = cast bytes.[ 0sz ] in
          let byte2:i32 = cast bytes.[ 1sz ] in
          let byte3:i32 = cast bytes.[ 2sz ] in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                (2sz *. i <: usize)
                (((byte2 &. 15l <: i32) >>. 8l <: i32) |. (byte1 &. 255l <: i32) <: i32)
            }
          in
          let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            {
              re with
              Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
              =
              Rust_primitives.Hax.update_at re
                  .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                ((2sz *. i <: usize) +. 1sz <: usize)
                ((byte3 >>. 4l <: i32) |. ((byte2 <<. 4l <: i32) &. 15l <: i32) <: i32)
            }
          in
          re)
  in
  re