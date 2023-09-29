module Libcrux.Kem.Kyber768.Ind_cpa
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_CiphertextCpa = array u8 1088sz

type t_KeyPair = {
  f_sk:array u8 1152sz;
  f_pk:array u8 1184sz
}

let new_under_impl (sk: array u8 1152sz) (pk: array u8 1184sz) : t_KeyPair =
  { Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_sk = sk; Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_pk = pk }

let serialize_secret_key_under_impl (self: t_KeyPair) (implicit_rejection_value: slice u8)
    : array u8 2400sz =
  Libcrux.Kem.Kyber768.Conversions.array_under_impl (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push
        (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push
                (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push (Libcrux.Kem.Kyber768.Conversions.new_under_impl
                        (Rust_primitives.Hax.repeat 0uy 2400sz <: array u8 2400sz)
                      <:
                      Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 2400sz)
                    (Rust_primitives.unsize self.Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_sk
                      <:
                      slice u8)
                  <:
                  Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 2400sz)
                (Rust_primitives.unsize self.Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_pk <: slice u8)
              <:
              Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 2400sz)
            (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                        self.Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_pk
                      <:
                      slice u8)
                  <:
                  array u8 32sz)
              <:
              slice u8)
          <:
          Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 2400sz)
        implicit_rejection_value
      <:
      Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 2400sz)

let pk_under_impl (self: t_KeyPair) : array u8 1184sz =
  self.Libcrux.Kem.Kyber768.Ind_cpa.KeyPair.f_pk

let sample_matrix_A (seed: array u8 34sz) (transpose: bool)
    : (array (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz &
      Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
  let v_A_transpose:array (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    3sz =
    Rust_primitives.Hax.repeat (Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
          3sz
        <:
        array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
      3sz
  in
  let sampling_A_error:Core.Option.t_Option
  Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError =
    Core.Option.Option_None
  in
  let v_A_transpose, sampling_A_error, seed:(array
      (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz &
    Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError &
    array u8 34sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      (v_A_transpose, sampling_A_error, seed)
      (fun (v_A_transpose, sampling_A_error, seed) i ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
                    Core.Ops.Range.Range.f_start = 0sz;
                    Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
                  })
              <:
              _)
            (v_A_transpose, sampling_A_error, seed)
            (fun (v_A_transpose, sampling_A_error, seed) j ->
                let seed:array u8 34sz = Rust_primitives.Hax.update_at seed 32sz (cast i) in
                let seed:array u8 34sz = Rust_primitives.Hax.update_at seed 33sz (cast j) in
                let (xof_bytes: array u8 840sz):array u8 840sz =
                  Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_XOF (Rust_primitives.unsize seed
                      <:
                      slice u8)
                in
                let sampled, error:(Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement &
                  Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
                  Libcrux.Kem.Kyber768.Sampling.sample_from_uniform_distribution xof_bytes
                in
                let sampling_A_error:Core.Option.t_Option
                Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError =
                  if Core.Option.is_some_under_impl error
                  then
                    let sampling_A_error:Core.Option.t_Option
                    Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError =
                      error
                    in
                    sampling_A_error
                  else sampling_A_error
                in
                if transpose
                then
                  let v_A_transpose:array
                    (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz =
                    Rust_primitives.Hax.update_at v_A_transpose
                      j
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ j ]
                            <:
                            array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
                          i
                          sampled
                        <:
                        array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
                  in
                  v_A_transpose, sampling_A_error, seed
                else
                  let v_A_transpose:array
                    (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz =
                    Rust_primitives.Hax.update_at v_A_transpose
                      i
                      (Rust_primitives.Hax.update_at (v_A_transpose.[ i ]
                            <:
                            array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
                          j
                          sampled
                        <:
                        array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
                  in
                  v_A_transpose, sampling_A_error, seed)
          <:
          (array (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz &
            Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError &
            array u8 34sz))
  in
  v_A_transpose, sampling_A_error

let cbd (prf_input: array u8 33sz)
    : (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz & u8) =
  let domain_separator:u8 = 0uy in
  let re_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let domain_separator, prf_input, re_as_ntt:(Prims.unit & array u8 33sz &
    array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      (domain_separator, prf_input, re_as_ntt)
      (fun (domain_separator, prf_input, re_as_ntt) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let r:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber768.Sampling.sample_from_binomial_distribution_2_ prf_output
          in
          let re_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at re_as_ntt
              i
              (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_representation r
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, re_as_ntt)
  in
  re_as_ntt, domain_separator

let encode_12_ (input: array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    : array u8 1152sz =
  let out:array u8 1152sz = Rust_primitives.Hax.repeat 0uy 1152sz in
  let out:array u8 1152sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Iter.Traits.Collect.IntoIterator.into_iter input <: _)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
                3sz))
        <:
        _)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.Range.f_start
                =
                i *. Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                Core.Ops.Range.Range.f_end
                =
                (i +. 1sz <: usize) *. Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.Range.f_start
                        =
                        i *. Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT <: usize;
                        Core.Ops.Range.Range.f_end
                        =
                        (i +. 1sz <: usize) *.
                        Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT
                        <:
                        usize
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Serialize.serialize_little_endian_12_ re

                      <:
                      array u8 384sz)
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 1152sz)
  in
  out

let generate_keypair (key_generation_seed: slice u8)
    : (t_KeyPair & Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
  let (prf_input: array u8 33sz):array u8 33sz = Rust_primitives.Hax.repeat 0uy 33sz in
  let secret_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let error_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let (domain_separator: u8):u8 = 0uy in
  let hashed:array u8 64sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_G key_generation_seed
  in
  let seed_for_A, seed_for_secret_and_error:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz &
    Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber768.Conversions.into_padded_array seed_for_A <: array u8 34sz)
      true
  in
  let prf_input:array u8 33sz =
    Rust_primitives.Hax.update_at prf_input
      ({
          Core.Ops.Range.Range.f_start = 0sz;
          Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl seed_for_secret_and_error <: usize
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut prf_input
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Core.Slice.len_under_impl seed_for_secret_and_error <: usize
                })
            <:
            slice u8)
          seed_for_secret_and_error
        <:
        slice u8)
  in
  let domain_separator, prf_input, secret_as_ntt:(Prims.unit & array u8 33sz &
    array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      (domain_separator, prf_input, secret_as_ntt)
      (fun (domain_separator, prf_input, secret_as_ntt) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let secret:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber768.Sampling.sample_from_binomial_distribution_2_ prf_output
          in
          let secret_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at secret_as_ntt
              i
              (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_representation secret
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, prf_input, secret_as_ntt)
  in
  let domain_separator, error_as_ntt, prf_input:(Prims.unit &
    array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      (domain_separator, error_as_ntt, prf_input)
      (fun (domain_separator, error_as_ntt, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber768.Sampling.sample_from_binomial_distribution_2_ prf_output
          in
          let error_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at error_as_ntt
              i
              (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_representation error
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_as_ntt, prf_input)
  in
  let t__as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Libcrux.Kem.Kyber768.Ntt.multiply_matrix_by_column v_A_transpose secret_as_ntt
  in
  let t__as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      t__as_ntt
      (fun t__as_ntt i ->
          Rust_primitives.Hax.update_at t__as_ntt
            i
            ((t__as_ntt.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement) +.
              (error_as_ntt.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
              <:
              _)
          <:
          array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
  in
  let public_key_serialized:array u8 1184sz =
    Libcrux.Kem.Kyber768.Conversions.array_under_impl (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push
          (Libcrux.Kem.Kyber768.Conversions.UpdatingArray.push (Libcrux.Kem.Kyber768.Conversions.new_under_impl
                  (Rust_primitives.Hax.repeat 0uy 1184sz <: array u8 1184sz)
                <:
                Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 1184sz)
              (Rust_primitives.unsize (encode_12_ t__as_ntt <: array u8 1152sz) <: slice u8)
            <:
            Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 1184sz)
          seed_for_A
        <:
        Libcrux.Kem.Kyber768.Conversions.t_UpdatableArray 1184sz)
  in
  let secret_key_serialized:array u8 1152sz = encode_12_ secret_as_ntt in
  new_under_impl secret_key_serialized public_key_serialized, sampling_A_error

let compress_then_encode_u
      (input: array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    : array u8 960sz =
  let out:array u8 960sz = Rust_primitives.Hax.repeat 0uy 960sz in
  let out:array u8 960sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Iter.Traits.Collect.IntoIterator.into_iter input <: _)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Array.Iter.t_IntoIter Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
                3sz))
        <:
        _)
      out
      (fun out (i, re) ->
          Rust_primitives.Hax.update_at out
            ({
                Core.Ops.Range.Range.f_start
                =
                i *. Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_ENCODED_ELEMENT_OF_U <: usize;
                Core.Ops.Range.Range.f_end
                =
                (i +. 1sz <: usize) *.
                Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_ENCODED_ELEMENT_OF_U
                <:
                usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
                    ({
                        Core.Ops.Range.Range.f_start
                        =
                        i *. Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_ENCODED_ELEMENT_OF_U
                        <:
                        usize;
                        Core.Ops.Range.Range.f_end
                        =
                        (i +. 1sz <: usize) *.
                        Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_ENCODED_ELEMENT_OF_U
                        <:
                        usize
                      })
                  <:
                  slice u8)
                (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Serialize.serialize_little_endian_10_ (
                          Libcrux.Kem.Kyber768.Compress.compress re
                            Libcrux.Kem.Kyber768.Parameters.v_VECTOR_U_COMPRESSION_FACTOR
                          <:
                          Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                      <:
                      array u8 320sz)
                  <:
                  slice u8)
              <:
              slice u8)
          <:
          array u8 960sz)
  in
  out

let encrypt (public_key: slice u8) (message: array u8 32sz) (randomness: slice u8)
    : (array u8 1088sz &
      Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
  let t__as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let t__as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (public_key.[ {
                        Core.Ops.Range.RangeTo.f_end
                        =
                        Libcrux.Kem.Kyber768.Parameters.v_T_AS_NTT_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      t__as_ntt
      (fun t__as_ntt (i, t__as_ntt_bytes) ->
          Rust_primitives.Hax.update_at t__as_ntt
            i
            (Libcrux.Kem.Kyber768.Serialize.deserialize_little_endian_12_ t__as_ntt_bytes
              <:
              Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          <:
          array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
  in
  let seed:slice u8 =
    public_key.[ {
        Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber768.Parameters.v_T_AS_NTT_ENCODED_SIZE
      } ]
  in
  let v_A_transpose, sampling_A_error:(array
      (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz &
    Core.Option.t_Option Libcrux.Kem.Kyber768.t_BadRejectionSamplingRandomnessError) =
    sample_matrix_A (Libcrux.Kem.Kyber768.Conversions.into_padded_array seed <: array u8 34sz) false
  in
  let (prf_input: array u8 33sz):array u8 33sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array randomness
  in
  let r_as_ntt, domain_separator:(array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
      3sz &
    u8) =
    cbd prf_input
  in
  let error_1_:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let domain_separator, error_1_, prf_input:(Prims.unit &
    array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz &
    array u8 33sz) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      (domain_separator, error_1_, prf_input)
      (fun (domain_separator, error_1_, prf_input) i ->
          let prf_input:array u8 33sz =
            Rust_primitives.Hax.update_at prf_input 32sz domain_separator
          in
          let domain_separator:Prims.unit = domain_separator +. 1uy in
          let (prf_output: array u8 128sz):array u8 128sz =
            Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
                <:
                slice u8)
          in
          let error_1_:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at error_1_
              i
              (Libcrux.Kem.Kyber768.Sampling.sample_from_binomial_distribution_2_ prf_output
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          in
          domain_separator, error_1_, prf_input)
  in
  let prf_input:array u8 33sz = Rust_primitives.Hax.update_at prf_input 32sz domain_separator in
  let (prf_output: array u8 128sz):array u8 128sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_PRF (Rust_primitives.unsize prf_input
        <:
        slice u8)
  in
  let error_2_:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Sampling.sample_from_binomial_distribution_2_ prf_output
  in
  let u:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Libcrux.Kem.Kyber768.Ntt.multiply_matrix_by_column_montgomery v_A_transpose r_as_ntt
  in
  let u:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.Range.f_start = 0sz;
              Core.Ops.Range.Range.f_end = Libcrux.Kem.Kyber768.Parameters.v_RANK
            })
        <:
        _)
      u
      (fun u i ->
          Rust_primitives.Hax.update_at u
            i
            ((Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.invert_ntt_montgomery (u.[ i
                    ]
                    <:
                    Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement) +.
              (error_1_.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
              <:
              _)
          <:
          array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
  in
  let message_as_ring_element:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Serialize.deserialize_little_endian_1_ (Rust_primitives.unsize message
        <:
        slice u8)
  in
  let v =
    ((Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.invert_ntt_montgomery (Libcrux.Kem.Kyber768.Ntt.multiply_row_by_column_montgomery
              t__as_ntt
              r_as_ntt
            <:
            Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
        <:
        Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement) +.
      error_2_
      <:
      _) +.
    (Libcrux.Kem.Kyber768.Compress.decompress message_as_ring_element 1sz
      <:
      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
  in
  let c1:array u8 960sz = compress_then_encode_u u in
  let c2:array u8 128sz =
    Libcrux.Kem.Kyber768.Serialize.serialize_little_endian_4_ (Libcrux.Kem.Kyber768.Compress.compress
          v
          Libcrux.Kem.Kyber768.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
        <:
        Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
  in
  let (ciphertext: array u8 1088sz):array u8 1088sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize c1 <: slice u8)
  in
  let ciphertext:array u8 1088sz =
    Rust_primitives.Hax.update_at ciphertext
      ({
          Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber768.Parameters.v_VECTOR_U_ENCODED_SIZE
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut ciphertext
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_VECTOR_U_ENCODED_SIZE
                })
            <:
            slice u8)
          (Core.Array.as_slice_under_impl_23 c2 <: slice u8)
        <:
        slice u8)
  in
  ciphertext, sampling_A_error

let decrypt (secret_key: slice u8) (ciphertext: array u8 1088sz) : array u8 32sz =
  let u_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let u_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl (ciphertext.[ {
                        Core.Ops.Range.RangeTo.f_end
                        =
                        Libcrux.Kem.Kyber768.Parameters.v_VECTOR_U_ENCODED_SIZE
                      } ]
                    <:
                    slice u8)
                  ((Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT *. 10sz <: usize) /.
                    8sz
                    <:
                    usize)
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      u_as_ntt
      (fun u_as_ntt (i, u_bytes) ->
          let u:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Libcrux.Kem.Kyber768.Serialize.deserialize_little_endian_10_ u_bytes
          in
          let u_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at u_as_ntt
              i
              (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_representation (Libcrux.Kem.Kyber768.Compress.decompress
                      u
                      10sz
                    <:
                    Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          in
          u_as_ntt)
  in
  let v:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Compress.decompress (Libcrux.Kem.Kyber768.Serialize.deserialize_little_endian_4_
          (ciphertext.[ {
                Core.Ops.Range.RangeFrom.f_start
                =
                Libcrux.Kem.Kyber768.Parameters.v_VECTOR_U_ENCODED_SIZE
              } ]
            <:
            slice u8)
        <:
        Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      Libcrux.Kem.Kyber768.Parameters.v_VECTOR_V_COMPRESSION_FACTOR
  in
  let secret_as_ntt:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.chunks_exact_under_impl secret_key
                  Libcrux.Kem.Kyber768.Parameters.v_BYTES_PER_RING_ELEMENT
                <:
                Core.Slice.Iter.t_ChunksExact u8)
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate (Core.Slice.Iter.t_ChunksExact u8))
        <:
        _)
      secret_as_ntt
      (fun secret_as_ntt (i, secret_bytes) ->
          Rust_primitives.Hax.update_at secret_as_ntt
            i
            (Libcrux.Kem.Kyber768.Serialize.deserialize_little_endian_12_ secret_bytes
              <:
              Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          <:
          array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
  in
  let message =
    v -.
    (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.invert_ntt_montgomery (Libcrux.Kem.Kyber768.Ntt.multiply_row_by_column_montgomery
            secret_as_ntt
            u_as_ntt
          <:
          Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
      <:
      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
  in
  Libcrux.Kem.Kyber768.Serialize.serialize_little_endian_1_ (Libcrux.Kem.Kyber768.Compress.compress message
        1sz
      <:
      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)