module Libcrux.Kem.Kyber768.Ntt
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let multiply_row_by_column_montgomery
      (row_vector column_vector:
          array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let result:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let result =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.zip
              (Core.Slice.iter_under_impl (Rust_primitives.unsize row_vector
                    <:
                    slice Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
              (Core.Slice.iter_under_impl (Rust_primitives.unsize column_vector
                    <:
                    slice Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                <:
                Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
            <:
            Core.Iter.Adapters.Zip.t_Zip
              (Core.Slice.Iter.t_Iter Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
              _)
        <:
        _)
      result
      (fun result (row_element, column_element) ->
          result +.
          (Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_multiply row_element
              column_element
            <:
            Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
          <:
          _)
  in
  let result:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      result with
      Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 result
          .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
        Libcrux.Kem.Kyber768.Arithmetic.barrett_reduce
    }
  in
  result

let multiply_matrix_by_column_montgomery
      (matrix: array (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz)
      (vector: array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    : array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize matrix
                    <:
                    slice (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz))
                <:
                Core.Slice.Iter.t_Iter
                (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)))
        <:
        _)
      result
      (fun result (i, row) ->
          let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  (Core.Iter.Traits.Iterator.Iterator.enumerate (Core.Slice.iter_under_impl (Rust_primitives.unsize
                              row
                            <:
                            slice Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement))
                <:
                _)
              result
              (fun result (j, matrix_element) ->
                  let product:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                    Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_multiply matrix_element
                      (vector.[ j ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz
                  =
                    Rust_primitives.Hax.update_at result
                      i
                      ((result.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
                        ) +.
                        product
                        <:
                        _)
                  in
                  result)
          in
          let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at result
              i
              ({
                  (result.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement) with
                  Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Core.Array.map_under_impl_23 (result.[ i ]
                      <:
                      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                      .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    Libcrux.Kem.Kyber768.Arithmetic.barrett_reduce
                  <:
                  array i32 256sz
                })
          in
          result)
  in
  result

let multiply_matrix_by_column
      (matrix: array (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz) 3sz)
      (vector: array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)
    : array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Rust_primitives.Hax.repeat Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl 3sz
  in
  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.enumerate
              (Core.Slice.iter_under_impl (Rust_primitives.unsize matrix
                    <:
                    slice (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz))
                <:
                Core.Slice.Iter.t_Iter
                (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz))
            <:
            Core.Iter.Adapters.Enumerate.t_Enumerate
            (Core.Slice.Iter.t_Iter
              (array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz)))
        <:
        _)
      result
      (fun result (i, row) ->
          let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                  (Core.Iter.Traits.Iterator.Iterator.enumerate (Core.Slice.iter_under_impl (Rust_primitives.unsize
                              row
                            <:
                            slice Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                        <:
                        Core.Slice.Iter.t_Iter
                        Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                    <:
                    Core.Iter.Adapters.Enumerate.t_Enumerate
                    (Core.Slice.Iter.t_Iter
                      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement))
                <:
                _)
              result
              (fun result (j, matrix_element) ->
                  let product:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                    Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod.ntt_multiply matrix_element
                      (vector.[ j ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                  in
                  let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz
                  =
                    Rust_primitives.Hax.update_at result
                      i
                      ((result.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement
                        ) +.
                        product
                        <:
                        _)
                  in
                  result)
          in
          let result:array Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement 3sz =
            Rust_primitives.Hax.update_at result
              i
              ({
                  (result.[ i ] <: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement) with
                  Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                  =
                  Core.Array.map_under_impl_23 (result.[ i ]
                      <:
                      Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
                      .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
                    (fun coefficient ->
                        let coefficient_montgomery:i32 =
                          Libcrux.Kem.Kyber768.Arithmetic.to_montgomery_domain coefficient
                        in
                        Libcrux.Kem.Kyber768.Arithmetic.barrett_reduce coefficient_montgomery)
                  <:
                  array i32 256sz
                })
          in
          result)
  in
  result