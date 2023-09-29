module Libcrux.Kem.Kyber768.Ntt.Kyber_polynomial_ring_element_mod
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_ZETAS_MONTGOMERY_DOMAIN: array i32 128sz =
  let list =
    [
      1044l; 758l; 359l; 1517l; 1493l; 1422l; 287l; 202l; 171l; 622l; 1577l; 182l; 962l; 1202l;
      1474l; 1468l; 573l; 1325l; 264l; 383l; 829l; 1458l; 1602l; 130l; 681l; 1017l; 732l; 608l;
      1542l; 411l; 205l; 1571l; 1223l; 652l; 552l; 1015l; 1293l; 1491l; 282l; 1544l; 516l; 8l; 320l;
      666l; 1618l; 1162l; 126l; 1469l; 853l; 90l; 271l; 830l; 107l; 1421l; 247l; 951l; 398l; 961l;
      1508l; 725l; 448l; 1065l; 677l; 1275l; 1103l; 430l; 555l; 843l; 1251l; 871l; 1550l; 105l; 422l;
      587l; 177l; 235l; 291l; 460l; 1574l; 1653l; 246l; 778l; 1159l; 147l; 777l; 1483l; 602l; 1119l;
      1590l; 644l; 872l; 349l; 418l; 329l; 156l; 75l; 817l; 1097l; 603l; 610l; 1322l; 1285l; 1465l;
      384l; 1215l; 136l; 1218l; 1335l; 874l; 220l; 1187l; 1659l; 1185l; 1530l; 1278l; 794l; 1510l;
      854l; 870l; 478l; 108l; 308l; 996l; 991l; 958l; 1460l; 1522l; 1628l
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 128);
  Rust_primitives.Hax.array_of_list list

let v_NTT_LAYERS: array usize 7sz =
  let list = [2sz; 4sz; 8sz; 16sz; 32sz; 64sz; 128sz] in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 7);
  Rust_primitives.Hax.array_of_list list

let ntt_representation (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let zeta_i:usize = 0sz in
  let re, zeta_i:(Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.rev
              (Core.Slice.iter_under_impl (Rust_primitives.unsize v_NTT_LAYERS <: slice usize)
                <:
                Core.Slice.Iter.t_Iter usize)
            <:
            Core.Iter.Adapters.Rev.t_Rev (Core.Slice.Iter.t_Iter usize))
        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) layer ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({
                        Core.Ops.Range.Range.f_start = 0sz;
                        Core.Ops.Range.Range.f_end
                        =
                        Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -. layer <: _
                      })
                    (2sz *. layer <: _)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              _)
            (re, zeta_i)
            (fun (re, zeta_i) offset ->
                let zeta_i:Prims.unit = zeta_i +. 1sz in
                let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                        ({
                            Core.Ops.Range.Range.f_start = offset;
                            Core.Ops.Range.Range.f_end = offset +. layer <: _
                          })
                      <:
                      _)
                    re
                    (fun re j ->
                        let t:i32 =
                          Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce ((re.[ j +. layer <: _ ]
                                <:
                                i32) *.
                              (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                              <:
                              i32)
                        in
                        let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                          Rust_primitives.Hax.update_at re
                            (j +. layer <: _)
                            ((re.[ j ] <: i32) -. t <: i32)
                        in
                        let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                          Rust_primitives.Hax.update_at re j ((re.[ j ] <: i32) +. t <: i32)
                        in
                        re)
                in
                re, zeta_i)
          <:
          (Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement & Prims.unit))
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 re
          .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
        Libcrux.Kem.Kyber768.Arithmetic.barrett_reduce
    }
  in
  re

let invert_ntt_montgomery (re: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let zeta_i:usize = Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT /. 2sz in
  let re, zeta_i:(Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement & Prims.unit) =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter v_NTT_LAYERS

        <:
        _)
      (re, zeta_i)
      (fun (re, zeta_i) layer ->
          Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
                    ({
                        Core.Ops.Range.Range.f_start = 0sz;
                        Core.Ops.Range.Range.f_end
                        =
                        Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT -. layer
                        <:
                        usize
                      })
                    (2sz *. layer <: usize)
                  <:
                  Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
              <:
              _)
            (re, zeta_i)
            (fun (re, zeta_i) offset ->
                let zeta_i:Prims.unit = zeta_i -. 1sz in
                let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                  Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter
                        ({
                            Core.Ops.Range.Range.f_start = offset;
                            Core.Ops.Range.Range.f_end = offset +. layer <: usize
                          })
                      <:
                      _)
                    re
                    (fun re j ->
                        let a_minus_b:i32 =
                          (re.[ j +. layer <: usize ] <: i32) -. (re.[ j ] <: i32)
                        in
                        let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                          Rust_primitives.Hax.update_at re
                            j
                            ((re.[ j ] <: i32) +. (re.[ j +. layer <: usize ] <: i32) <: i32)
                        in
                        let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
                          Rust_primitives.Hax.update_at re
                            (j +. layer <: usize)
                            (Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce (a_minus_b *.
                                  (v_ZETAS_MONTGOMERY_DOMAIN.[ zeta_i ] <: i32)
                                  <:
                                  i32)
                              <:
                              i32)
                        in
                        re)
                in
                re, zeta_i)
          <:
          (Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement & Prims.unit))
  in
  let re:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    {
      re with
      Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
      =
      Core.Array.map_under_impl_23 (Core.Array.map_under_impl_23 re
              .Libcrux.Kem.Kyber768.Arithmetic.KyberPolynomialRingElement.f_coefficients
            (fun coefficient ->
                Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce (coefficient *. 1441l <: i32)
                <:
                i32)
          <:
          array i32 256sz)
        Libcrux.Kem.Kyber768.Arithmetic.barrett_reduce
    }
  in
  re

let ntt_multiply_binomials (a0, a1: (i32 & i32)) (b0, b1: (i32 & i32)) (zeta: i32) : (i32 & i32) =
  (Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce (a0 *. b0 <: i32) <: i32) +.
  (Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce ((Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce
            (a1 *. b1 <: i32)
          <:
          i32) *.
        zeta
        <:
        i32)
    <:
    i32),
  (Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce (a0 *. b1 <: i32) <: i32) +.
  (Libcrux.Kem.Kyber768.Arithmetic.montgomery_reduce (a1 *. b0 <: i32) <: i32)

let ntt_multiply (left right: Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement)
    : Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
  let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Libcrux.Kem.Kyber768.Arithmetic.v_ZERO_under_impl
  in
  let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
    Core.Iter.Traits.Iterator.Iterator.fold (Core.Iter.Traits.Collect.IntoIterator.into_iter (Core.Iter.Traits.Iterator.Iterator.step_by
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_COEFFICIENTS_IN_RING_ELEMENT
                })
              4sz
            <:
            Core.Iter.Adapters.Step_by.t_StepBy (Core.Ops.Range.t_Range usize))
        <:
        _)
      out
      (fun out i ->
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.[ i ] <: i32), (left.[ i +. 1sz <: usize ] <: i32))
              ((right.[ i ] <: i32), (right.[ i +. 1sz <: usize ] <: i32))
              (v_ZETAS_MONTGOMERY_DOMAIN.[ 64sz +. (i /. 4sz <: usize) <: usize ] <: i32)
          in
          let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out i product._1
          in
          let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 1sz <: usize) product._2
          in
          let product:(i32 & i32) =
            ntt_multiply_binomials ((left.[ i +. 2sz <: usize ] <: i32),
                (left.[ i +. 3sz <: usize ] <: i32))
              ((right.[ i +. 2sz <: usize ] <: i32), (right.[ i +. 3sz <: usize ] <: i32))
              (Core.Ops.Arith.Neg.neg (v_ZETAS_MONTGOMERY_DOMAIN.[ 64sz +. (i /. 4sz <: usize)
                      <:
                      usize ]
                    <:
                    i32)
                <:
                i32)
          in
          let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 2sz <: usize) product._1
          in
          let out:Libcrux.Kem.Kyber768.Arithmetic.t_KyberPolynomialRingElement =
            Rust_primitives.Hax.update_at out (i +. 3sz <: usize) product._2
          in
          out)
  in
  out