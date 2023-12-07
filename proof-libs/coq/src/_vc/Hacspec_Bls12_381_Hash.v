(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Bls12_381.

Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition fp_hash_canvas_t := nseq (int8) (64).
Definition fp_hash_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.

Definition arr_fp_t := nseq (uint64) (usize 6).

Definition b_in_bytes_v : uint_size :=
  usize 32.

Definition s_in_bytes_v : uint_size :=
  usize 64.

Definition l_v : uint_size :=
  usize 64.

Definition p_1_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 936899308823769933) : int64;
        secret (@repr WORDSIZE64 2706051889235351147) : int64;
        secret (@repr WORDSIZE64 12843041017062132063) : int64;
        secret (@repr WORDSIZE64 12941209323636816658) : int64;
        secret (@repr WORDSIZE64 1105070755758604287) : int64;
        secret (@repr WORDSIZE64 15924587544893707605) : int64
      ] in  l).

Definition p_1_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629611) : int64
      ] in  l).

Definition p_3_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 468449654411884966) : int64;
        secret (@repr WORDSIZE64 10576397981472451381) : int64;
        secret (@repr WORDSIZE64 15644892545385841839) : int64;
        secret (@repr WORDSIZE64 15693976698673184137) : int64;
        secret (@repr WORDSIZE64 552535377879302143) : int64;
        secret (@repr WORDSIZE64 17185665809301629610) : int64
      ] in  l).

Definition expand_message_xmd
  (msg_1389 : byte_seq)
  (dst_1390 : byte_seq)
  (len_in_bytes_1391 : uint_size)
  : byte_seq :=
  let ell_1392 : uint_size :=
    (((len_in_bytes_1391) + (b_in_bytes_v)) - (usize 1)) / (b_in_bytes_v) in 
  let dst_prime_1393 : seq uint8 :=
    seq_push (dst_1390) (uint8_from_usize (seq_len (dst_1390))) in 
  let z_pad_1394 : seq uint8 :=
    seq_new_ (default) (s_in_bytes_v) in 
  let l_i_b_str_1395 : seq uint8 :=
    seq_new_ (default) (usize 2) in 
  let l_i_b_str_1395 :=
    seq_upd l_i_b_str_1395 (usize 0) (uint8_from_usize ((len_in_bytes_1391) / (
          usize 256))) in 
  let l_i_b_str_1395 :=
    seq_upd l_i_b_str_1395 (usize 1) (uint8_from_usize (len_in_bytes_1391)) in 
  let msg_prime_1396 : seq uint8 :=
    seq_concat (seq_concat (seq_concat (seq_concat (z_pad_1394) (msg_1389)) (
          l_i_b_str_1395)) (seq_new_ (default) (usize 1))) (dst_prime_1393) in 
  let b_0_1397 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (msg_prime_1396))) in 
  let b_i_1398 : seq uint8 :=
    seq_from_seq (array_to_seq (hash (seq_concat (seq_push (b_0_1397) (secret (
              @repr WORDSIZE8 1) : int8)) (dst_prime_1393)))) in 
  let uniform_bytes_1399 : seq uint8 :=
    seq_from_seq (b_i_1398) in 
  let '(b_i_1398, uniform_bytes_1399) :=
    foldi (usize 2) ((ell_1392) + (usize 1)) (fun i_1400 '(
        b_i_1398,
        uniform_bytes_1399
      ) =>
      let t_1401 : seq uint8 :=
        seq_from_seq (b_0_1397) in 
      let b_i_1398 :=
        seq_from_seq (array_to_seq (hash (seq_concat (seq_push ((
                  t_1401) seq_xor (b_i_1398)) (uint8_from_usize (i_1400))) (
              dst_prime_1393)))) in 
      let uniform_bytes_1399 :=
        seq_concat (uniform_bytes_1399) (b_i_1398) in 
      (b_i_1398, uniform_bytes_1399))
    (b_i_1398, uniform_bytes_1399) in 
  seq_truncate (uniform_bytes_1399) (len_in_bytes_1391).

Definition fp_hash_to_field
  (msg_1402 : byte_seq)
  (dst_1403 : byte_seq)
  (count_1404 : uint_size)
  : seq fp_t :=
  let len_in_bytes_1405 : uint_size :=
    (count_1404) * (l_v) in 
  let uniform_bytes_1406 : seq uint8 :=
    expand_message_xmd (msg_1402) (dst_1403) (len_in_bytes_1405) in 
  let output_1407 : seq fp_t :=
    seq_new_ (default) (count_1404) in 
  let output_1407 :=
    foldi (usize 0) (count_1404) (fun i_1408 output_1407 =>
      let elm_offset_1409 : uint_size :=
        (l_v) * (i_1408) in 
      let tv_1410 : seq uint8 :=
        seq_slice (uniform_bytes_1406) (elm_offset_1409) (l_v) in 
      let u_i_1411 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1410) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1407 :=
        seq_upd output_1407 (i_1408) (u_i_1411) in 
      (output_1407))
    output_1407 in 
  output_1407.

Definition fp_sgn0 (x_1412 : fp_t) : bool :=
  ((x_1412) rem (nat_mod_two )) =.? (nat_mod_one ).

Definition fp_is_square (x_1413 : fp_t) : bool :=
  let c1_1414 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let tv_1415 : fp_t :=
    nat_mod_pow_self (x_1413) (c1_1414) in 
  ((tv_1415) =.? (nat_mod_zero )) || ((tv_1415) =.? (nat_mod_one )).

Definition fp_sqrt (x_1416 : fp_t) : fp_t :=
  let c1_1417 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_4_v)) : fp_t in 
  nat_mod_pow_self (x_1416) (c1_1417).

Definition g1_curve_func (x_1418 : fp_t) : fp_t :=
  (((x_1418) *% (x_1418)) *% (x_1418)) +% (nat_mod_from_literal (_) (
      @repr WORDSIZE128 4) : fp_t).

Definition g1_map_to_curve_svdw (u_1419 : fp_t) : g1_t :=
  let z_1420 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_from_literal (_) (
        @repr WORDSIZE128 3) : fp_t) in 
  let gz_1421 : fp_t :=
    g1_curve_func (z_1420) in 
  let tv1_1422 : fp_t :=
    ((u_1419) *% (u_1419)) *% (gz_1421) in 
  let tv2_1423 : fp_t :=
    (nat_mod_one ) +% (tv1_1422) in 
  let tv1_1424 : fp_t :=
    (nat_mod_one ) -% (tv1_1422) in 
  let tv3_1425 : fp_t :=
    nat_mod_inv ((tv1_1424) *% (tv2_1423)) in 
  let tv4_1426 : fp_t :=
    fp_sqrt (((nat_mod_zero ) -% (gz_1421)) *% (((nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t) *% (z_1420)) *% (z_1420))) in 
  let '(tv4_1426) :=
    if fp_sgn0 (tv4_1426):bool then (let tv4_1426 :=
        (nat_mod_zero ) -% (tv4_1426) in 
      (tv4_1426)) else ((tv4_1426)) in 
  let tv5_1427 : fp_t :=
    (((u_1419) *% (tv1_1424)) *% (tv3_1425)) *% (tv4_1426) in 
  let tv6_1428 : fp_t :=
    (((nat_mod_zero ) -% (nat_mod_from_literal (_) (
            @repr WORDSIZE128 4) : fp_t)) *% (gz_1421)) *% (nat_mod_inv (((
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t) *% (
            z_1420)) *% (z_1420))) in 
  let x1_1429 : fp_t :=
    (((nat_mod_zero ) -% (z_1420)) *% (nat_mod_inv (nat_mod_two ))) -% (
      tv5_1427) in 
  let x2_1430 : fp_t :=
    (((nat_mod_zero ) -% (z_1420)) *% (nat_mod_inv (nat_mod_two ))) +% (
      tv5_1427) in 
  let x3_1431 : fp_t :=
    (z_1420) +% (((tv6_1428) *% (((tv2_1423) *% (tv2_1423)) *% (tv3_1425))) *% (
        ((tv2_1423) *% (tv2_1423)) *% (tv3_1425))) in 
  let x_1432 : fp_t :=
    (if (fp_is_square (g1_curve_func (x1_1429))):bool then (x1_1429) else ((if (
            fp_is_square (g1_curve_func (x2_1430))):bool then (x2_1430) else (
            x3_1431)))) in 
  let y_1433 : fp_t :=
    fp_sqrt (g1_curve_func (x_1432)) in 
  let '(y_1433) :=
    if (fp_sgn0 (u_1419)) !=.? (fp_sgn0 (y_1433)):bool then (let y_1433 :=
        (nat_mod_zero ) -% (y_1433) in 
      (y_1433)) else ((y_1433)) in 
  (x_1432, y_1433, false).

Definition g1_clear_cofactor (x_1434 : g1_t) : g1_t :=
  let h_eff_1435 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642753) : scalar_t in 
  g1mul (h_eff_1435) (x_1434).

Definition g1_hash_to_curve_svdw
  (msg_1436 : byte_seq)
  (dst_1437 : byte_seq)
  : g1_t :=
  let u_1438 : seq fp_t :=
    fp_hash_to_field (msg_1436) (dst_1437) (usize 2) in 
  let q0_1439 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1438) (usize 0)) in 
  let q1_1440 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1438) (usize 1)) in 
  let r_1441 : (fp_t × fp_t × bool) :=
    g1add (q0_1439) (q1_1440) in 
  let p_1442 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_1441) in 
  p_1442.

Definition g1_encode_to_curve_svdw
  (msg_1443 : byte_seq)
  (dst_1444 : byte_seq)
  : g1_t :=
  let u_1445 : seq fp_t :=
    fp_hash_to_field (msg_1443) (dst_1444) (usize 1) in 
  let q_1446 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_svdw (seq_index (u_1445) (usize 0)) in 
  let p_1447 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_1446) in 
  p_1447.

Definition fp2_hash_to_field
  (msg_1448 : byte_seq)
  (dst_1449 : byte_seq)
  (count_1450 : uint_size)
  : seq fp2_t :=
  let len_in_bytes_1451 : uint_size :=
    ((count_1450) * (usize 2)) * (l_v) in 
  let uniform_bytes_1452 : seq uint8 :=
    expand_message_xmd (msg_1448) (dst_1449) (len_in_bytes_1451) in 
  let output_1453 : seq (fp_t × fp_t) :=
    seq_new_ (default) (count_1450) in 
  let output_1453 :=
    foldi (usize 0) (count_1450) (fun i_1454 output_1453 =>
      let elm_offset_1455 : uint_size :=
        ((l_v) * (i_1454)) * (usize 2) in 
      let tv_1456 : seq uint8 :=
        seq_slice (uniform_bytes_1452) (elm_offset_1455) (l_v) in 
      let e_1_1457 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1456) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let elm_offset_1458 : uint_size :=
        (l_v) * ((usize 1) + ((i_1454) * (usize 2))) in 
      let tv_1459 : seq uint8 :=
        seq_slice (uniform_bytes_1452) (elm_offset_1458) (l_v) in 
      let e_2_1460 : fp_t :=
        nat_mod_from_byte_seq_be (seq_slice (nat_mod_to_byte_seq_be (
              nat_mod_from_byte_seq_be (tv_1459) : fp_hash_t)) (usize 16) (
            usize 48)) : fp_t in 
      let output_1453 :=
        seq_upd output_1453 (i_1454) ((e_1_1457, e_2_1460)) in 
      (output_1453))
    output_1453 in 
  output_1453.

Definition fp2_sgn0 (x_1461 : fp2_t) : bool :=
  let '(x0_1462, x1_1463) :=
    x_1461 in 
  let sign_0_1464 : bool :=
    fp_sgn0 (x0_1462) in 
  let zero_0_1465 : bool :=
    (x0_1462) =.? (nat_mod_zero ) in 
  let sign_1_1466 : bool :=
    fp_sgn0 (x1_1463) in 
  (sign_0_1464) || ((zero_0_1465) && (sign_1_1466)).

Definition fp2_is_square (x_1467 : fp2_t) : bool :=
  let c1_1468 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let '(x1_1469, x2_1470) :=
    x_1467 in 
  let tv1_1471 : fp_t :=
    (x1_1469) *% (x1_1469) in 
  let tv2_1472 : fp_t :=
    (x2_1470) *% (x2_1470) in 
  let tv1_1473 : fp_t :=
    (tv1_1471) +% (tv2_1472) in 
  let tv1_1474 : fp_t :=
    nat_mod_pow_self (tv1_1473) (c1_1468) in 
  let neg1_1475 : fp_t :=
    (nat_mod_zero ) -% (nat_mod_one ) in 
  (tv1_1474) !=.? (neg1_1475).

Definition fp2exp (n_1476 : fp2_t) (k_1477 : fp_t) : fp2_t :=
  let c_1478 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let c_1478 :=
    foldi (usize 0) (usize 381) (fun i_1479 c_1478 =>
      let c_1478 :=
        fp2mul (c_1478) (c_1478) in 
      let '(c_1478) :=
        if nat_mod_bit (k_1477) ((usize 380) - (i_1479)):bool then (
          let c_1478 :=
            fp2mul (c_1478) (n_1476) in 
          (c_1478)) else ((c_1478)) in 
      (c_1478))
    c_1478 in 
  c_1478.

Definition fp2_sqrt (a_1480 : fp2_t) : fp2_t :=
  let c1_1481 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_3_4_v)) : fp_t in 
  let c2_1482 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (p_1_2_v)) : fp_t in 
  let a1_1483 : (fp_t × fp_t) :=
    fp2exp (a_1480) (c1_1481) in 
  let alpha_1484 : (fp_t × fp_t) :=
    fp2mul (a1_1483) (fp2mul (a1_1483) (a_1480)) in 
  let x0_1485 : (fp_t × fp_t) :=
    fp2mul (a1_1483) (a_1480) in 
  let neg1_1486 : (fp_t × fp_t) :=
    ((nat_mod_zero ) -% (nat_mod_one ), nat_mod_zero ) in 
  let b_1487 : (fp_t × fp_t) :=
    fp2exp (fp2add (fp2fromfp (nat_mod_one )) (alpha_1484)) (c2_1482) in 
  (if ((alpha_1484) =.? (neg1_1486)):bool then (fp2mul ((
          nat_mod_zero ,
          nat_mod_one 
        )) (x0_1485)) else (fp2mul (b_1487) (x0_1485))).

Definition g2_curve_func (x_1488 : fp2_t) : fp2_t :=
  fp2add (fp2mul (x_1488) (fp2mul (x_1488) (x_1488))) ((
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 4) : fp_t
    )).

Definition g2_map_to_curve_svdw (u_1489 : fp2_t) : g2_t :=
  let z_1490 : (fp_t × fp_t) :=
    fp2neg (fp2fromfp (nat_mod_one )) in 
  let gz_1491 : (fp_t × fp_t) :=
    g2_curve_func (z_1490) in 
  let tv1_1492 : (fp_t × fp_t) :=
    fp2mul (fp2mul (u_1489) (u_1489)) (gz_1491) in 
  let tv2_1493 : (fp_t × fp_t) :=
    fp2add (fp2fromfp (nat_mod_one )) (tv1_1492) in 
  let tv1_1494 : (fp_t × fp_t) :=
    fp2sub (fp2fromfp (nat_mod_one )) (tv1_1492) in 
  let tv3_1495 : (fp_t × fp_t) :=
    fp2inv (fp2mul (tv1_1494) (tv2_1493)) in 
  let tv4_1496 : (fp_t × fp_t) :=
    fp2_sqrt (fp2mul (fp2neg (gz_1491)) (fp2mul (fp2fromfp (
            nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (fp2mul (
            z_1490) (z_1490)))) in 
  let '(tv4_1496) :=
    if fp2_sgn0 (tv4_1496):bool then (let tv4_1496 :=
        fp2neg (tv4_1496) in 
      (tv4_1496)) else ((tv4_1496)) in 
  let tv5_1497 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2mul (u_1489) (tv1_1494)) (tv3_1495)) (tv4_1496) in 
  let tv6_1498 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (fp2fromfp (nat_mod_from_literal (_) (
              @repr WORDSIZE128 4) : fp_t))) (gz_1491)) (fp2inv (fp2mul (
          fp2fromfp (nat_mod_from_literal (_) (@repr WORDSIZE128 3) : fp_t)) (
          fp2mul (z_1490) (z_1490)))) in 
  let x1_1499 : (fp_t × fp_t) :=
    fp2sub (fp2mul (fp2neg (z_1490)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1497) in 
  let x2_1500 : (fp_t × fp_t) :=
    fp2add (fp2mul (fp2neg (z_1490)) (fp2inv (fp2fromfp (nat_mod_two )))) (
      tv5_1497) in 
  let tv7_1501 : (fp_t × fp_t) :=
    fp2mul (fp2mul (tv2_1493) (tv2_1493)) (tv3_1495) in 
  let x3_1502 : (fp_t × fp_t) :=
    fp2add (z_1490) (fp2mul (tv6_1498) (fp2mul (tv7_1501) (tv7_1501))) in 
  let x_1503 : (fp_t × fp_t) :=
    (if (fp2_is_square (g2_curve_func (x1_1499))):bool then (x1_1499) else ((
          if (fp2_is_square (g2_curve_func (x2_1500))):bool then (
            x2_1500) else (x3_1502)))) in 
  let y_1504 : (fp_t × fp_t) :=
    fp2_sqrt (g2_curve_func (x_1503)) in 
  let '(y_1504) :=
    if (fp2_sgn0 (u_1489)) !=.? (fp2_sgn0 (y_1504)):bool then (let y_1504 :=
        fp2neg (y_1504) in 
      (y_1504)) else ((y_1504)) in 
  (x_1503, y_1504, false).

Definition psi (p_1505 : g2_t) : g2_t :=
  let c1_1506 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_from_literal (_) (
              @repr WORDSIZE128 3) : fp_t)))) in 
  let c2_1507 : (fp_t × fp_t) :=
    fp2inv (fp2exp ((nat_mod_one , nat_mod_one )) (((nat_mod_zero ) -% (
            nat_mod_one )) *% (nat_mod_inv (nat_mod_two )))) in 
  let '(x_1508, y_1509, inf_1510) :=
    p_1505 in 
  let qx_1511 : (fp_t × fp_t) :=
    fp2mul (c1_1506) (fp2conjugate (x_1508)) in 
  let qy_1512 : (fp_t × fp_t) :=
    fp2mul (c2_1507) (fp2conjugate (y_1509)) in 
  (qx_1511, qy_1512, inf_1510).

Definition g2_clear_cofactor (p_1513 : g2_t) : g2_t :=
  let c1_1514 : scalar_t :=
    nat_mod_from_literal (_) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let t1_1515 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_1514) (p_1513) in 
  let t1_1516 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t1_1515) in 
  let t2_1517 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (p_1513) in 
  let t3_1518 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2double (p_1513) in 
  let t3_1519 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    psi (psi (t3_1518)) in 
  let t3_1520 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1519) (g2neg (t2_1517)) in 
  let t2_1521 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t1_1516) (t2_1517) in 
  let t2_1522 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2mul (c1_1514) (t2_1521) in 
  let t2_1523 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2neg (t2_1522) in 
  let t3_1524 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1520) (t2_1523) in 
  let t3_1525 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1524) (g2neg (t1_1516)) in 
  let q_1526 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (t3_1525) (g2neg (p_1513)) in 
  q_1526.

Definition g2_hash_to_curve_svdw
  (msg_1527 : byte_seq)
  (dst_1528 : byte_seq)
  : g2_t :=
  let u_1529 : seq fp2_t :=
    fp2_hash_to_field (msg_1527) (dst_1528) (usize 2) in 
  let q0_1530 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1529) (usize 0)) in 
  let q1_1531 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1529) (usize 1)) in 
  let r_1532 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_1530) (q1_1531) in 
  let p_1533 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_1532) in 
  p_1533.

Definition g2_encode_to_curve_svdw
  (msg_1534 : byte_seq)
  (dst_1535 : byte_seq)
  : g2_t :=
  let u_1536 : seq fp2_t :=
    fp2_hash_to_field (msg_1534) (dst_1535) (usize 1) in 
  let q_1537 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_svdw (seq_index (u_1536) (usize 0)) in 
  let p_1538 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_1537) in 
  p_1538.

Definition g1_iso_a_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 5707120929990979) : int64;
        secret (@repr WORDSIZE64 4425131892511951234) : int64;
        secret (@repr WORDSIZE64 12748169179688756904) : int64;
        secret (@repr WORDSIZE64 15629909748249821612) : int64;
        secret (@repr WORDSIZE64 10994253769421683071) : int64;
        secret (@repr WORDSIZE64 6698022561392380957) : int64
      ] in  l).

Definition g1_iso_b_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1360808972976160816) : int64;
        secret (@repr WORDSIZE64 111203405409480251) : int64;
        secret (@repr WORDSIZE64 2312248699302920304) : int64;
        secret (@repr WORDSIZE64 11581500465278574325) : int64;
        secret (@repr WORDSIZE64 6495071758858381989) : int64;
        secret (@repr WORDSIZE64 15117538217124375520) : int64
      ] in  l).

Definition g1_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1270119733718627136) : int64;
        secret (@repr WORDSIZE64 13261148298159854981) : int64;
        secret (@repr WORDSIZE64 7723742117508874335) : int64;
        secret (@repr WORDSIZE64 17465657917644792520) : int64;
        secret (@repr WORDSIZE64 6201670911048166766) : int64;
        secret (@repr WORDSIZE64 12586459670690286007) : int64
      ] in  l).

Definition g1_xnum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1668951808976071471) : int64;
        secret (@repr WORDSIZE64 398773841247578140) : int64;
        secret (@repr WORDSIZE64 8941869963990959127) : int64;
        secret (@repr WORDSIZE64 17682789360670468203) : int64;
        secret (@repr WORDSIZE64 5204176168283587414) : int64;
        secret (@repr WORDSIZE64 16732261237459223483) : int64
      ] in  l).

Definition g1_xnum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 960393023080265964) : int64;
        secret (@repr WORDSIZE64 2094253841180170779) : int64;
        secret (@repr WORDSIZE64 14844748873776858085) : int64;
        secret (@repr WORDSIZE64 7528018573573808732) : int64;
        secret (@repr WORDSIZE64 10776056440809943711) : int64;
        secret (@repr WORDSIZE64 16147550488514976944) : int64
      ] in  l).

Definition g1_xnum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1691355743628586423) : int64;
        secret (@repr WORDSIZE64 5622191986793862162) : int64;
        secret (@repr WORDSIZE64 15561595211679121189) : int64;
        secret (@repr WORDSIZE64 17416319752018800771) : int64;
        secret (@repr WORDSIZE64 5996228842464768403) : int64;
        secret (@repr WORDSIZE64 14245880009877842017) : int64
      ] in  l).

Definition g1_xnum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1051997788391994435) : int64;
        secret (@repr WORDSIZE64 7368650625050054228) : int64;
        secret (@repr WORDSIZE64 11086623519836470079) : int64;
        secret (@repr WORDSIZE64 607681821319080984) : int64;
        secret (@repr WORDSIZE64 10978131499682789316) : int64;
        secret (@repr WORDSIZE64 5842660658088809945) : int64
      ] in  l).

Definition g1_xnum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1598992431623377919) : int64;
        secret (@repr WORDSIZE64 130921168661596853) : int64;
        secret (@repr WORDSIZE64 15797696746983946651) : int64;
        secret (@repr WORDSIZE64 11444679715590672272) : int64;
        secret (@repr WORDSIZE64 11567228658253249817) : int64;
        secret (@repr WORDSIZE64 14777367860349315459) : int64
      ] in  l).

Definition g1_xnum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 967946631563726121) : int64;
        secret (@repr WORDSIZE64 7653628713030275775) : int64;
        secret (@repr WORDSIZE64 12760252618317466849) : int64;
        secret (@repr WORDSIZE64 10378793938173061930) : int64;
        secret (@repr WORDSIZE64 10205808941053849290) : int64;
        secret (@repr WORDSIZE64 15985511645807504772) : int64
      ] in  l).

Definition g1_xnum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1709149555065084898) : int64;
        secret (@repr WORDSIZE64 16750075057192140371) : int64;
        secret (@repr WORDSIZE64 3849985779734105521) : int64;
        secret (@repr WORDSIZE64 11998370262181639475) : int64;
        secret (@repr WORDSIZE64 4159013751748851119) : int64;
        secret (@repr WORDSIZE64 11298218755092433038) : int64
      ] in  l).

Definition g1_xnum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 580186936973955012) : int64;
        secret (@repr WORDSIZE64 8903813505199544589) : int64;
        secret (@repr WORDSIZE64 14140024565662700916) : int64;
        secret (@repr WORDSIZE64 11728946595272970718) : int64;
        secret (@repr WORDSIZE64 5738313744366653077) : int64;
        secret (@repr WORDSIZE64 7886252005760951063) : int64
      ] in  l).

Definition g1_xnum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1628930385436977092) : int64;
        secret (@repr WORDSIZE64 3318087848058654498) : int64;
        secret (@repr WORDSIZE64 15937899882900905113) : int64;
        secret (@repr WORDSIZE64 7449821001803307903) : int64;
        secret (@repr WORDSIZE64 11752436998487615353) : int64;
        secret (@repr WORDSIZE64 9161465579737517214) : int64
      ] in  l).

Definition g1_xnum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1167027828517898210) : int64;
        secret (@repr WORDSIZE64 8275623842221021965) : int64;
        secret (@repr WORDSIZE64 18049808134997311382) : int64;
        secret (@repr WORDSIZE64 15351349873550116966) : int64;
        secret (@repr WORDSIZE64 17769927732099571180) : int64;
        secret (@repr WORDSIZE64 14584871380308065147) : int64
      ] in  l).

Definition g1_xnum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 495550047642324592) : int64;
        secret (@repr WORDSIZE64 13627494601717575229) : int64;
        secret (@repr WORDSIZE64 3591512392926246844) : int64;
        secret (@repr WORDSIZE64 2576269112800734056) : int64;
        secret (@repr WORDSIZE64 14000314106239596831) : int64;
        secret (@repr WORDSIZE64 12234233096825917993) : int64
      ] in  l).

Definition g1_xden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633474091881273774) : int64;
        secret (@repr WORDSIZE64 1779737893574802031) : int64;
        secret (@repr WORDSIZE64 132274872219551930) : int64;
        secret (@repr WORDSIZE64 11283074393783708770) : int64;
        secret (@repr WORDSIZE64 13067430171545714168) : int64;
        secret (@repr WORDSIZE64 11041975239630265116) : int64
      ] in  l).

Definition g1_xden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1321272531362356291) : int64;
        secret (@repr WORDSIZE64 5238936591227237942) : int64;
        secret (@repr WORDSIZE64 8089002360232247308) : int64;
        secret (@repr WORDSIZE64 82967328719421271) : int64;
        secret (@repr WORDSIZE64 1430641118356186857) : int64;
        secret (@repr WORDSIZE64 16557527386785790975) : int64
      ] in  l).

Definition g1_xden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 804282852993868382) : int64;
        secret (@repr WORDSIZE64 9311163821600184607) : int64;
        secret (@repr WORDSIZE64 8037026956533927121) : int64;
        secret (@repr WORDSIZE64 18205324308570099372) : int64;
        secret (@repr WORDSIZE64 15466434890074226396) : int64;
        secret (@repr WORDSIZE64 18213183315621985817) : int64
      ] in  l).

Definition g1_xden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 234844145893171966) : int64;
        secret (@repr WORDSIZE64 14428037799351479124) : int64;
        secret (@repr WORDSIZE64 6559532710647391569) : int64;
        secret (@repr WORDSIZE64 6110444250091843536) : int64;
        secret (@repr WORDSIZE64 5293652763671852484) : int64;
        secret (@repr WORDSIZE64 1373009181854280920) : int64
      ] in  l).

Definition g1_xden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1416629893867312296) : int64;
        secret (@repr WORDSIZE64 751851957792514173) : int64;
        secret (@repr WORDSIZE64 18437674587247370939) : int64;
        secret (@repr WORDSIZE64 10190314345946351322) : int64;
        secret (@repr WORDSIZE64 11228207967368476701) : int64;
        secret (@repr WORDSIZE64 6025034940388909598) : int64
      ] in  l).

Definition g1_xden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1041270466333271993) : int64;
        secret (@repr WORDSIZE64 6140956605115975401) : int64;
        secret (@repr WORDSIZE64 4131830461445745997) : int64;
        secret (@repr WORDSIZE64 739642499118176303) : int64;
        secret (@repr WORDSIZE64 8358912131254619921) : int64;
        secret (@repr WORDSIZE64 13847998906088228005) : int64
      ] in  l).

Definition g1_xden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 536714149743900185) : int64;
        secret (@repr WORDSIZE64 1098328982230230817) : int64;
        secret (@repr WORDSIZE64 6273329123533496713) : int64;
        secret (@repr WORDSIZE64 5633448088282521244) : int64;
        secret (@repr WORDSIZE64 16894043798660571244) : int64;
        secret (@repr WORDSIZE64 17016134625831438906) : int64
      ] in  l).

Definition g1_xden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1488347500898461874) : int64;
        secret (@repr WORDSIZE64 3509418672874520985) : int64;
        secret (@repr WORDSIZE64 7962192351555381416) : int64;
        secret (@repr WORDSIZE64 1843909372225399896) : int64;
        secret (@repr WORDSIZE64 1127511003250156243) : int64;
        secret (@repr WORDSIZE64 1294742680819751518) : int64
      ] in  l).

Definition g1_xden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 725340084226051970) : int64;
        secret (@repr WORDSIZE64 6814521545734988748) : int64;
        secret (@repr WORDSIZE64 16176803544133875307) : int64;
        secret (@repr WORDSIZE64 8363199516777220149) : int64;
        secret (@repr WORDSIZE64 252877309218538352) : int64;
        secret (@repr WORDSIZE64 5149562959837648449) : int64
      ] in  l).

Definition g1_xden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 675470927100193492) : int64;
        secret (@repr WORDSIZE64 5146891164735334016) : int64;
        secret (@repr WORDSIZE64 17762958817130696759) : int64;
        secret (@repr WORDSIZE64 8565656522589412373) : int64;
        secret (@repr WORDSIZE64 10599026333335446784) : int64;
        secret (@repr WORDSIZE64 3270603789344496906) : int64
      ] in  l).

Definition g1_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 652344406751465184) : int64;
        secret (@repr WORDSIZE64 2710356675495255290) : int64;
        secret (@repr WORDSIZE64 1273695771440998738) : int64;
        secret (@repr WORDSIZE64 3121750372618945491) : int64;
        secret (@repr WORDSIZE64 14775319642720936898) : int64;
        secret (@repr WORDSIZE64 13733803417833814835) : int64
      ] in  l).

Definition g1_ynum_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1389807578337138705) : int64;
        secret (@repr WORDSIZE64 15352831428748068483) : int64;
        secret (@repr WORDSIZE64 1307144967559264317) : int64;
        secret (@repr WORDSIZE64 1121505450578652468) : int64;
        secret (@repr WORDSIZE64 15475889019760388287) : int64;
        secret (@repr WORDSIZE64 16183658160488302230) : int64
      ] in  l).

Definition g1_ynum_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 57553299067792998) : int64;
        secret (@repr WORDSIZE64 17628079362768849300) : int64;
        secret (@repr WORDSIZE64 2689461337731570914) : int64;
        secret (@repr WORDSIZE64 14070580367580990887) : int64;
        secret (@repr WORDSIZE64 15162865775551710499) : int64;
        secret (@repr WORDSIZE64 13321614990632673782) : int64
      ] in  l).

Definition g1_ynum_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 141972750621744161) : int64;
        secret (@repr WORDSIZE64 8689824239172478807) : int64;
        secret (@repr WORDSIZE64 15288216298323671324) : int64;
        secret (@repr WORDSIZE64 712874875091754233) : int64;
        secret (@repr WORDSIZE64 16014900032503684588) : int64;
        secret (@repr WORDSIZE64 11976580453200426187) : int64
      ] in  l).

Definition g1_ynum_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 633886036738506515) : int64;
        secret (@repr WORDSIZE64 6678644607214234052) : int64;
        secret (@repr WORDSIZE64 1825425679455244472) : int64;
        secret (@repr WORDSIZE64 8755912272271186652) : int64;
        secret (@repr WORDSIZE64 3379943669301788840) : int64;
        secret (@repr WORDSIZE64 4735212769449148123) : int64
      ] in  l).

Definition g1_ynum_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612358804494830442) : int64;
        secret (@repr WORDSIZE64 2454990789666711200) : int64;
        secret (@repr WORDSIZE64 8405916841409361853) : int64;
        secret (@repr WORDSIZE64 8525415512662168654) : int64;
        secret (@repr WORDSIZE64 2323684950984523890) : int64;
        secret (@repr WORDSIZE64 11074978966450447856) : int64
      ] in  l).

Definition g1_ynum_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 336375361001233340) : int64;
        secret (@repr WORDSIZE64 12882959944969186108) : int64;
        secret (@repr WORDSIZE64 16671121624101127371) : int64;
        secret (@repr WORDSIZE64 5922586712221110071) : int64;
        secret (@repr WORDSIZE64 5163511947597922654) : int64;
        secret (@repr WORDSIZE64 14511152726087948018) : int64
      ] in  l).

Definition g1_ynum_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 686738286210365551) : int64;
        secret (@repr WORDSIZE64 16039894141796533876) : int64;
        secret (@repr WORDSIZE64 1660145734357211167) : int64;
        secret (@repr WORDSIZE64 18231571463891878950) : int64;
        secret (@repr WORDSIZE64 4825120264949852469) : int64;
        secret (@repr WORDSIZE64 11627815551290637097) : int64
      ] in  l).

Definition g1_ynum_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 719520515476580427) : int64;
        secret (@repr WORDSIZE64 16756942182913253819) : int64;
        secret (@repr WORDSIZE64 10320769399998235244) : int64;
        secret (@repr WORDSIZE64 2200974244968450750) : int64;
        secret (@repr WORDSIZE64 7626373186594408355) : int64;
        secret (@repr WORDSIZE64 6933025920263103879) : int64
      ] in  l).

Definition g1_ynum_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1016611174344998325) : int64;
        secret (@repr WORDSIZE64 2466492548686891555) : int64;
        secret (@repr WORDSIZE64 14135124294293452542) : int64;
        secret (@repr WORDSIZE64 475233659467912251) : int64;
        secret (@repr WORDSIZE64 11186783513499056751) : int64;
        secret (@repr WORDSIZE64 3147922594245844016) : int64
      ] in  l).

Definition g1_ynum_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1833315000454533566) : int64;
        secret (@repr WORDSIZE64 1007974600900082579) : int64;
        secret (@repr WORDSIZE64 14785260176242854207) : int64;
        secret (@repr WORDSIZE64 15066861003931772432) : int64;
        secret (@repr WORDSIZE64 3584647998681889532) : int64;
        secret (@repr WORDSIZE64 16722834201330696498) : int64
      ] in  l).

Definition g1_ynum_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1780164921828767454) : int64;
        secret (@repr WORDSIZE64 13337622794239929804) : int64;
        secret (@repr WORDSIZE64 5923739534552515142) : int64;
        secret (@repr WORDSIZE64 3345046972101780530) : int64;
        secret (@repr WORDSIZE64 5321510883028162054) : int64;
        secret (@repr WORDSIZE64 14846055306840460686) : int64
      ] in  l).

Definition g1_ynum_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 799438051374502809) : int64;
        secret (@repr WORDSIZE64 15083972834952036164) : int64;
        secret (@repr WORDSIZE64 8838227588559581326) : int64;
        secret (@repr WORDSIZE64 13846054168121598783) : int64;
        secret (@repr WORDSIZE64 488730451382505970) : int64;
        secret (@repr WORDSIZE64 958146249756188408) : int64
      ] in  l).

Definition g1_ynum_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 163716820423854747) : int64;
        secret (@repr WORDSIZE64 8285498163857659356) : int64;
        secret (@repr WORDSIZE64 8465424830341846400) : int64;
        secret (@repr WORDSIZE64 1433942577299613084) : int64;
        secret (@repr WORDSIZE64 14325828012864645732) : int64;
        secret (@repr WORDSIZE64 4817114329354076467) : int64
      ] in  l).

Definition g1_ynum_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 414658151749832465) : int64;
        secret (@repr WORDSIZE64 189531577938912252) : int64;
        secret (@repr WORDSIZE64 6802473390048830824) : int64;
        secret (@repr WORDSIZE64 15684647020317539556) : int64;
        secret (@repr WORDSIZE64 7755485098777620407) : int64;
        secret (@repr WORDSIZE64 9685868895687483979) : int64
      ] in  l).

Definition g1_ynum_k_15_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1578157964224562126) : int64;
        secret (@repr WORDSIZE64 5666948055268535989) : int64;
        secret (@repr WORDSIZE64 14634479491382401593) : int64;
        secret (@repr WORDSIZE64 6317940024988860850) : int64;
        secret (@repr WORDSIZE64 13142913832013798519) : int64;
        secret (@repr WORDSIZE64 338991247778166276) : int64
      ] in  l).

Definition g1_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1590100849350973618) : int64;
        secret (@repr WORDSIZE64 5915497081334721257) : int64;
        secret (@repr WORDSIZE64 6924968209373727718) : int64;
        secret (@repr WORDSIZE64 17204633670617869946) : int64;
        secret (@repr WORDSIZE64 572916540828819565) : int64;
        secret (@repr WORDSIZE64 92203205520679873) : int64
      ] in  l).

Definition g1_yden_k_1_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1829261189398470686) : int64;
        secret (@repr WORDSIZE64 1877083417397643448) : int64;
        secret (@repr WORDSIZE64 9640042925497046428) : int64;
        secret (@repr WORDSIZE64 11862766565471805471) : int64;
        secret (@repr WORDSIZE64 8693114993904885301) : int64;
        secret (@repr WORDSIZE64 3672140328108400701) : int64
      ] in  l).

Definition g1_yden_k_2_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 400243331105348135) : int64;
        secret (@repr WORDSIZE64 8046435537999802711) : int64;
        secret (@repr WORDSIZE64 8702226981475745585) : int64;
        secret (@repr WORDSIZE64 879791671491744492) : int64;
        secret (@repr WORDSIZE64 11994630442058346377) : int64;
        secret (@repr WORDSIZE64 2172204746352322546) : int64
      ] in  l).

Definition g1_yden_k_3_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1637008473169220501) : int64;
        secret (@repr WORDSIZE64 17441636237435581649) : int64;
        secret (@repr WORDSIZE64 15066165676546511630) : int64;
        secret (@repr WORDSIZE64 1314387578457599809) : int64;
        secret (@repr WORDSIZE64 8247046336453711789) : int64;
        secret (@repr WORDSIZE64 12164906044230685718) : int64
      ] in  l).

Definition g1_yden_k_4_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 855930740911588324) : int64;
        secret (@repr WORDSIZE64 12685735333705453020) : int64;
        secret (@repr WORDSIZE64 14326404096614579120) : int64;
        secret (@repr WORDSIZE64 6066025509460822294) : int64;
        secret (@repr WORDSIZE64 11676450493790612973) : int64;
        secret (@repr WORDSIZE64 15724621714793234461) : int64
      ] in  l).

Definition g1_yden_k_5_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 637792788410719021) : int64;
        secret (@repr WORDSIZE64 11507373155986977154) : int64;
        secret (@repr WORDSIZE64 13186912195705886849) : int64;
        secret (@repr WORDSIZE64 14262012144631372388) : int64;
        secret (@repr WORDSIZE64 5328758613570342114) : int64;
        secret (@repr WORDSIZE64 199925847119476652) : int64
      ] in  l).

Definition g1_yden_k_6_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1612297190139091759) : int64;
        secret (@repr WORDSIZE64 14103733843373163083) : int64;
        secret (@repr WORDSIZE64 6840121186619029743) : int64;
        secret (@repr WORDSIZE64 6760859324815900753) : int64;
        secret (@repr WORDSIZE64 15418807805142572985) : int64;
        secret (@repr WORDSIZE64 4402853133867972444) : int64
      ] in  l).

Definition g1_yden_k_7_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1631410310868805610) : int64;
        secret (@repr WORDSIZE64 269334146695233390) : int64;
        secret (@repr WORDSIZE64 16547411811928854487) : int64;
        secret (@repr WORDSIZE64 18353100669930795314) : int64;
        secret (@repr WORDSIZE64 13339932232668798692) : int64;
        secret (@repr WORDSIZE64 6984591927261867737) : int64
      ] in  l).

Definition g1_yden_k_8_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1758313625630302499) : int64;
        secret (@repr WORDSIZE64 1881349400343039172) : int64;
        secret (@repr WORDSIZE64 18013005311323887904) : int64;
        secret (@repr WORDSIZE64 12377427846571989832) : int64;
        secret (@repr WORDSIZE64 5967237584920922243) : int64;
        secret (@repr WORDSIZE64 7720081932193848650) : int64
      ] in  l).

Definition g1_yden_k_9_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1619701357752249884) : int64;
        secret (@repr WORDSIZE64 16898074901591262352) : int64;
        secret (@repr WORDSIZE64 3609344159736760251) : int64;
        secret (@repr WORDSIZE64 5983130161189999867) : int64;
        secret (@repr WORDSIZE64 14355327869992416094) : int64;
        secret (@repr WORDSIZE64 3778226018344582997) : int64
      ] in  l).

Definition g1_yden_k_10_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 347606589330687421) : int64;
        secret (@repr WORDSIZE64 5255719044972187933) : int64;
        secret (@repr WORDSIZE64 11271894388753671721) : int64;
        secret (@repr WORDSIZE64 1033887512062764488) : int64;
        secret (@repr WORDSIZE64 8189165486932690436) : int64;
        secret (@repr WORDSIZE64 70004379462101672) : int64
      ] in  l).

Definition g1_yden_k_11_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 778202887894139711) : int64;
        secret (@repr WORDSIZE64 17691595219776375879) : int64;
        secret (@repr WORDSIZE64 9193253711563866834) : int64;
        secret (@repr WORDSIZE64 10092455202333888821) : int64;
        secret (@repr WORDSIZE64 1655469341950262250) : int64;
        secret (@repr WORDSIZE64 10845992994110574738) : int64
      ] in  l).

Definition g1_yden_k_12_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 781015344221683683) : int64;
        secret (@repr WORDSIZE64 14078588081290548374) : int64;
        secret (@repr WORDSIZE64 6067271023149908518) : int64;
        secret (@repr WORDSIZE64 9033357708497886086) : int64;
        secret (@repr WORDSIZE64 10592474449179118273) : int64;
        secret (@repr WORDSIZE64 2204988348113831372) : int64
      ] in  l).

Definition g1_yden_k_13_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 172830037692534587) : int64;
        secret (@repr WORDSIZE64 7101012286790006514) : int64;
        secret (@repr WORDSIZE64 13787308004332873665) : int64;
        secret (@repr WORDSIZE64 14660498759553796110) : int64;
        secret (@repr WORDSIZE64 4757234684169342080) : int64;
        secret (@repr WORDSIZE64 15130647872920159991) : int64
      ] in  l).

Definition g1_yden_k_14_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1013206390650290238) : int64;
        secret (@repr WORDSIZE64 7720336747103001025) : int64;
        secret (@repr WORDSIZE64 8197694151986493523) : int64;
        secret (@repr WORDSIZE64 3625112747029342752) : int64;
        secret (@repr WORDSIZE64 6675167463148394368) : int64;
        secret (@repr WORDSIZE64 4905905684016745359) : int64
      ] in  l).

Definition g1_simple_swu_iso (u_1539 : fp_t) : (fp_t × fp_t) :=
  let z_1540 : fp_t :=
    nat_mod_from_literal (_) (@repr WORDSIZE128 11) : fp_t in 
  let a_1541 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_a_v)) : fp_t in 
  let b_1542 : fp_t :=
    nat_mod_from_byte_seq_be (array_to_be_bytes (g1_iso_b_v)) : fp_t in 
  let tv1_1543 : fp_t :=
    nat_mod_inv ((((z_1540) *% (z_1540)) *% (nat_mod_exp (u_1539) (
            @repr WORDSIZE32 4))) +% (((z_1540) *% (u_1539)) *% (u_1539))) in 
  let x1_1544 : fp_t :=
    (((nat_mod_zero ) -% (b_1542)) *% (nat_mod_inv (a_1541))) *% ((
        nat_mod_one ) +% (tv1_1543)) in 
  let '(x1_1544) :=
    if (tv1_1543) =.? (nat_mod_zero ):bool then (let x1_1544 :=
        (b_1542) *% (nat_mod_inv ((z_1540) *% (a_1541))) in 
      (x1_1544)) else ((x1_1544)) in 
  let gx1_1545 : fp_t :=
    ((nat_mod_exp (x1_1544) (@repr WORDSIZE32 3)) +% ((a_1541) *% (
          x1_1544))) +% (b_1542) in 
  let x2_1546 : fp_t :=
    (((z_1540) *% (u_1539)) *% (u_1539)) *% (x1_1544) in 
  let gx2_1547 : fp_t :=
    ((nat_mod_exp (x2_1546) (@repr WORDSIZE32 3)) +% ((a_1541) *% (
          x2_1546))) +% (b_1542) in 
  let '(x_1548, y_1549) :=
    (if (fp_is_square (gx1_1545)):bool then ((x1_1544, fp_sqrt (gx1_1545)
        )) else ((x2_1546, fp_sqrt (gx2_1547)))) in 
  let '(y_1549) :=
    if (fp_sgn0 (u_1539)) !=.? (fp_sgn0 (y_1549)):bool then (let y_1549 :=
        (nat_mod_zero ) -% (y_1549) in 
      (y_1549)) else ((y_1549)) in 
  (x_1548, y_1549).

Definition g1_isogeny_map (x_1550 : fp_t) (y_1551 : fp_t) : g1_t :=
  let xnum_k_1552 : seq fp_t :=
    seq_new_ (default) (usize 12) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_0_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_1_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_2_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_3_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_4_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_5_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_6_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_7_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_8_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xnum_k_9_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_10_v)) : fp_t) in 
  let xnum_k_1552 :=
    seq_upd xnum_k_1552 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_xnum_k_11_v)) : fp_t) in 
  let xden_k_1553 : seq fp_t :=
    seq_new_ (default) (usize 10) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_0_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_1_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_2_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_3_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_4_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_5_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_6_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_7_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_8_v)) : fp_t) in 
  let xden_k_1553 :=
    seq_upd xden_k_1553 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_xden_k_9_v)) : fp_t) in 
  let ynum_k_1554 : seq fp_t :=
    seq_new_ (default) (usize 16) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_0_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_1_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_2_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_3_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_4_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_5_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_6_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_7_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_8_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_ynum_k_9_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_10_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_11_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_12_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_13_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_14_v)) : fp_t) in 
  let ynum_k_1554 :=
    seq_upd ynum_k_1554 (usize 15) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_ynum_k_15_v)) : fp_t) in 
  let yden_k_1555 : seq fp_t :=
    seq_new_ (default) (usize 15) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 0) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_0_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 1) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_1_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 2) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_2_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 3) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_3_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 4) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_4_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 5) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_5_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 6) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_6_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 7) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_7_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 8) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_8_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 9) (nat_mod_from_byte_seq_be (array_to_be_bytes (
          g1_yden_k_9_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 10) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_10_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 11) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_11_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 12) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_12_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 13) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_13_v)) : fp_t) in 
  let yden_k_1555 :=
    seq_upd yden_k_1555 (usize 14) (nat_mod_from_byte_seq_be (
        array_to_be_bytes (g1_yden_k_14_v)) : fp_t) in 
  let xnum_1556 : fp_t :=
    nat_mod_zero  in 
  let xx_1557 : fp_t :=
    nat_mod_one  in 
  let '(xnum_1556, xx_1557) :=
    foldi (usize 0) (seq_len (xnum_k_1552)) (fun i_1558 '(xnum_1556, xx_1557) =>
      let xnum_1556 :=
        (xnum_1556) +% ((xx_1557) *% (seq_index (xnum_k_1552) (i_1558))) in 
      let xx_1557 :=
        (xx_1557) *% (x_1550) in 
      (xnum_1556, xx_1557))
    (xnum_1556, xx_1557) in 
  let xden_1559 : fp_t :=
    nat_mod_zero  in 
  let xx_1560 : fp_t :=
    nat_mod_one  in 
  let '(xden_1559, xx_1560) :=
    foldi (usize 0) (seq_len (xden_k_1553)) (fun i_1561 '(xden_1559, xx_1560) =>
      let xden_1559 :=
        (xden_1559) +% ((xx_1560) *% (seq_index (xden_k_1553) (i_1561))) in 
      let xx_1560 :=
        (xx_1560) *% (x_1550) in 
      (xden_1559, xx_1560))
    (xden_1559, xx_1560) in 
  let xden_1559 :=
    (xden_1559) +% (xx_1560) in 
  let ynum_1562 : fp_t :=
    nat_mod_zero  in 
  let xx_1563 : fp_t :=
    nat_mod_one  in 
  let '(ynum_1562, xx_1563) :=
    foldi (usize 0) (seq_len (ynum_k_1554)) (fun i_1564 '(ynum_1562, xx_1563) =>
      let ynum_1562 :=
        (ynum_1562) +% ((xx_1563) *% (seq_index (ynum_k_1554) (i_1564))) in 
      let xx_1563 :=
        (xx_1563) *% (x_1550) in 
      (ynum_1562, xx_1563))
    (ynum_1562, xx_1563) in 
  let yden_1565 : fp_t :=
    nat_mod_zero  in 
  let xx_1566 : fp_t :=
    nat_mod_one  in 
  let '(yden_1565, xx_1566) :=
    foldi (usize 0) (seq_len (yden_k_1555)) (fun i_1567 '(yden_1565, xx_1566) =>
      let yden_1565 :=
        (yden_1565) +% ((xx_1566) *% (seq_index (yden_k_1555) (i_1567))) in 
      let xx_1566 :=
        (xx_1566) *% (x_1550) in 
      (yden_1565, xx_1566))
    (yden_1565, xx_1566) in 
  let yden_1565 :=
    (yden_1565) +% (xx_1566) in 
  let xr_1568 : fp_t :=
    (xnum_1556) *% (nat_mod_inv (xden_1559)) in 
  let yr_1569 : fp_t :=
    ((y_1551) *% (ynum_1562)) *% (nat_mod_inv (yden_1565)) in 
  let inf_1570 : bool :=
    false in 
  let '(inf_1570) :=
    if ((xden_1559) =.? (nat_mod_zero )) || ((yden_1565) =.? (
        nat_mod_zero )):bool then (let inf_1570 :=
        true in 
      (inf_1570)) else ((inf_1570)) in 
  (xr_1568, yr_1569, inf_1570).

Definition g1_map_to_curve_sswu (u_1571 : fp_t) : g1_t :=
  let '(xp_1572, yp_1573) :=
    g1_simple_swu_iso (u_1571) in 
  let p_1574 : (fp_t × fp_t × bool) :=
    g1_isogeny_map (xp_1572) (yp_1573) in 
  p_1574.

Definition g1_hash_to_curve_sswu
  (msg_1575 : byte_seq)
  (dst_1576 : byte_seq)
  : g1_t :=
  let u_1577 : seq fp_t :=
    fp_hash_to_field (msg_1575) (dst_1576) (usize 2) in 
  let q0_1578 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1577) (usize 0)) in 
  let q1_1579 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1577) (usize 1)) in 
  let r_1580 : (fp_t × fp_t × bool) :=
    g1add (q0_1578) (q1_1579) in 
  let p_1581 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (r_1580) in 
  p_1581.

Definition g1_encode_to_curve_sswu
  (msg_1582 : byte_seq)
  (dst_1583 : byte_seq)
  : g1_t :=
  let u_1584 : seq fp_t :=
    fp_hash_to_field (msg_1582) (dst_1583) (usize 1) in 
  let q_1585 : (fp_t × fp_t × bool) :=
    g1_map_to_curve_sswu (seq_index (u_1584) (usize 0)) in 
  let p_1586 : (fp_t × fp_t × bool) :=
    g1_clear_cofactor (q_1585) in 
  p_1586.

Definition g2_xnum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203414) : int64
      ] in  l).

Definition g2_xnum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058522) : int64
      ] in  l).

Definition g2_xnum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058526) : int64
      ] in  l).

Definition g2_xnum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805069) : int64
      ] in  l).

Definition g2_xnum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1665598771242257658) : int64;
        secret (@repr WORDSIZE64 17108588296669214228) : int64;
        secret (@repr WORDSIZE64 14633519997572878506) : int64;
        secret (@repr WORDSIZE64 2510212049010394485) : int64;
        secret (@repr WORDSIZE64 8113484923696258161) : int64;
        secret (@repr WORDSIZE64 9863633783879261905) : int64
      ] in  l).

Definition g2_xden_k_0_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863523) : int64
      ] in  l).

Definition g2_xden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863583) : int64
      ] in  l).

Definition g2_ynum_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1526798873638736187) : int64;
        secret (@repr WORDSIZE64 6459500568425337235) : int64;
        secret (@repr WORDSIZE64 1116230615302104219) : int64;
        secret (@repr WORDSIZE64 17673314439684154624) : int64;
        secret (@repr WORDSIZE64 18197961889718808424) : int64;
        secret (@repr WORDSIZE64 1355520937843676934) : int64
      ] in  l).

Definition g2_ynum_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 416399692810564414) : int64;
        secret (@repr WORDSIZE64 13500519111022079365) : int64;
        secret (@repr WORDSIZE64 3658379999393219626) : int64;
        secret (@repr WORDSIZE64 9850925049107374429) : int64;
        secret (@repr WORDSIZE64 6640057249351452444) : int64;
        secret (@repr WORDSIZE64 7077594464397203390) : int64
      ] in  l).

Definition g2_ynum_k_2_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1249199078431693244) : int64;
        secret (@repr WORDSIZE64 3608069185647134863) : int64;
        secret (@repr WORDSIZE64 10975139998179658879) : int64;
        secret (@repr WORDSIZE64 11106031073612571672) : int64;
        secret (@repr WORDSIZE64 1473427674344805717) : int64;
        secret (@repr WORDSIZE64 2786039319482058524) : int64
      ] in  l).

Definition g2_ynum_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 624599539215846622) : int64;
        secret (@repr WORDSIZE64 1804034592823567431) : int64;
        secret (@repr WORDSIZE64 14710942035944605247) : int64;
        secret (@repr WORDSIZE64 14776387573661061644) : int64;
        secret (@repr WORDSIZE64 736713837172402858) : int64;
        secret (@repr WORDSIZE64 10616391696595805071) : int64
      ] in  l).

Definition g2_ynum_k_3_r_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1318599027233453979) : int64;
        secret (@repr WORDSIZE64 18155985086623849168) : int64;
        secret (@repr WORDSIZE64 8510412652460270214) : int64;
        secret (@repr WORDSIZE64 12747851915130467410) : int64;
        secret (@repr WORDSIZE64 5654561228188306393) : int64;
        secret (@repr WORDSIZE64 16263467779354626832) : int64
      ] in  l).

Definition g2_yden_k_0_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863163) : int64
      ] in  l).

Definition g2_yden_k_1_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863379) : int64
      ] in  l).

Definition g2_yden_k_2_i_v : arr_fp_t :=
  array_from_list uint64 (let l :=
      [
        secret (@repr WORDSIZE64 1873798617647539866) : int64;
        secret (@repr WORDSIZE64 5412103778470702295) : int64;
        secret (@repr WORDSIZE64 7239337960414712511) : int64;
        secret (@repr WORDSIZE64 7435674573564081700) : int64;
        secret (@repr WORDSIZE64 2210141511517208575) : int64;
        secret (@repr WORDSIZE64 13402431016077863577) : int64
      ] in  l).

Definition g2_simple_swu_iso (u_1587 : fp2_t) : (fp2_t × fp2_t) :=
  let z_1588 : (fp_t × fp_t) :=
    fp2neg ((nat_mod_two , nat_mod_one )) in 
  let a_1589 : (fp_t × fp_t) :=
    (nat_mod_zero , nat_mod_from_literal (_) (@repr WORDSIZE128 240) : fp_t) in 
  let b_1590 : (fp_t × fp_t) :=
    (
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t,
      nat_mod_from_literal (_) (@repr WORDSIZE128 1012) : fp_t
    ) in 
  let tv1_1591 : (fp_t × fp_t) :=
    fp2inv (fp2add (fp2mul (fp2mul (z_1588) (z_1588)) (fp2mul (fp2mul (u_1587) (
              u_1587)) (fp2mul (u_1587) (u_1587)))) (fp2mul (z_1588) (fp2mul (
            u_1587) (u_1587)))) in 
  let x1_1592 : (fp_t × fp_t) :=
    fp2mul (fp2mul (fp2neg (b_1590)) (fp2inv (a_1589))) (fp2add (fp2fromfp (
          nat_mod_one )) (tv1_1591)) in 
  let '(x1_1592) :=
    if (tv1_1591) =.? (fp2zero ):bool then (let x1_1592 :=
        fp2mul (b_1590) (fp2inv (fp2mul (z_1588) (a_1589))) in 
      (x1_1592)) else ((x1_1592)) in 
  let gx1_1593 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x1_1592) (x1_1592)) (x1_1592)) (fp2mul (
          a_1589) (x1_1592))) (b_1590) in 
  let x2_1594 : (fp_t × fp_t) :=
    fp2mul (fp2mul (z_1588) (fp2mul (u_1587) (u_1587))) (x1_1592) in 
  let gx2_1595 : (fp_t × fp_t) :=
    fp2add (fp2add (fp2mul (fp2mul (x2_1594) (x2_1594)) (x2_1594)) (fp2mul (
          a_1589) (x2_1594))) (b_1590) in 
  let '(x_1596, y_1597) :=
    (if (fp2_is_square (gx1_1593)):bool then ((x1_1592, fp2_sqrt (gx1_1593)
        )) else ((x2_1594, fp2_sqrt (gx2_1595)))) in 
  let '(y_1597) :=
    if (fp2_sgn0 (u_1587)) !=.? (fp2_sgn0 (y_1597)):bool then (let y_1597 :=
        fp2neg (y_1597) in 
      (y_1597)) else ((y_1597)) in 
  (x_1596, y_1597).

Definition g2_isogeny_map (x_1598 : fp2_t) (y_1599 : fp2_t) : g2_t :=
  let xnum_k_1600 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 4) in 
  let xnum_k_1600 :=
    seq_upd xnum_k_1600 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_0_v)) : fp_t
      )) in 
  let xnum_k_1600 :=
    seq_upd xnum_k_1600 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_1_i_v)) : fp_t
      )) in 
  let xnum_k_1600 :=
    seq_upd xnum_k_1600 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_2_i_v)) : fp_t
      )) in 
  let xnum_k_1600 :=
    seq_upd xnum_k_1600 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xnum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let xden_k_1601 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 2) in 
  let xden_k_1601 :=
    seq_upd xden_k_1601 (usize 0) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_0_i_v)) : fp_t
      )) in 
  let xden_k_1601 :=
    seq_upd xden_k_1601 (usize 1) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 12) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_xden_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_1602 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 4) in 
  let ynum_k_1602 :=
    seq_upd ynum_k_1602 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_0_v)) : fp_t
      )) in 
  let ynum_k_1602 :=
    seq_upd ynum_k_1602 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_1_i_v)) : fp_t
      )) in 
  let ynum_k_1602 :=
    seq_upd ynum_k_1602 (usize 2) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_r_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_2_i_v)) : fp_t
      )) in 
  let ynum_k_1602 :=
    seq_upd ynum_k_1602 (usize 3) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_ynum_k_3_r_v)) : fp_t,
        nat_mod_zero 
      )) in 
  let yden_k_1603 : seq (fp_t × fp_t) :=
    seq_new_ (default) (usize 3) in 
  let yden_k_1603 :=
    seq_upd yden_k_1603 (usize 0) ((
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_0_v)) : fp_t
      )) in 
  let yden_k_1603 :=
    seq_upd yden_k_1603 (usize 1) ((
        nat_mod_zero ,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_1_i_v)) : fp_t
      )) in 
  let yden_k_1603 :=
    seq_upd yden_k_1603 (usize 2) ((
        nat_mod_from_literal (_) (@repr WORDSIZE128 18) : fp_t,
        nat_mod_from_byte_seq_be (array_to_be_bytes (g2_yden_k_2_i_v)) : fp_t
      )) in 
  let xnum_1604 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1605 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xnum_1604, xx_1605) :=
    foldi (usize 0) (seq_len (xnum_k_1600)) (fun i_1606 '(xnum_1604, xx_1605) =>
      let xnum_1604 :=
        fp2add (xnum_1604) (fp2mul (xx_1605) (seq_index (xnum_k_1600) (
              i_1606))) in 
      let xx_1605 :=
        fp2mul (xx_1605) (x_1598) in 
      (xnum_1604, xx_1605))
    (xnum_1604, xx_1605) in 
  let xden_1607 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1608 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(xden_1607, xx_1608) :=
    foldi (usize 0) (seq_len (xden_k_1601)) (fun i_1609 '(xden_1607, xx_1608) =>
      let xden_1607 :=
        fp2add (xden_1607) (fp2mul (xx_1608) (seq_index (xden_k_1601) (
              i_1609))) in 
      let xx_1608 :=
        fp2mul (xx_1608) (x_1598) in 
      (xden_1607, xx_1608))
    (xden_1607, xx_1608) in 
  let xden_1607 :=
    fp2add (xden_1607) (xx_1608) in 
  let ynum_1610 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1611 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(ynum_1610, xx_1611) :=
    foldi (usize 0) (seq_len (ynum_k_1602)) (fun i_1612 '(ynum_1610, xx_1611) =>
      let ynum_1610 :=
        fp2add (ynum_1610) (fp2mul (xx_1611) (seq_index (ynum_k_1602) (
              i_1612))) in 
      let xx_1611 :=
        fp2mul (xx_1611) (x_1598) in 
      (ynum_1610, xx_1611))
    (ynum_1610, xx_1611) in 
  let yden_1613 : (fp_t × fp_t) :=
    fp2zero  in 
  let xx_1614 : (fp_t × fp_t) :=
    fp2fromfp (nat_mod_one ) in 
  let '(yden_1613, xx_1614) :=
    foldi (usize 0) (seq_len (yden_k_1603)) (fun i_1615 '(yden_1613, xx_1614) =>
      let yden_1613 :=
        fp2add (yden_1613) (fp2mul (xx_1614) (seq_index (yden_k_1603) (
              i_1615))) in 
      let xx_1614 :=
        fp2mul (xx_1614) (x_1598) in 
      (yden_1613, xx_1614))
    (yden_1613, xx_1614) in 
  let yden_1613 :=
    fp2add (yden_1613) (xx_1614) in 
  let xr_1616 : (fp_t × fp_t) :=
    fp2mul (xnum_1604) (fp2inv (xden_1607)) in 
  let yr_1617 : (fp_t × fp_t) :=
    fp2mul (y_1599) (fp2mul (ynum_1610) (fp2inv (yden_1613))) in 
  let inf_1618 : bool :=
    false in 
  let '(inf_1618) :=
    if ((xden_1607) =.? (fp2zero )) || ((yden_1613) =.? (fp2zero )):bool then (
      let inf_1618 :=
        true in 
      (inf_1618)) else ((inf_1618)) in 
  (xr_1616, yr_1617, inf_1618).

Definition g2_map_to_curve_sswu (u_1619 : fp2_t) : g2_t :=
  let '(xp_1620, yp_1621) :=
    g2_simple_swu_iso (u_1619) in 
  let p_1622 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_isogeny_map (xp_1620) (yp_1621) in 
  p_1622.

Definition g2_hash_to_curve_sswu
  (msg_1623 : byte_seq)
  (dst_1624 : byte_seq)
  : g2_t :=
  let u_1625 : seq fp2_t :=
    fp2_hash_to_field (msg_1623) (dst_1624) (usize 2) in 
  let q0_1626 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1625) (usize 0)) in 
  let q1_1627 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1625) (usize 1)) in 
  let r_1628 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2add (q0_1626) (q1_1627) in 
  let p_1629 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (r_1628) in 
  p_1629.

Definition g2_encode_to_curve_sswu
  (msg_1630 : byte_seq)
  (dst_1631 : byte_seq)
  : g2_t :=
  let u_1632 : seq fp2_t :=
    fp2_hash_to_field (msg_1630) (dst_1631) (usize 1) in 
  let q_1633 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_map_to_curve_sswu (seq_index (u_1632) (usize 0)) in 
  let p_1634 : ((fp_t × fp_t) × (fp_t × fp_t) × bool) :=
    g2_clear_cofactor (q_1633) in 
  p_1634.

