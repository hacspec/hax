(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
From QuickChick Require Import QuickChick.
Require Import QuickChickLib.
Require Import Hacspec_Lib.

Definition fp_canvas_t := nseq (int8) (48).
Definition fp_t :=
  nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab.
Instance show_fp_t : Show (fp_t) := Build_Show (fp_t) (fun x => show (GZnZ.val _ x)).
Definition g_fp_t : G (fp_t) := @bindGen Z (fp_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_fp_t : Gen (fp_t) := Build_Gen fp_t g_fp_t.


Definition serialized_fp_t := nseq (uint8) (usize 48).

Definition array_fp_t := nseq (uint64) (usize 6).

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000.
Instance show_scalar_t : Show (scalar_t) := Build_Show (scalar_t) (fun x => show (GZnZ.val _ x)).
Definition g_scalar_t : G (scalar_t) := @bindGen Z (scalar_t) (arbitrary) (fun x => returnGen (@Z_in_nat_mod _ x)).
Instance gen_scalar_t : Gen (scalar_t) := Build_Gen scalar_t g_scalar_t.


Notation "'g1_t'" := ((fp_t '× fp_t '× bool)) : hacspec_scope.
Instance show_g1_t : Show (g1_t) :=
Build_Show g1_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g1_t : G (g1_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g1_t : Gen (g1_t) := Build_Gen g1_t g_g1_t.


Notation "'fp2_t'" := ((fp_t '× fp_t)) : hacspec_scope.
Instance show_fp2_t : Show (fp2_t) :=
Build_Show fp2_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp2_t : G (fp2_t) :=
bindGen arbitrary (fun x0 : fp_t =>
  bindGen arbitrary (fun x1 : fp_t =>
  returnGen (x0,x1))).
Instance gen_fp2_t : Gen (fp2_t) := Build_Gen fp2_t g_fp2_t.


Notation "'g2_t'" := ((fp2_t '× fp2_t '× bool)) : hacspec_scope.
Instance show_g2_t : Show (g2_t) :=
Build_Show g2_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_g2_t : G (g2_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : bool =>
  returnGen (x0,x1,x2)))).
Instance gen_g2_t : Gen (g2_t) := Build_Gen g2_t g_g2_t.


Notation "'fp6_t'" := ((fp2_t '× fp2_t '× fp2_t)) : hacspec_scope.
Instance show_fp6_t : Show (fp6_t) :=
Build_Show fp6_t (fun x =>
  let (x, x0) := x in
  let (x, x1) := x in
  (
    ("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ ((",") ++ ((show x1) ++ (")"))))))))%string.
Definition g_fp6_t : G (fp6_t) :=
bindGen arbitrary (fun x0 : fp2_t =>
  bindGen arbitrary (fun x1 : fp2_t =>
  bindGen arbitrary (fun x2 : fp2_t =>
  returnGen (x0,x1,x2)))).
Instance gen_fp6_t : Gen (fp6_t) := Build_Gen fp6_t g_fp6_t.


Notation "'fp12_t'" := ((fp6_t '× fp6_t)) : hacspec_scope.
Instance show_fp12_t : Show (fp12_t) :=
Build_Show fp12_t (fun x =>
  let (x, x0) := x in
  (("(") ++ ((show x) ++ ((",") ++ ((show x0) ++ (")"))))))%string.
Definition g_fp12_t : G (fp12_t) :=
bindGen arbitrary (fun x0 : fp6_t =>
  bindGen arbitrary (fun x1 : fp6_t =>
  returnGen (x0,x1))).
Instance gen_fp12_t : Gen (fp12_t) := Build_Gen fp12_t g_fp12_t.


Definition fp2fromfp (n_1405 : fp_t) : fp2_t :=
  (n_1405, nat_mod_zero ).

Definition fp2zero  : fp2_t :=
  fp2fromfp (nat_mod_zero ).

Definition fp2neg (n_1406 : fp2_t) : fp2_t :=
  let '(n1_1407, n2_1408) :=
    n_1406 in 
  ((nat_mod_zero ) -% (n1_1407), (nat_mod_zero ) -% (n2_1408)).

Definition fp2add (n_1409 : fp2_t) (m_1410 : fp2_t) : fp2_t :=
  let '(n1_1411, n2_1412) :=
    n_1409 in 
  let '(m1_1413, m2_1414) :=
    m_1410 in 
  ((n1_1411) +% (m1_1413), (n2_1412) +% (m2_1414)).

Definition fp2sub (n_1415 : fp2_t) (m_1416 : fp2_t) : fp2_t :=
  fp2add (n_1415) (fp2neg (m_1416)).

Definition fp2mul (n_1417 : fp2_t) (m_1418 : fp2_t) : fp2_t :=
  let '(n1_1419, n2_1420) :=
    n_1417 in 
  let '(m1_1421, m2_1422) :=
    m_1418 in 
  let x1_1423 : fp_t :=
    ((n1_1419) *% (m1_1421)) -% ((n2_1420) *% (m2_1422)) in 
  let x2_1424 : fp_t :=
    ((n1_1419) *% (m2_1422)) +% ((n2_1420) *% (m1_1421)) in 
  (x1_1423, x2_1424).

Definition fp2inv (n_1425 : fp2_t) : fp2_t :=
  let '(n1_1426, n2_1427) :=
    n_1425 in 
  let t0_1428 : fp_t :=
    ((n1_1426) *% (n1_1426)) +% ((n2_1427) *% (n2_1427)) in 
  let t1_1429 : fp_t :=
    nat_mod_inv (t0_1428) in 
  let x1_1430 : fp_t :=
    (n1_1426) *% (t1_1429) in 
  let x2_1431 : fp_t :=
    (nat_mod_zero ) -% ((n2_1427) *% (t1_1429)) in 
  (x1_1430, x2_1431).

Definition fp2conjugate (n_1432 : fp2_t) : fp2_t :=
  let '(n1_1433, n2_1434) :=
    n_1432 in 
  (n1_1433, (nat_mod_zero ) -% (n2_1434)).

Definition fp6fromfp2 (n_1435 : fp2_t) : fp6_t :=
  (n_1435, fp2zero , fp2zero ).

Definition fp6zero  : fp6_t :=
  fp6fromfp2 (fp2zero ).

Definition fp6neg (n_1436 : fp6_t) : fp6_t :=
  let '(n1_1437, n2_1438, n3_1439) :=
    n_1436 in 
  (
    fp2sub (fp2zero ) (n1_1437),
    fp2sub (fp2zero ) (n2_1438),
    fp2sub (fp2zero ) (n3_1439)
  ).

Definition fp6add (n_1440 : fp6_t) (m_1441 : fp6_t) : fp6_t :=
  let '(n1_1442, n2_1443, n3_1444) :=
    n_1440 in 
  let '(m1_1445, m2_1446, m3_1447) :=
    m_1441 in 
  (
    fp2add (n1_1442) (m1_1445),
    fp2add (n2_1443) (m2_1446),
    fp2add (n3_1444) (m3_1447)
  ).

Definition fp6sub (n_1448 : fp6_t) (m_1449 : fp6_t) : fp6_t :=
  fp6add (n_1448) (fp6neg (m_1449)).

Definition fp6mul (n_1450 : fp6_t) (m_1451 : fp6_t) : fp6_t :=
  let '(n1_1452, n2_1453, n3_1454) :=
    n_1450 in 
  let '(m1_1455, m2_1456, m3_1457) :=
    m_1451 in 
  let eps_1458 : (fp_t '× fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1459 : (fp_t '× fp_t) :=
    fp2mul (n1_1452) (m1_1455) in 
  let t2_1460 : (fp_t '× fp_t) :=
    fp2mul (n2_1453) (m2_1456) in 
  let t3_1461 : (fp_t '× fp_t) :=
    fp2mul (n3_1454) (m3_1457) in 
  let t4_1462 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n2_1453) (n3_1454)) (fp2add (m2_1456) (m3_1457)) in 
  let t5_1463 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1462) (t2_1460)) (t3_1461) in 
  let x_1464 : (fp_t '× fp_t) :=
    fp2add (fp2mul (t5_1463) (eps_1458)) (t1_1459) in 
  let t4_1465 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n1_1452) (n2_1453)) (fp2add (m1_1455) (m2_1456)) in 
  let t5_1466 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1465) (t1_1459)) (t2_1460) in 
  let y_1467 : (fp_t '× fp_t) :=
    fp2add (t5_1466) (fp2mul (eps_1458) (t3_1461)) in 
  let t4_1468 : (fp_t '× fp_t) :=
    fp2mul (fp2add (n1_1452) (n3_1454)) (fp2add (m1_1455) (m3_1457)) in 
  let t5_1469 : (fp_t '× fp_t) :=
    fp2sub (fp2sub (t4_1468) (t1_1459)) (t3_1461) in 
  let z_1470 : (fp_t '× fp_t) :=
    fp2add (t5_1469) (t2_1460) in 
  (x_1464, y_1467, z_1470).

Definition fp6inv (n_1471 : fp6_t) : fp6_t :=
  let '(n1_1472, n2_1473, n3_1474) :=
    n_1471 in 
  let eps_1475 : (fp_t '× fp_t) :=
    (nat_mod_one , nat_mod_one ) in 
  let t1_1476 : (fp_t '× fp_t) :=
    fp2mul (n1_1472) (n1_1472) in 
  let t2_1477 : (fp_t '× fp_t) :=
    fp2mul (n2_1473) (n2_1473) in 
  let t3_1478 : (fp_t '× fp_t) :=
    fp2mul (n3_1474) (n3_1474) in 
  let t4_1479 : (fp_t '× fp_t) :=
    fp2mul (n1_1472) (n2_1473) in 
  let t5_1480 : (fp_t '× fp_t) :=
    fp2mul (n1_1472) (n3_1474) in 
  let t6_1481 : (fp_t '× fp_t) :=
    fp2mul (n2_1473) (n3_1474) in 
  let x0_1482 : (fp_t '× fp_t) :=
    fp2sub (t1_1476) (fp2mul (eps_1475) (t6_1481)) in 
  let y0_1483 : (fp_t '× fp_t) :=
    fp2sub (fp2mul (eps_1475) (t3_1478)) (t4_1479) in 
  let z0_1484 : (fp_t '× fp_t) :=
    fp2sub (t2_1477) (t5_1480) in 
  let t0_1485 : (fp_t '× fp_t) :=
    fp2mul (n1_1472) (x0_1482) in 
  let t0_1486 : (fp_t '× fp_t) :=
    fp2add (t0_1485) (fp2mul (eps_1475) (fp2mul (n3_1474) (y0_1483))) in 
  let t0_1487 : (fp_t '× fp_t) :=
    fp2add (t0_1486) (fp2mul (eps_1475) (fp2mul (n2_1473) (z0_1484))) in 
  let t0_1488 : (fp_t '× fp_t) :=
    fp2inv (t0_1487) in 
  let x_1489 : (fp_t '× fp_t) :=
    fp2mul (x0_1482) (t0_1488) in 
  let y_1490 : (fp_t '× fp_t) :=
    fp2mul (y0_1483) (t0_1488) in 
  let z_1491 : (fp_t '× fp_t) :=
    fp2mul (z0_1484) (t0_1488) in 
  (x_1489, y_1490, z_1491).

Definition fp12fromfp6 (n_1492 : fp6_t) : fp12_t :=
  (n_1492, fp6zero ).

Definition fp12neg (n_1493 : fp12_t) : fp12_t :=
  let '(n1_1494, n2_1495) :=
    n_1493 in 
  (fp6sub (fp6zero ) (n1_1494), fp6sub (fp6zero ) (n2_1495)).

Definition fp12add (n_1496 : fp12_t) (m_1497 : fp12_t) : fp12_t :=
  let '(n1_1498, n2_1499) :=
    n_1496 in 
  let '(m1_1500, m2_1501) :=
    m_1497 in 
  (fp6add (n1_1498) (m1_1500), fp6add (n2_1499) (m2_1501)).

Definition fp12sub (n_1502 : fp12_t) (m_1503 : fp12_t) : fp12_t :=
  fp12add (n_1502) (fp12neg (m_1503)).

Definition fp12mul (n_1504 : fp12_t) (m_1505 : fp12_t) : fp12_t :=
  let '(n1_1506, n2_1507) :=
    n_1504 in 
  let '(m1_1508, m2_1509) :=
    m_1505 in 
  let gamma_1510 : (fp2_t '× fp2_t '× fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1511 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1506) (m1_1508) in 
  let t2_1512 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n2_1507) (m2_1509) in 
  let x_1513 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6add (t1_1511) (fp6mul (t2_1512) (gamma_1510)) in 
  let y_1514 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (fp6add (n1_1506) (n2_1507)) (fp6add (m1_1508) (m2_1509)) in 
  let y_1515 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6sub (fp6sub (y_1514) (t1_1511)) (t2_1512) in 
  (x_1513, y_1515).

Definition fp12inv (n_1516 : fp12_t) : fp12_t :=
  let '(n1_1517, n2_1518) :=
    n_1516 in 
  let gamma_1519 : (fp2_t '× fp2_t '× fp2_t) :=
    (fp2zero , fp2fromfp (nat_mod_one ), fp2zero ) in 
  let t1_1520 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1517) (n1_1517) in 
  let t2_1521 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n2_1518) (n2_1518) in 
  let t1_1522 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6sub (t1_1520) (fp6mul (gamma_1519) (t2_1521)) in 
  let t2_1523 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6inv (t1_1522) in 
  let x_1524 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6mul (n1_1517) (t2_1523) in 
  let y_1525 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6neg (fp6mul (n2_1518) (t2_1523)) in 
  (x_1524, y_1525).

Definition fp12exp (n_1526 : fp12_t) (k_1527 : scalar_t) : fp12_t :=
  let c_1528 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let c_1528 :=
    foldi (usize 0) (usize 256) (fun i_1529 c_1528 =>
      let c_1528 :=
        fp12mul (c_1528) (c_1528) in 
      let '(c_1528) :=
        if nat_mod_bit (k_1527) ((usize 255) - (i_1529)):bool then (
          let c_1528 :=
            fp12mul (c_1528) (n_1526) in 
          (c_1528)) else ((c_1528)) in 
      (c_1528))
    c_1528 in 
  c_1528.

Definition fp12conjugate (n_1530 : fp12_t) : fp12_t :=
  let '(n1_1531, n2_1532) :=
    n_1530 in 
  (n1_1531, fp6neg (n2_1532)).

Definition fp12zero  : fp12_t :=
  fp12fromfp6 (fp6zero ).

Definition g1add_a (p_1533 : g1_t) (q_1534 : g1_t) : g1_t :=
  let '(x1_1535, y1_1536, _) :=
    p_1533 in 
  let '(x2_1537, y2_1538, _) :=
    q_1534 in 
  let x_diff_1539 : fp_t :=
    (x2_1537) -% (x1_1535) in 
  let y_diff_1540 : fp_t :=
    (y2_1538) -% (y1_1536) in 
  let xovery_1541 : fp_t :=
    (y_diff_1540) *% (nat_mod_inv (x_diff_1539)) in 
  let x3_1542 : fp_t :=
    ((nat_mod_exp (xovery_1541) (@repr WORDSIZE32 2)) -% (x1_1535)) -% (
      x2_1537) in 
  let y3_1543 : fp_t :=
    ((xovery_1541) *% ((x1_1535) -% (x3_1542))) -% (y1_1536) in 
  (x3_1542, y3_1543, false).

Definition g1double_a (p_1544 : g1_t) : g1_t :=
  let '(x1_1545, y1_1546, _) :=
    p_1544 in 
  let x12_1547 : fp_t :=
    nat_mod_exp (x1_1545) (@repr WORDSIZE32 2) in 
  let xovery_1548 : fp_t :=
    ((nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t) *% (x12_1547)) *% (nat_mod_inv ((
          nat_mod_two ) *% (y1_1546))) in 
  let x3_1549 : fp_t :=
    (nat_mod_exp (xovery_1548) (@repr WORDSIZE32 2)) -% ((nat_mod_two ) *% (
        x1_1545)) in 
  let y3_1550 : fp_t :=
    ((xovery_1548) *% ((x1_1545) -% (x3_1549))) -% (y1_1546) in 
  (x3_1549, y3_1550, false).

Definition g1double (p_1551 : g1_t) : g1_t :=
  let '(x1_1552, y1_1553, inf1_1554) :=
    p_1551 in 
  (if (((y1_1553) !=.? (nat_mod_zero )) && (negb (inf1_1554))):bool then (
      g1double_a (p_1551)) else ((nat_mod_zero , nat_mod_zero , true))).

Definition g1add (p_1555 : g1_t) (q_1556 : g1_t) : g1_t :=
  let '(x1_1557, y1_1558, inf1_1559) :=
    p_1555 in 
  let '(x2_1560, y2_1561, inf2_1562) :=
    q_1556 in 
  (if (inf1_1559):bool then (q_1556) else ((if (inf2_1562):bool then (
          p_1555) else ((if ((p_1555) =.? (q_1556)):bool then (g1double (
                p_1555)) else ((if (negb (((x1_1557) =.? (x2_1560)) && ((
                        y1_1558) =.? ((nat_mod_zero ) -% (
                          y2_1561))))):bool then (g1add_a (p_1555) (
                    q_1556)) else ((nat_mod_zero , nat_mod_zero , true))))))))).

Definition g1mul (m_1563 : scalar_t) (p_1564 : g1_t) : g1_t :=
  let t_1565 : (fp_t '× fp_t '× bool) :=
    (nat_mod_zero , nat_mod_zero , true) in 
  let t_1565 :=
    foldi (usize 0) (usize 256) (fun i_1566 t_1565 =>
      let t_1565 :=
        g1double (t_1565) in 
      let '(t_1565) :=
        if nat_mod_bit (m_1563) ((usize 255) - (i_1566)):bool then (
          let t_1565 :=
            g1add (t_1565) (p_1564) in 
          (t_1565)) else ((t_1565)) in 
      (t_1565))
    t_1565 in 
  t_1565.

Definition g1neg (p_1567 : g1_t) : g1_t :=
  let '(x_1568, y_1569, inf_1570) :=
    p_1567 in 
  (x_1568, (nat_mod_zero ) -% (y_1569), inf_1570).

Definition g2add_a (p_1571 : g2_t) (q_1572 : g2_t) : g2_t :=
  let '(x1_1573, y1_1574, _) :=
    p_1571 in 
  let '(x2_1575, y2_1576, _) :=
    q_1572 in 
  let x_diff_1577 : (fp_t '× fp_t) :=
    fp2sub (x2_1575) (x1_1573) in 
  let y_diff_1578 : (fp_t '× fp_t) :=
    fp2sub (y2_1576) (y1_1574) in 
  let xovery_1579 : (fp_t '× fp_t) :=
    fp2mul (y_diff_1578) (fp2inv (x_diff_1577)) in 
  let t1_1580 : (fp_t '× fp_t) :=
    fp2mul (xovery_1579) (xovery_1579) in 
  let t2_1581 : (fp_t '× fp_t) :=
    fp2sub (t1_1580) (x1_1573) in 
  let x3_1582 : (fp_t '× fp_t) :=
    fp2sub (t2_1581) (x2_1575) in 
  let t1_1583 : (fp_t '× fp_t) :=
    fp2sub (x1_1573) (x3_1582) in 
  let t2_1584 : (fp_t '× fp_t) :=
    fp2mul (xovery_1579) (t1_1583) in 
  let y3_1585 : (fp_t '× fp_t) :=
    fp2sub (t2_1584) (y1_1574) in 
  (x3_1582, y3_1585, false).

Definition g2double_a (p_1586 : g2_t) : g2_t :=
  let '(x1_1587, y1_1588, _) :=
    p_1586 in 
  let x12_1589 : (fp_t '× fp_t) :=
    fp2mul (x1_1587) (x1_1587) in 
  let t1_1590 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (x12_1589) in 
  let t2_1591 : (fp_t '× fp_t) :=
    fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (y1_1588)) in 
  let xovery_1592 : (fp_t '× fp_t) :=
    fp2mul (t1_1590) (t2_1591) in 
  let t1_1593 : (fp_t '× fp_t) :=
    fp2mul (xovery_1592) (xovery_1592) in 
  let t2_1594 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_two )) (x1_1587) in 
  let x3_1595 : (fp_t '× fp_t) :=
    fp2sub (t1_1593) (t2_1594) in 
  let t1_1596 : (fp_t '× fp_t) :=
    fp2sub (x1_1587) (x3_1595) in 
  let t2_1597 : (fp_t '× fp_t) :=
    fp2mul (xovery_1592) (t1_1596) in 
  let y3_1598 : (fp_t '× fp_t) :=
    fp2sub (t2_1597) (y1_1588) in 
  (x3_1595, y3_1598, false).

Definition g2double (p_1599 : g2_t) : g2_t :=
  let '(x1_1600, y1_1601, inf1_1602) :=
    p_1599 in 
  (if (((y1_1601) !=.? (fp2zero )) && (negb (inf1_1602))):bool then (
      g2double_a (p_1599)) else ((fp2zero , fp2zero , true))).

Definition g2add (p_1603 : g2_t) (q_1604 : g2_t) : g2_t :=
  let '(x1_1605, y1_1606, inf1_1607) :=
    p_1603 in 
  let '(x2_1608, y2_1609, inf2_1610) :=
    q_1604 in 
  (if (inf1_1607):bool then (q_1604) else ((if (inf2_1610):bool then (
          p_1603) else ((if ((p_1603) =.? (q_1604)):bool then (g2double (
                p_1603)) else ((if (negb (((x1_1605) =.? (x2_1608)) && ((
                        y1_1606) =.? (fp2neg (y2_1609))))):bool then (g2add_a (
                    p_1603) (q_1604)) else ((fp2zero , fp2zero , true))))))))).

Definition g2mul (m_1611 : scalar_t) (p_1612 : g2_t) : g2_t :=
  let t_1613 : (fp2_t '× fp2_t '× bool) :=
    (fp2zero , fp2zero , true) in 
  let t_1613 :=
    foldi (usize 0) (usize 256) (fun i_1614 t_1613 =>
      let t_1613 :=
        g2double (t_1613) in 
      let '(t_1613) :=
        if nat_mod_bit (m_1611) ((usize 255) - (i_1614)):bool then (
          let t_1613 :=
            g2add (t_1613) (p_1612) in 
          (t_1613)) else ((t_1613)) in 
      (t_1613))
    t_1613 in 
  t_1613.

Definition g2neg (p_1615 : g2_t) : g2_t :=
  let '(x_1616, y_1617, inf_1618) :=
    p_1615 in 
  (x_1616, fp2neg (y_1617), inf_1618).

Definition twist (p_1619 : g1_t) : (fp12_t '× fp12_t) :=
  let '(p0_1620, p1_1621, _) :=
    p_1619 in 
  let x_1622 : ((fp2_t '× fp2_t '× fp2_t) '× fp6_t) :=
    ((fp2zero , fp2fromfp (p0_1620), fp2zero ), fp6zero ) in 
  let y_1623 : (fp6_t '× (fp2_t '× fp2_t '× fp2_t)) :=
    (fp6zero , (fp2zero , fp2fromfp (p1_1621), fp2zero )) in 
  (x_1622, y_1623).

Definition line_double_p (r_1624 : g2_t) (p_1625 : g1_t) : fp12_t :=
  let '(r0_1626, r1_1627, _) :=
    r_1624 in 
  let a_1628 : (fp_t '× fp_t) :=
    fp2mul (fp2fromfp (nat_mod_from_literal (
          0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab) (
          @repr WORDSIZE128 3) : fp_t)) (fp2mul (r0_1626) (r0_1626)) in 
  let a_1629 : (fp_t '× fp_t) :=
    fp2mul (a_1628) (fp2inv (fp2mul (fp2fromfp (nat_mod_two )) (r1_1627))) in 
  let b_1630 : (fp_t '× fp_t) :=
    fp2sub (r1_1627) (fp2mul (a_1629) (r0_1626)) in 
  let a_1631 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1629)) in 
  let b_1632 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1630)) in 
  let '(x_1633, y_1634) :=
    twist (p_1625) in 
  fp12neg (fp12sub (fp12sub (y_1634) (fp12mul (a_1631) (x_1633))) (b_1632)).

Definition line_add_p
  (r_1635 : g2_t)
  (q_1636 : g2_t)
  (p_1637 : g1_t)
  : fp12_t :=
  let '(r0_1638, r1_1639, _) :=
    r_1635 in 
  let '(q0_1640, q1_1641, _) :=
    q_1636 in 
  let a_1642 : (fp_t '× fp_t) :=
    fp2mul (fp2sub (q1_1641) (r1_1639)) (fp2inv (fp2sub (q0_1640) (
          r0_1638))) in 
  let b_1643 : (fp_t '× fp_t) :=
    fp2sub (r1_1639) (fp2mul (a_1642) (r0_1638)) in 
  let a_1644 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (a_1642)) in 
  let b_1645 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (b_1643)) in 
  let '(x_1646, y_1647) :=
    twist (p_1637) in 
  fp12neg (fp12sub (fp12sub (y_1647) (fp12mul (a_1644) (x_1646))) (b_1645)).

Definition frobenius (f_1648 : fp12_t) : fp12_t :=
  let '((g0_1649, g1_1650, g2_1651), (h0_1652, h1_1653, h2_1654)) :=
    f_1648 in 
  let t1_1655 : (fp_t '× fp_t) :=
    fp2conjugate (g0_1649) in 
  let t2_1656 : (fp_t '× fp_t) :=
    fp2conjugate (h0_1652) in 
  let t3_1657 : (fp_t '× fp_t) :=
    fp2conjugate (g1_1650) in 
  let t4_1658 : (fp_t '× fp_t) :=
    fp2conjugate (h1_1653) in 
  let t5_1659 : (fp_t '× fp_t) :=
    fp2conjugate (g2_1651) in 
  let t6_1660 : (fp_t '× fp_t) :=
    fp2conjugate (h2_1654) in 
  let c1_1661 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 10162220747404304312) : int64;
          secret (@repr WORDSIZE64 17761815663483519293) : int64;
          secret (@repr WORDSIZE64 8873291758750579140) : int64;
          secret (@repr WORDSIZE64 1141103941765652303) : int64;
          secret (@repr WORDSIZE64 13993175198059990303) : int64;
          secret (@repr WORDSIZE64 1802798568193066599) : int64
        ] in  l) in 
  let c1_1662 : seq uint8 :=
    array_to_le_bytes (c1_1661) in 
  let c1_1663 : fp_t :=
    nat_mod_from_byte_seq_le (c1_1662) : fp_t in 
  let c2_1664 : array_fp_t :=
    array_from_list uint64 (let l :=
        [
          secret (@repr WORDSIZE64 3240210268673559283) : int64;
          secret (@repr WORDSIZE64 2895069921743240898) : int64;
          secret (@repr WORDSIZE64 17009126888523054175) : int64;
          secret (@repr WORDSIZE64 6098234018649060207) : int64;
          secret (@repr WORDSIZE64 9865672654120263608) : int64;
          secret (@repr WORDSIZE64 71000049454473266) : int64
        ] in  l) in 
  let c2_1665 : seq uint8 :=
    array_to_le_bytes (c2_1664) in 
  let c2_1666 : fp_t :=
    nat_mod_from_byte_seq_le (c2_1665) : fp_t in 
  let gamma11_1667 : (fp_t '× fp_t) :=
    (c1_1663, c2_1666) in 
  let gamma12_1668 : (fp_t '× fp_t) :=
    fp2mul (gamma11_1667) (gamma11_1667) in 
  let gamma13_1669 : (fp_t '× fp_t) :=
    fp2mul (gamma12_1668) (gamma11_1667) in 
  let gamma14_1670 : (fp_t '× fp_t) :=
    fp2mul (gamma13_1669) (gamma11_1667) in 
  let gamma15_1671 : (fp_t '× fp_t) :=
    fp2mul (gamma14_1670) (gamma11_1667) in 
  let t2_1672 : (fp_t '× fp_t) :=
    fp2mul (t2_1656) (gamma11_1667) in 
  let t3_1673 : (fp_t '× fp_t) :=
    fp2mul (t3_1657) (gamma12_1668) in 
  let t4_1674 : (fp_t '× fp_t) :=
    fp2mul (t4_1658) (gamma13_1669) in 
  let t5_1675 : (fp_t '× fp_t) :=
    fp2mul (t5_1659) (gamma14_1670) in 
  let t6_1676 : (fp_t '× fp_t) :=
    fp2mul (t6_1660) (gamma15_1671) in 
  ((t1_1655, t3_1673, t5_1675), (t2_1672, t4_1674, t6_1676)).

Definition final_exponentiation (f_1677 : fp12_t) : fp12_t :=
  let fp6_1678 : (fp6_t '× fp6_t) :=
    fp12conjugate (f_1677) in 
  let finv_1679 : (fp6_t '× fp6_t) :=
    fp12inv (f_1677) in 
  let fp6_1_1680 : (fp6_t '× fp6_t) :=
    fp12mul (fp6_1678) (finv_1679) in 
  let fp8_1681 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (fp6_1_1680)) in 
  let f_1682 : (fp6_t '× fp6_t) :=
    fp12mul (fp8_1681) (fp6_1_1680) in 
  let u_1683 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let u_half_1684 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 7566188111470821376) : scalar_t in 
  let t0_1685 : (fp6_t '× fp6_t) :=
    fp12mul (f_1682) (f_1682) in 
  let t1_1686 : (fp6_t '× fp6_t) :=
    fp12exp (t0_1685) (u_1683) in 
  let t1_1687 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1686) in 
  let t2_1688 : (fp6_t '× fp6_t) :=
    fp12exp (t1_1687) (u_half_1684) in 
  let t2_1689 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1688) in 
  let t3_1690 : (fp6_t '× fp6_t) :=
    fp12conjugate (f_1682) in 
  let t1_1691 : (fp6_t '× fp6_t) :=
    fp12mul (t3_1690) (t1_1687) in 
  let t1_1692 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1691) in 
  let t1_1693 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1692) (t2_1689) in 
  let t2_1694 : (fp6_t '× fp6_t) :=
    fp12exp (t1_1693) (u_1683) in 
  let t2_1695 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1694) in 
  let t3_1696 : (fp6_t '× fp6_t) :=
    fp12exp (t2_1695) (u_1683) in 
  let t3_1697 : (fp6_t '× fp6_t) :=
    fp12conjugate (t3_1696) in 
  let t1_1698 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1693) in 
  let t3_1699 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1698) (t3_1697) in 
  let t1_1700 : (fp6_t '× fp6_t) :=
    fp12conjugate (t1_1698) in 
  let t1_1701 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (frobenius (t1_1700))) in 
  let t2_1702 : (fp6_t '× fp6_t) :=
    frobenius (frobenius (t2_1695)) in 
  let t1_1703 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1701) (t2_1702) in 
  let t2_1704 : (fp6_t '× fp6_t) :=
    fp12exp (t3_1699) (u_1683) in 
  let t2_1705 : (fp6_t '× fp6_t) :=
    fp12conjugate (t2_1704) in 
  let t2_1706 : (fp6_t '× fp6_t) :=
    fp12mul (t2_1705) (t0_1685) in 
  let t2_1707 : (fp6_t '× fp6_t) :=
    fp12mul (t2_1706) (f_1682) in 
  let t1_1708 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1703) (t2_1707) in 
  let t2_1709 : (fp6_t '× fp6_t) :=
    frobenius (t3_1699) in 
  let t1_1710 : (fp6_t '× fp6_t) :=
    fp12mul (t1_1708) (t2_1709) in 
  t1_1710.

Definition pairing (p_1711 : g1_t) (q_1712 : g2_t) : fp12_t :=
  let t_1713 : scalar_t :=
    nat_mod_from_literal (
      0x8000000000000000000000000000000000000000000000000000000000000000) (
      @repr WORDSIZE128 15132376222941642752) : scalar_t in 
  let r_1714 : (fp2_t '× fp2_t '× bool) :=
    q_1712 in 
  let f_1715 : (fp6_t '× fp6_t) :=
    fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one ))) in 
  let '(r_1714, f_1715) :=
    foldi (usize 1) (usize 64) (fun i_1716 '(r_1714, f_1715) =>
      let lrr_1717 : (fp6_t '× fp6_t) :=
        line_double_p (r_1714) (p_1711) in 
      let r_1714 :=
        g2double (r_1714) in 
      let f_1715 :=
        fp12mul (fp12mul (f_1715) (f_1715)) (lrr_1717) in 
      let '(r_1714, f_1715) :=
        if nat_mod_bit (t_1713) (((usize 64) - (i_1716)) - (
            usize 1)):bool then (let lrq_1718 : (fp6_t '× fp6_t) :=
            line_add_p (r_1714) (q_1712) (p_1711) in 
          let r_1714 :=
            g2add (r_1714) (q_1712) in 
          let f_1715 :=
            fp12mul (f_1715) (lrq_1718) in 
          (r_1714, f_1715)) else ((r_1714, f_1715)) in 
      (r_1714, f_1715))
    (r_1714, f_1715) in 
  final_exponentiation (fp12conjugate (f_1715)).

Definition test_fp2_prop_add_neg (a_1719 : fp2_t) : bool :=
  let b_1720 : (fp_t '× fp_t) :=
    fp2neg (a_1719) in 
  (fp2fromfp (nat_mod_zero )) =.? (fp2add (a_1719) (b_1720)).
(*QuickChick (
  forAll g_fp2_t (fun a_1719 : fp2_t =>test_fp2_prop_add_neg a_1719)).*)


Definition test_fp2_prop_mul_inv (a_1721 : fp2_t) : bool :=
  let b_1722 : (fp_t '× fp_t) :=
    fp2inv (a_1721) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul (a_1721) (b_1722)).
(*QuickChick (
  forAll g_fp2_t (fun a_1721 : fp2_t =>test_fp2_prop_mul_inv a_1721)).*)


Definition test_extraction_issue  : bool :=
  let b_1723 : (fp_t '× fp_t) :=
    fp2inv ((nat_mod_one , nat_mod_one )) in 
  (fp2fromfp (nat_mod_one )) =.? (fp2mul ((nat_mod_one , nat_mod_one )) (
      b_1723)).
(*QuickChick (test_extraction_issue).*)


Definition test_fp6_prop_mul_inv (a_1724 : fp6_t) : bool :=
  let b_1725 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6inv (a_1724) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_one ))) =.? (fp6mul (a_1724) (b_1725)).
(*QuickChick (
  forAll g_fp6_t (fun a_1724 : fp6_t =>test_fp6_prop_mul_inv a_1724)).*)


Definition test_fp6_prop_add_neg (a_1726 : fp6_t) : bool :=
  let b_1727 : (fp2_t '× fp2_t '× fp2_t) :=
    fp6neg (a_1726) in 
  (fp6fromfp2 (fp2fromfp (nat_mod_zero ))) =.? (fp6add (a_1726) (b_1727)).
(*QuickChick (
  forAll g_fp6_t (fun a_1726 : fp6_t =>test_fp6_prop_add_neg a_1726)).*)


Definition test_fp12_prop_add_neg (a_1728 : fp12_t) : bool :=
  let b_1729 : (fp6_t '× fp6_t) :=
    fp12neg (a_1728) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_zero )))) =.? (fp12add (a_1728) (
      b_1729)).
(*QuickChick (
  forAll g_fp12_t (fun a_1728 : fp12_t =>test_fp12_prop_add_neg a_1728)).*)


Definition test_fp12_prop_mul_inv (a_1730 : fp12_t) : bool :=
  let b_1731 : (fp6_t '× fp6_t) :=
    fp12inv (a_1730) in 
  (fp12fromfp6 (fp6fromfp2 (fp2fromfp (nat_mod_one )))) =.? (fp12mul (a_1730) (
      b_1731)).
(*QuickChick (
  forAll g_fp12_t (fun a_1730 : fp12_t =>test_fp12_prop_mul_inv a_1730)).*)


