(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.

Definition scalar_from_hash (h_1635 : sha512_digest_t) : scalar_t :=
  let s_1636 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1635)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1636)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1637 : secret_key_t) (msg_1638 : byte_seq) : signature_t :=
  let '(a_1639, prefix_1640) :=
    secret_expand (sk_1637) in 
  let a_1641 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1639)) : scalar_t in 
  let b_1642 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1643 : compressed_ed_point_t :=
    compress (point_mul (a_1641) (b_1642)) in 
  let r_1644 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1640) (msg_1638))) in 
  let r_p_1645 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_mul (r_1644) (b_1642) in 
  let r_s_1646 : compressed_ed_point_t :=
    compress (r_p_1645) in 
  let h_1647 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1646) (
            array_to_seq (a_p_1643))) (msg_1638))) in 
  let s_1648 : scalar_t :=
    (r_1644) +% ((h_1647) *% (a_1641)) in 
  let s_bytes_1649 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1648)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default) (64)) (usize 0) (
      array_to_seq (r_s_1646))) (usize 32) (s_bytes_1649).

Definition zcash_verify
  (pk_1650 : public_key_t)
  (signature_1651 : signature_t)
  (msg_1652 : byte_seq)
  : verify_result_t :=
  let b_1653 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  bind (option_ok_or (decompress_non_canonical (pk_1650)) (InvalidPublickey)) (
    fun a_1654 => let r_bytes_1655 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1651)) (
        usize 0) (usize 32) in 
    let s_bytes_1656 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1651)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1656)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1655)) (InvalidR)) (
      fun r_1657 => let s_1658 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1656)) : scalar_t in 
      let k_1659 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1655) (
                pk_1650)) (msg_1652))) in 
      let sb_1660 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1658) (b_1653)) in 
      let rc_1661 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1657) in 
      let ka_1662 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1659) (a_1654)) in 
      (if (point_eq (sb_1660) (point_add (rc_1661) (ka_1662))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactored_verify
  (pk_1663 : public_key_t)
  (signature_1664 : signature_t)
  (msg_1665 : byte_seq)
  : verify_result_t :=
  let b_1666 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1663)) (InvalidPublickey)) (fun a_1667 =>
    let r_bytes_1668 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1664)) (
        usize 0) (usize 32) in 
    let s_bytes_1669 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1664)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1669)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1668)) (InvalidR)) (fun r_1670 =>
      let s_1671 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1669)) : scalar_t in 
      let k_1672 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1668) (
                pk_1663)) (msg_1665))) in 
      let sb_1673 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1671) (b_1666)) in 
      let rc_1674 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1670) in 
      let ka_1675 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1672) (a_1667)) in 
      (if (point_eq (sb_1673) (point_add (rc_1674) (ka_1675))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactorless_verify
  (pk_1676 : public_key_t)
  (signature_1677 : signature_t)
  (msg_1678 : byte_seq)
  : verify_result_t :=
  let b_1679 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1676)) (InvalidPublickey)) (fun a_1680 =>
    let r_bytes_1681 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1677)) (
        usize 0) (usize 32) in 
    let s_bytes_1682 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1677)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1682)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1681)) (InvalidR)) (fun r_1683 =>
      let s_1684 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1682)) : scalar_t in 
      let k_1685 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1681) (
                pk_1676)) (msg_1678))) in 
      let sb_1686 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul (s_1684) (b_1679) in 
      let ka_1687 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul (k_1685) (a_1680) in 
      (if (point_eq (sb_1686) (point_add (r_1683) (ka_1687))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition is_identity (p_1688 : ed_point_t) : bool :=
  point_eq (p_1688) (point_identity ).

Definition alg2_verify
  (pk_1689 : public_key_t)
  (signature_1690 : signature_t)
  (msg_1691 : byte_seq)
  : verify_result_t :=
  let b_1692 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_1689)) (InvalidPublickey)) (fun a_1693 =>
    ifbnd is_identity (point_mul_by_cofactor (a_1693)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_1694 : compressed_ed_point_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1690)) (
        usize 0) (usize 32) in 
    let s_bytes_1695 : serialized_scalar_t :=
      array_from_slice (default) (32) (array_to_seq (signature_1690)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1695)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_1694)) (InvalidR)) (fun r_1696 =>
      let s_1697 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1695)) : scalar_t in 
      let k_1698 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1694) (
                pk_1689)) (msg_1691))) in 
      let sb_1699 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_1697) (b_1692)) in 
      let rc_1700 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_1696) in 
      let ka_1701 : (
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t ×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_1698) (a_1693)) in 
      (if (point_eq (sb_1699) (point_add (rc_1700) (ka_1701))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t × byte_seq × signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_1702 : seq batch_entry_t)
  (entropy_1703 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1703)) <.? ((usize 16) * (seq_len (
        entries_1702))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1704 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1705 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1706 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1702)) for (
      s_sum_1704,
      r_sum_1705,
      a_sum_1706
    ) >> (fun i_1707 '(s_sum_1704, r_sum_1705, a_sum_1706) =>
    let 'BatchEntry ((pk_1708, msg_1709, signature_1710)) :=
      (seq_index (entries_1702) (i_1707)) in 
    bind (option_ok_or (decompress_non_canonical (pk_1708)) (
        InvalidPublickey)) (fun a_1711 =>
      let r_bytes_1712 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1710)) (
          usize 0) (usize 32) in 
      let s_bytes_1713 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1710)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1713)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_1712)) (InvalidR)) (
        fun r_1714 => let s_1715 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1713)) : scalar_t in 
        let c_1716 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1712) (
                  array_to_seq (pk_1708))) (msg_1709))) in 
        let z_1717 : seq uint8 :=
          seq_slice (entropy_1703) ((usize 16) * (i_1707)) (usize 16) in 
        let z_1718 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1717) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1704 :=
          (s_sum_1704) +% ((s_1715) *% (z_1718)) in 
        let r_sum_1705 :=
          point_add (r_sum_1705) (point_mul (z_1718) (r_1714)) in 
        let a_sum_1706 :=
          point_add (a_sum_1706) (point_mul ((z_1718) *% (c_1716)) (a_1711)) in 
        Ok ((s_sum_1704, r_sum_1705, a_sum_1706))))))) (fun '(
      s_sum_1704,
      r_sum_1705,
      a_sum_1706
    ) => let b_1719 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1720 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1704) (b_1719) in 
    let check_1721 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1720)) (point_add (
            r_sum_1705) (a_sum_1706))) in 
    (if (is_identity (check_1721)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactored_batch_verify
  (entries_1722 : seq batch_entry_t)
  (entropy_1723 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1723)) <.? ((usize 16) * (seq_len (
        entries_1722))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1724 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1725 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1726 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1722)) for (
      s_sum_1724,
      r_sum_1725,
      a_sum_1726
    ) >> (fun i_1727 '(s_sum_1724, r_sum_1725, a_sum_1726) =>
    let 'BatchEntry ((pk_1728, msg_1729, signature_1730)) :=
      (seq_index (entries_1722) (i_1727)) in 
    bind (option_ok_or (decompress (pk_1728)) (InvalidPublickey)) (fun a_1731 =>
      let r_bytes_1732 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1730)) (
          usize 0) (usize 32) in 
      let s_bytes_1733 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1730)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1733)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1732)) (InvalidR)) (fun r_1734 =>
        let s_1735 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1733)) : scalar_t in 
        let c_1736 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1732) (
                  array_to_seq (pk_1728))) (msg_1729))) in 
        let z_1737 : seq uint8 :=
          seq_slice (entropy_1723) ((usize 16) * (i_1727)) (usize 16) in 
        let z_1738 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1737) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1724 :=
          (s_sum_1724) +% ((s_1735) *% (z_1738)) in 
        let r_sum_1725 :=
          point_add (r_sum_1725) (point_mul (z_1738) (r_1734)) in 
        let a_sum_1726 :=
          point_add (a_sum_1726) (point_mul ((z_1738) *% (c_1736)) (a_1731)) in 
        Ok ((s_sum_1724, r_sum_1725, a_sum_1726))))))) (fun '(
      s_sum_1724,
      r_sum_1725,
      a_sum_1726
    ) => let b_1739 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1740 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1724) (b_1739) in 
    let check_1741 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1740)) (point_add (
            r_sum_1725) (a_sum_1726))) in 
    (if (is_identity (check_1741)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactorless_batch_verify
  (entries_1742 : seq batch_entry_t)
  (entropy_1743 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1743)) <.? ((usize 16) * (seq_len (
        entries_1742))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1744 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1745 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1746 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1742)) for (
      s_sum_1744,
      r_sum_1745,
      a_sum_1746
    ) >> (fun i_1747 '(s_sum_1744, r_sum_1745, a_sum_1746) =>
    let 'BatchEntry ((pk_1748, msg_1749, signature_1750)) :=
      (seq_index (entries_1742) (i_1747)) in 
    bind (option_ok_or (decompress (pk_1748)) (InvalidPublickey)) (fun a_1751 =>
      let r_bytes_1752 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1750)) (
          usize 0) (usize 32) in 
      let s_bytes_1753 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1750)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1753)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1752)) (InvalidR)) (fun r_1754 =>
        let s_1755 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1753)) : scalar_t in 
        let c_1756 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1752) (
                  array_to_seq (pk_1748))) (msg_1749))) in 
        let z_1757 : seq uint8 :=
          seq_slice (entropy_1743) ((usize 16) * (i_1747)) (usize 16) in 
        let z_1758 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1757) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1744 :=
          (s_sum_1744) +% ((s_1755) *% (z_1758)) in 
        let r_sum_1745 :=
          point_add (r_sum_1745) (point_mul (z_1758) (r_1754)) in 
        let a_sum_1746 :=
          point_add (a_sum_1746) (point_mul ((z_1758) *% (c_1756)) (a_1751)) in 
        Ok ((s_sum_1744, r_sum_1745, a_sum_1746))))))) (fun '(
      s_sum_1744,
      r_sum_1745,
      a_sum_1746
    ) => let b_1759 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1760 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1744) (b_1759) in 
    let check_1761 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_add (point_neg (sb_1760)) (point_add (r_sum_1745) (a_sum_1746)) in 
    (if (is_identity (check_1761)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition alg3_batch_verify
  (entries_1762 : seq batch_entry_t)
  (entropy_1763 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_1763)) <.? ((usize 16) * (seq_len (
        entries_1762))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ => Ok (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_1764 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_1765 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_1766 : (
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t ×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_1762)) for (
      s_sum_1764,
      r_sum_1765,
      a_sum_1766
    ) >> (fun i_1767 '(s_sum_1764, r_sum_1765, a_sum_1766) =>
    let 'BatchEntry ((pk_1768, msg_1769, signature_1770)) :=
      (seq_index (entries_1762) (i_1767)) in 
    bind (option_ok_or (decompress (pk_1768)) (InvalidPublickey)) (fun a_1771 =>
      ifbnd is_identity (point_mul_by_cofactor (a_1771)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_1772 : compressed_ed_point_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1770)) (
          usize 0) (usize 32) in 
      let s_bytes_1773 : serialized_scalar_t :=
        array_from_slice (default) (32) (array_to_seq (signature_1770)) (
          usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_1773)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => Ok (tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_1772)) (InvalidR)) (fun r_1774 =>
        let s_1775 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1773)) : scalar_t in 
        let c_1776 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1772) (
                  array_to_seq (pk_1768))) (msg_1769))) in 
        let z_1777 : seq uint8 :=
          seq_slice (entropy_1763) ((usize 16) * (i_1767)) (usize 16) in 
        let z_1778 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_1777) (seq_new_ (default) (
                usize 16))) : scalar_t in 
        let s_sum_1764 :=
          (s_sum_1764) +% ((s_1775) *% (z_1778)) in 
        let r_sum_1765 :=
          point_add (r_sum_1765) (point_mul (z_1778) (r_1774)) in 
        let a_sum_1766 :=
          point_add (a_sum_1766) (point_mul ((z_1778) *% (c_1776)) (a_1771)) in 
        Ok ((s_sum_1764, r_sum_1765, a_sum_1766)))))))) (fun '(
      s_sum_1764,
      r_sum_1765,
      a_sum_1766
    ) => let b_1779 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_1780 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_1764) (b_1779) in 
    let check_1781 : (
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t ×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_1780)) (point_add (
            r_sum_1765) (a_sum_1766))) in 
    (if (is_identity (check_1781)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

