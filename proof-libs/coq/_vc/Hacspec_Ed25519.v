(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha512.

Require Import Hacspec_Edwards25519.

Definition scalar_from_hash (h_1978 : sha512_digest_t) : scalar_t :=
  let s_1979 : big_scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (h_1978)) : big_scalar_t in 
  nat_mod_from_byte_seq_le (seq_slice (nat_mod_to_byte_seq_le (s_1979)) (
      usize 0) (usize 32)) : scalar_t.

Definition sign (sk_1980 : secret_key_t) (msg_1981 : byte_seq) : signature_t :=
  let '(a_1982, prefix_1983) :=
    secret_expand (sk_1980) in 
  let a_1984 : scalar_t :=
    nat_mod_from_byte_seq_le (array_to_seq (a_1982)) : scalar_t in 
  let b_1985 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  let a_p_1986 : compressed_ed_point_t :=
    compress (point_mul (a_1984) (b_1985)) in 
  let r_1987 : scalar_t :=
    scalar_from_hash (sha512 (array_concat (prefix_1983) (msg_1981))) in 
  let r_p_1988 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_mul (r_1987) (b_1985) in 
  let r_s_1989 : compressed_ed_point_t :=
    compress (r_p_1988) in 
  let h_1990 : scalar_t :=
    scalar_from_hash (sha512 (seq_concat (array_concat (r_s_1989) (
            array_to_seq (a_p_1986))) (msg_1981))) in 
  let s_1991 : scalar_t :=
    (r_1987) +% ((h_1990) *% (a_1984)) in 
  let s_bytes_1992 : seq uint8 :=
    seq_slice (nat_mod_to_byte_seq_le (s_1991)) (usize 0) (usize 32) in 
  array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
      array_to_seq (r_s_1989))) (usize 32) (s_bytes_1992).

Definition zcash_verify
  (pk_1993 : public_key_t)
  (signature_1994 : signature_t)
  (msg_1995 : byte_seq)
  : verify_result_t :=
  let b_1996 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress_non_canonical (base_v)) in 
  bind (option_ok_or (decompress_non_canonical (pk_1993)) (InvalidPublickey)) (
    fun a_1997 => let r_bytes_1998 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1994)) (
        usize 0) (usize 32) in 
    let s_bytes_1999 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_1994)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_1999)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress_non_canonical (r_bytes_1998)) (InvalidR)) (
      fun r_2000 => let s_2001 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_1999)) : scalar_t in 
      let k_2002 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_1998) (
                pk_1993)) (msg_1995))) in 
      let sb_2003 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2001) (b_1996)) in 
      let rc_2004 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2000) in 
      let ka_2005 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2002) (a_1997)) in 
      (if (point_eq (sb_2003) (point_add (rc_2004) (ka_2005))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactored_verify
  (pk_2006 : public_key_t)
  (signature_2007 : signature_t)
  (msg_2008 : byte_seq)
  : verify_result_t :=
  let b_2009 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2006)) (InvalidPublickey)) (fun a_2010 =>
    let r_bytes_2011 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2007)) (
        usize 0) (usize 32) in 
    let s_bytes_2012 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2007)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2012)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2011)) (InvalidR)) (fun r_2013 =>
      let s_2014 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2012)) : scalar_t in 
      let k_2015 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2011) (
                pk_2006)) (msg_2008))) in 
      let sb_2016 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2014) (b_2009)) in 
      let rc_2017 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2013) in 
      let ka_2018 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2015) (a_2010)) in 
      (if (point_eq (sb_2016) (point_add (rc_2017) (ka_2018))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition ietf_cofactorless_verify
  (pk_2019 : public_key_t)
  (signature_2020 : signature_t)
  (msg_2021 : byte_seq)
  : verify_result_t :=
  let b_2022 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2019)) (InvalidPublickey)) (fun a_2023 =>
    let r_bytes_2024 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2020)) (
        usize 0) (usize 32) in 
    let s_bytes_2025 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2020)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2025)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2024)) (InvalidR)) (fun r_2026 =>
      let s_2027 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2025)) : scalar_t in 
      let k_2028 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2024) (
                pk_2019)) (msg_2021))) in 
      let sb_2029 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (s_2027) (b_2022) in 
      let ka_2030 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul (k_2028) (a_2023) in 
      (if (point_eq (sb_2029) (point_add (r_2026) (ka_2030))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature)))))).

Definition is_identity (p_2031 : ed_point_t) : bool :=
  point_eq (p_2031) (point_identity ).

Definition alg2_verify
  (pk_2032 : public_key_t)
  (signature_2033 : signature_t)
  (msg_2034 : byte_seq)
  : verify_result_t :=
  let b_2035 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    option_unwrap (decompress (base_v)) in 
  bind (option_ok_or (decompress (pk_2032)) (InvalidPublickey)) (fun a_2036 =>
    ifbnd is_identity (point_mul_by_cofactor (a_2036)) : bool
    thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_bytes_2037 : compressed_ed_point_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2033)) (
        usize 0) (usize 32) in 
    let s_bytes_2038 : serialized_scalar_t :=
      array_from_slice (default : uint8) (32) (array_to_seq (signature_2033)) (
        usize 32) (usize 32) in 
    ifbnd negb (check_canonical_scalar (s_bytes_2038)) : bool
    thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
          tt)))
    else (tt) >> (fun 'tt =>
    bind (option_ok_or (decompress (r_bytes_2037)) (InvalidR)) (fun r_2039 =>
      let s_2040 : scalar_t :=
        nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2038)) : scalar_t in 
      let k_2041 : scalar_t :=
        scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2037) (
                pk_2032)) (msg_2034))) in 
      let sb_2042 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (s_2040) (b_2035)) in 
      let rc_2043 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (r_2039) in 
      let ka_2044 : (
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t '×
          ed25519_field_element_t
        ) :=
        point_mul_by_cofactor (point_mul (k_2041) (a_2036)) in 
      (if (point_eq (sb_2042) (point_add (rc_2043) (ka_2044))):bool then (
          @Ok unit error_t (tt)) else (@Err unit error_t (
            InvalidSignature))))))).

Inductive batch_entry_t :=
| BatchEntry : (public_key_t '× byte_seq '× signature_t) -> batch_entry_t.

Definition zcash_batch_verify
  (entries_2045 : seq batch_entry_t)
  (entropy_2046 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_2046)) <.? ((usize 16) * (seq_len (
        entries_2045))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2047 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2048 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2049 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2045)) for (
      s_sum_2047,
      r_sum_2048,
      a_sum_2049
    ) >> (fun i_2050 '(s_sum_2047, r_sum_2048, a_sum_2049) =>
    let 'BatchEntry ((pk_2051, msg_2052, signature_2053)) :=
      (seq_index (entries_2045) (i_2050)) in 
    bind (option_ok_or (decompress_non_canonical (pk_2051)) (
        InvalidPublickey)) (fun a_2054 =>
      let r_bytes_2055 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2053)) (usize 0) (usize 32) in 
      let s_bytes_2056 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2053)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2056)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress_non_canonical (r_bytes_2055)) (InvalidR)) (
        fun r_2057 => let s_2058 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2056)) : scalar_t in 
        let c_2059 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2055) (
                  array_to_seq (pk_2051))) (msg_2052))) in 
        let z_2060 : seq uint8 :=
          seq_slice (entropy_2046) ((usize 16) * (i_2050)) (usize 16) in 
        let z_2061 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2060) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2047 :=
          (s_sum_2047) +% ((s_2058) *% (z_2061)) in 
        let r_sum_2048 :=
          point_add (r_sum_2048) (point_mul (z_2061) (r_2057)) in 
        let a_sum_2049 :=
          point_add (a_sum_2049) (point_mul ((z_2061) *% (c_2059)) (a_2054)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2047, r_sum_2048, a_sum_2049))))))) (fun '(
      s_sum_2047,
      r_sum_2048,
      a_sum_2049
    ) => let b_2062 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2063 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2047) (b_2062) in 
    let check_2064 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2063)) (point_add (
            r_sum_2048) (a_sum_2049))) in 
    (if (is_identity (check_2064)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactored_batch_verify
  (entries_2065 : seq batch_entry_t)
  (entropy_2066 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_2066)) <.? ((usize 16) * (seq_len (
        entries_2065))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2067 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2068 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2069 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2065)) for (
      s_sum_2067,
      r_sum_2068,
      a_sum_2069
    ) >> (fun i_2070 '(s_sum_2067, r_sum_2068, a_sum_2069) =>
    let 'BatchEntry ((pk_2071, msg_2072, signature_2073)) :=
      (seq_index (entries_2065) (i_2070)) in 
    bind (option_ok_or (decompress (pk_2071)) (InvalidPublickey)) (fun a_2074 =>
      let r_bytes_2075 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2073)) (usize 0) (usize 32) in 
      let s_bytes_2076 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2073)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2076)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2075)) (InvalidR)) (fun r_2077 =>
        let s_2078 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2076)) : scalar_t in 
        let c_2079 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2075) (
                  array_to_seq (pk_2071))) (msg_2072))) in 
        let z_2080 : seq uint8 :=
          seq_slice (entropy_2066) ((usize 16) * (i_2070)) (usize 16) in 
        let z_2081 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2080) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2067 :=
          (s_sum_2067) +% ((s_2078) *% (z_2081)) in 
        let r_sum_2068 :=
          point_add (r_sum_2068) (point_mul (z_2081) (r_2077)) in 
        let a_sum_2069 :=
          point_add (a_sum_2069) (point_mul ((z_2081) *% (c_2079)) (a_2074)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2067, r_sum_2068, a_sum_2069))))))) (fun '(
      s_sum_2067,
      r_sum_2068,
      a_sum_2069
    ) => let b_2082 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2083 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2067) (b_2082) in 
    let check_2084 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2083)) (point_add (
            r_sum_2068) (a_sum_2069))) in 
    (if (is_identity (check_2084)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition ietf_cofactorless_batch_verify
  (entries_2085 : seq batch_entry_t)
  (entropy_2086 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_2086)) <.? ((usize 16) * (seq_len (
        entries_2085))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2087 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2088 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2089 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2085)) for (
      s_sum_2087,
      r_sum_2088,
      a_sum_2089
    ) >> (fun i_2090 '(s_sum_2087, r_sum_2088, a_sum_2089) =>
    let 'BatchEntry ((pk_2091, msg_2092, signature_2093)) :=
      (seq_index (entries_2085) (i_2090)) in 
    bind (option_ok_or (decompress (pk_2091)) (InvalidPublickey)) (fun a_2094 =>
      let r_bytes_2095 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2093)) (usize 0) (usize 32) in 
      let s_bytes_2096 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2093)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2096)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2095)) (InvalidR)) (fun r_2097 =>
        let s_2098 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2096)) : scalar_t in 
        let c_2099 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2095) (
                  array_to_seq (pk_2091))) (msg_2092))) in 
        let z_2100 : seq uint8 :=
          seq_slice (entropy_2086) ((usize 16) * (i_2090)) (usize 16) in 
        let z_2101 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2100) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2087 :=
          (s_sum_2087) +% ((s_2098) *% (z_2101)) in 
        let r_sum_2088 :=
          point_add (r_sum_2088) (point_mul (z_2101) (r_2097)) in 
        let a_sum_2089 :=
          point_add (a_sum_2089) (point_mul ((z_2101) *% (c_2099)) (a_2094)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2087, r_sum_2088, a_sum_2089))))))) (fun '(
      s_sum_2087,
      r_sum_2088,
      a_sum_2089
    ) => let b_2102 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2103 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2087) (b_2102) in 
    let check_2104 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_add (point_neg (sb_2103)) (point_add (r_sum_2088) (a_sum_2089)) in 
    (if (is_identity (check_2104)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

Definition alg3_batch_verify
  (entries_2105 : seq batch_entry_t)
  (entropy_2106 : byte_seq)
  : verify_result_t :=
  ifbnd (seq_len (entropy_2106)) <.? ((usize 16) * (seq_len (
        entries_2105))) : bool
  thenbnd (bind (@Err unit error_t (NotEnoughRandomness)) (fun _ =>
      @Ok unit error_t (tt)))
  else (tt) >> (fun 'tt =>
  let s_sum_2107 : scalar_t :=
    nat_mod_zero  in 
  let r_sum_2108 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  let a_sum_2109 : (
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t '×
      ed25519_field_element_t
    ) :=
    point_identity  in 
  bind (foldibnd (usize 0) to (seq_len (entries_2105)) for (
      s_sum_2107,
      r_sum_2108,
      a_sum_2109
    ) >> (fun i_2110 '(s_sum_2107, r_sum_2108, a_sum_2109) =>
    let 'BatchEntry ((pk_2111, msg_2112, signature_2113)) :=
      (seq_index (entries_2105) (i_2110)) in 
    bind (option_ok_or (decompress (pk_2111)) (InvalidPublickey)) (fun a_2114 =>
      ifbnd is_identity (point_mul_by_cofactor (a_2114)) : bool
      thenbnd (bind (@Err unit error_t (SmallOrderPoint)) (fun _ =>
          @Ok unit error_t (tt)))
      else (tt) >> (fun 'tt =>
      let r_bytes_2115 : compressed_ed_point_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2113)) (usize 0) (usize 32) in 
      let s_bytes_2116 : serialized_scalar_t :=
        array_from_slice (default : uint8) (32) (
          array_to_seq (signature_2113)) (usize 32) (usize 32) in 
      ifbnd negb (check_canonical_scalar (s_bytes_2116)) : bool
      thenbnd (bind (@Err unit error_t (InvalidS)) (fun _ => @Ok unit error_t (
            tt)))
      else (tt) >> (fun 'tt =>
      bind (option_ok_or (decompress (r_bytes_2115)) (InvalidR)) (fun r_2117 =>
        let s_2118 : scalar_t :=
          nat_mod_from_byte_seq_le (array_to_seq (s_bytes_2116)) : scalar_t in 
        let c_2119 : scalar_t :=
          scalar_from_hash (sha512 (seq_concat (array_concat (r_bytes_2115) (
                  array_to_seq (pk_2111))) (msg_2112))) in 
        let z_2120 : seq uint8 :=
          seq_slice (entropy_2106) ((usize 16) * (i_2110)) (usize 16) in 
        let z_2121 : scalar_t :=
          nat_mod_from_byte_seq_le (seq_concat (z_2120) (seq_new_ (
                default : uint8) (usize 16))) : scalar_t in 
        let s_sum_2107 :=
          (s_sum_2107) +% ((s_2118) *% (z_2121)) in 
        let r_sum_2108 :=
          point_add (r_sum_2108) (point_mul (z_2121) (r_2117)) in 
        let a_sum_2109 :=
          point_add (a_sum_2109) (point_mul ((z_2121) *% (c_2119)) (a_2114)) in 
        @Ok (
          scalar_t '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          ) '×
          (
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t '×
            ed25519_field_element_t
          )
        ) error_t ((s_sum_2107, r_sum_2108, a_sum_2109)))))))) (fun '(
      s_sum_2107,
      r_sum_2108,
      a_sum_2109
    ) => let b_2122 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      option_unwrap (decompress (base_v)) in 
    let sb_2123 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul (s_sum_2107) (b_2122) in 
    let check_2124 : (
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t '×
        ed25519_field_element_t
      ) :=
      point_mul_by_cofactor (point_add (point_neg (sb_2123)) (point_add (
            r_sum_2108) (a_sum_2109))) in 
    (if (is_identity (check_2124)):bool then (@Ok unit error_t (tt)) else (
        @Err unit error_t (InvalidSignature))))).

