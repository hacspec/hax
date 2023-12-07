(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Aes.

Require Import Hacspec_Aes128_Gcm.

Require Import Hacspec_Chacha20.

Require Import Hacspec_Chacha20poly1305.

Require Import Hacspec_Curve25519.

Require Import Hacspec_Ecdsa_P256_Sha256.

Require Import Hacspec_Gf128.

Require Import Hacspec_Hkdf.

Require Import Hacspec_Hmac.

Require Import Hacspec_P256.

Require Import Hacspec_Poly1305.

Require Import Hacspec_Sha256.

Inductive crypto_error_t :=
| CryptoError : crypto_error_t
| HkdfError : crypto_error_t
| InsufficientEntropy : crypto_error_t
| InvalidCert : crypto_error_t
| MacFailed : crypto_error_t
| UnsupportedAlgorithm : crypto_error_t
| VerifyFailed : crypto_error_t.

Definition empty  : byte_seq :=
  seq_new_ (default) (usize 0).

Definition zeros (u_0 : uint_size) : byte_seq :=
  seq_new_ (default) (u_0).

Notation "'entropy_t'" := (byte_seq) : hacspec_scope.

Definition random_t := nseq (uint8) (usize 32).

Notation "'dh_sk_t'" := (byte_seq) : hacspec_scope.

Notation "'dh_pk_t'" := (byte_seq) : hacspec_scope.

Notation "'signature_key_t'" := (byte_seq) : hacspec_scope.

Notation "'verification_key_t'" := (byte_seq) : hacspec_scope.

Notation "'mac_key_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_key_t'" := (byte_seq) : hacspec_scope.

Notation "'key_t'" := (byte_seq) : hacspec_scope.

Notation "'psk_t'" := (key_t) : hacspec_scope.

Notation "'digest_t'" := (byte_seq) : hacspec_scope.

Notation "'hmac_t'" := (byte_seq) : hacspec_scope.

Notation "'signature_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_iv_t'" := (byte_seq) : hacspec_scope.

Notation "'aead_key_iv_t'" := ((aead_key_t × aead_iv_t)) : hacspec_scope.

Inductive named_group_t :=
| X25519 : named_group_t
| Secp256r1 : named_group_t.

Definition eqb_named_group_t (x y : named_group_t) : bool :=
match x with
   | X25519 => match y with | X25519=> true | _ => false end
   | Secp256r1 => match y with | Secp256r1=> true | _ => false end
   end.

Definition eqb_leibniz_named_group_t (x y : named_group_t) : eqb_named_group_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_named_group_t : EqDec (named_group_t) :=
Build_EqDec (named_group_t) (eqb_named_group_t) (eqb_leibniz_named_group_t).


Inductive hash_algorithm_t :=
| SHA256 : hash_algorithm_t
| SHA384 : hash_algorithm_t.

Definition eqb_hash_algorithm_t (x y : hash_algorithm_t) : bool :=
match x with
   | SHA256 => match y with | SHA256=> true | _ => false end
   | SHA384 => match y with | SHA384=> true | _ => false end
   end.

Definition eqb_leibniz_hash_algorithm_t (x y : hash_algorithm_t) : eqb_hash_algorithm_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_hash_algorithm_t : EqDec (hash_algorithm_t) :=
Build_EqDec (hash_algorithm_t) (eqb_hash_algorithm_t) (eqb_leibniz_hash_algorithm_t).


Inductive aead_algorithm_t :=
| Chacha20Poly1305 : aead_algorithm_t
| Aes128Gcm : aead_algorithm_t
| Aes256Gcm : aead_algorithm_t.

Definition eqb_aead_algorithm_t (x y : aead_algorithm_t) : bool :=
match x with
   | Chacha20Poly1305 => match y with | Chacha20Poly1305=> true | _ => false end
   | Aes128Gcm => match y with | Aes128Gcm=> true | _ => false end
   | Aes256Gcm => match y with | Aes256Gcm=> true | _ => false end
   end.

Definition eqb_leibniz_aead_algorithm_t (x y : aead_algorithm_t) : eqb_aead_algorithm_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_aead_algorithm_t : EqDec (aead_algorithm_t) :=
Build_EqDec (aead_algorithm_t) (eqb_aead_algorithm_t) (eqb_leibniz_aead_algorithm_t).


Inductive signature_scheme_t :=
| ED25519 : signature_scheme_t
| EcdsaSecp256r1Sha256 : signature_scheme_t
| RsaPssRsaSha256 : signature_scheme_t.

Definition eqb_signature_scheme_t (x y : signature_scheme_t) : bool :=
match x with
   | ED25519 => match y with | ED25519=> true | _ => false end
   | EcdsaSecp256r1Sha256 =>
       match y with
       | EcdsaSecp256r1Sha256=> true
       | _ => false
       end
   | RsaPssRsaSha256 => match y with | RsaPssRsaSha256=> true | _ => false end
   end.

Definition eqb_leibniz_signature_scheme_t (x y : signature_scheme_t) : eqb_signature_scheme_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_signature_scheme_t : EqDec (signature_scheme_t) :=
Build_EqDec (signature_scheme_t) (eqb_signature_scheme_t) (eqb_leibniz_signature_scheme_t).


Definition hash_len (ha_1 : hash_algorithm_t) : uint_size :=
  match ha_1 with | SHA256 => usize 32 | SHA384 => usize 48 end.

Definition hmac_key_len (ha_2 : hash_algorithm_t) : uint_size :=
  match ha_2 with | SHA256 => usize 32 | SHA384 => usize 48 end.

Definition ae_key_len (ae_3 : aead_algorithm_t) : uint_size :=
  match ae_3 with
  | Chacha20Poly1305 => usize 32
  | Aes128Gcm => usize 16
  | Aes256Gcm => usize 16
  end.

Definition ae_iv_len (ae_4 : aead_algorithm_t) : uint_size :=
  match ae_4 with
  | Chacha20Poly1305 => usize 12
  | Aes128Gcm => usize 12
  | Aes256Gcm => usize 12
  end.

Definition dh_priv_len (gn_5 : named_group_t) : uint_size :=
  match gn_5 with | X25519 => usize 32 | Secp256r1 => usize 32 end.

Definition dh_pub_len (gn_6 : named_group_t) : uint_size :=
  match gn_6 with | X25519 => usize 32 | Secp256r1 => usize 64 end.

Definition zero_key (ha_7 : hash_algorithm_t) : key_t :=
  seq_new_ (default) (usize (hash_len (ha_7))).

Definition secret_to_public
  (group_name_8 : named_group_t)
  (x_9 : dh_sk_t)
  : (result dh_pk_t crypto_error_t) :=
  match group_name_8 with
  | Secp256r1 => match p256_point_mul_base (nat_mod_from_byte_seq_be (
      x_9) : p256_scalar_t) with
  | Ok (x_10, y_11) => @Ok dh_pk_t crypto_error_t (seq_concat (
      nat_mod_to_byte_seq_be (x_10)) (nat_mod_to_byte_seq_be (y_11)))
  | Err _ => @Err dh_pk_t crypto_error_t (CryptoError)
  end
  | X25519 => @Ok dh_pk_t crypto_error_t (seq_from_seq (
      array_to_seq (x25519_secret_to_public (array_from_seq (32) (x_9)))))
  end.

Definition p256_check_point_len
  (p_12 : dh_pk_t)
  : (result unit crypto_error_t) :=
  (if ((seq_len (p_12)) !=.? (usize 64)):bool then (@Err unit crypto_error_t (
        CryptoError)) else (@Ok unit crypto_error_t (tt))).

Definition p256_ecdh
  (x_13 : dh_sk_t)
  (y_14 : dh_pk_t)
  : (result key_t crypto_error_t) :=
  bind (p256_check_point_len (y_14)) (fun _ => let pk_15 : (
        p256_field_element_t ×
        p256_field_element_t
      ) :=
      (
        nat_mod_from_byte_seq_be (seq_slice_range (y_14) ((usize 0, usize 32
            ))) : p256_field_element_t,
        nat_mod_from_byte_seq_be (seq_slice_range (y_14) ((usize 32, usize 64
            ))) : p256_field_element_t
      ) in 
    match p256_point_mul (nat_mod_from_byte_seq_be (x_13) : p256_scalar_t) (
      pk_15) with
    | Ok (x_16, y_17) => @Ok key_t crypto_error_t (seq_concat (
        nat_mod_to_byte_seq_be (x_16)) (nat_mod_to_byte_seq_be (y_17)))
    | Err _ => @Err key_t crypto_error_t (CryptoError)
    end).

Definition ecdh
  (group_name_18 : named_group_t)
  (x_19 : dh_sk_t)
  (y_20 : dh_pk_t)
  : (result key_t crypto_error_t) :=
  match group_name_18 with
  | Secp256r1 => p256_ecdh (x_19) (y_20)
  | X25519 => @Ok key_t crypto_error_t (seq_from_seq (
      array_to_seq (x25519_scalarmult (array_from_seq (32) (x_19)) (
        array_from_seq (32) (y_20)))))
  end.

Notation "'kem_scheme_t'" := (named_group_t) : hacspec_scope.

Notation "'kem_sk_t'" := (byte_seq) : hacspec_scope.

Notation "'kem_pk_t'" := (byte_seq) : hacspec_scope.

Definition kem_priv_len (ks_21 : kem_scheme_t) : uint_size :=
  dh_priv_len (ks_21).

Definition kem_pub_len (ks_22 : kem_scheme_t) : uint_size :=
  dh_pub_len (ks_22).

Definition kem_priv_to_pub
  (ks_23 : kem_scheme_t)
  (sk_24 : kem_sk_t)
  : (result kem_pk_t crypto_error_t) :=
  secret_to_public (ks_23) (sk_24).

Definition kem_keygen_inner
  (ks_25 : kem_scheme_t)
  (ent_26 : entropy_t)
  : (result (kem_sk_t × kem_pk_t) crypto_error_t) :=
  let sk_27 : seq uint8 :=
    seq_from_seq (seq_slice_range (ent_26) ((usize 0, dh_priv_len (ks_25)))) in 
  bind (kem_priv_to_pub (ks_25) (sk_27)) (fun pk_28 => @Ok (kem_sk_t × kem_pk_t
    ) crypto_error_t ((sk_27, pk_28))).

Definition kem_keygen
  (ks_29 : kem_scheme_t)
  (ent_30 : entropy_t)
  : (result (kem_sk_t × kem_pk_t) crypto_error_t) :=
  (if ((seq_len (ent_30)) <.? (dh_priv_len (ks_29))):bool then (@Err (
        kem_sk_t ×
        kem_pk_t
      ) crypto_error_t (InsufficientEntropy)) else (kem_keygen_inner (ks_29) (
        ent_30))).

Definition kem_encap
  (ks_31 : kem_scheme_t)
  (pk_32 : kem_pk_t)
  (ent_33 : entropy_t)
  : (result (key_t × byte_seq) crypto_error_t) :=
  bind (kem_keygen (ks_31) (ent_33)) (fun '(x_34, gx_35) => bind (ecdh (ks_31) (
        x_34) (pk_32)) (fun gxy_36 => @Ok (key_t × byte_seq) crypto_error_t ((
          gxy_36,
          gx_35
        )))).

Definition kem_decap
  (ks_37 : kem_scheme_t)
  (ct_38 : byte_seq)
  (sk_39 : kem_sk_t)
  : (result key_t crypto_error_t) :=
  bind (ecdh (ks_37) (sk_39) (ct_38)) (fun gxy_40 => @Ok key_t crypto_error_t (
      gxy_40)).

Definition hash
  (ha_41 : hash_algorithm_t)
  (payload_42 : byte_seq)
  : (result digest_t crypto_error_t) :=
  match ha_41 with
  | SHA256 => @Ok digest_t crypto_error_t (seq_from_seq (array_to_seq (sha256 (
        payload_42))))
  | SHA384 => @Err digest_t crypto_error_t (UnsupportedAlgorithm)
  end.

Definition hmac_tag
  (ha_43 : hash_algorithm_t)
  (mk_44 : mac_key_t)
  (payload_45 : byte_seq)
  : (result hmac_t crypto_error_t) :=
  match ha_43 with
  | SHA256 => @Ok hmac_t crypto_error_t (seq_from_seq (array_to_seq (hmac (
        mk_44) (payload_45))))
  | SHA384 => @Err hmac_t crypto_error_t (UnsupportedAlgorithm)
  end.

Definition check_tag_len
  (a_46 : hmac_t)
  (b_47 : hmac_t)
  : (result unit crypto_error_t) :=
  (if ((seq_len (a_46)) =.? (seq_len (b_47))):bool then (
      @Ok unit crypto_error_t (tt)) else (@Err unit crypto_error_t (
        MacFailed))).

Definition check_bytes
  (a_48 : uint8)
  (b_49 : uint8)
  : (result unit crypto_error_t) :=
  (if (negb (uint8_equal (a_48) (b_49))):bool then (@Err unit crypto_error_t (
        MacFailed)) else (@Ok unit crypto_error_t (tt))).

Definition hmac_verify
  (ha_50 : hash_algorithm_t)
  (mk_51 : mac_key_t)
  (payload_52 : byte_seq)
  (m_53 : hmac_t)
  : (result unit crypto_error_t) :=
  bind (hmac_tag (ha_50) (mk_51) (payload_52)) (fun my_hmac_54 => bind (
      check_tag_len (m_53) (my_hmac_54)) (fun _ => bind (foldibnd (usize 0) to (
          seq_len (m_53)) for tt >> (fun i_55 'tt =>
        bind (check_bytes (seq_index (my_hmac_54) (i_55)) (seq_index (m_53) (
              i_55))) (fun _ => Ok (tt)))) (fun _ => @Ok unit crypto_error_t (
          tt)))).

Definition ec_oid_tag_t := nseq (uint8) (usize 9).

Definition get_length_length (b_56 : byte_seq) : uint_size :=
  (if (((uint8_declassify (seq_index (b_56) (usize 0))) shift_right (
          usize 7)) =.? (@repr WORDSIZE8 1)):bool then (
      declassify_usize_from_uint8 ((seq_index (b_56) (usize 0)) .& (secret (
            @repr WORDSIZE8 127) : int8))) else (usize 0)).

Definition get_length (b_57 : byte_seq) (len_58 : uint_size) : uint_size :=
  (@cast _ uint32 _ (declassify_u32_from_uint32 (uint32_from_be_bytes (
          array_from_slice (default) (4) (b_57) (usize 0) (
            len_58))))) usize_shift_right (((usize 4) - (len_58)) * (usize 8)).

Definition get_short_length (b_59 : byte_seq) : uint_size :=
  declassify_usize_from_uint8 ((seq_index (b_59) (usize 0)) .& (secret (
        @repr WORDSIZE8 127) : int8)).

Definition verification_key_from_cert
  (cert_60 : byte_seq)
  : (result verification_key_t crypto_error_t) :=
  let skip_61 : uint_size :=
    ((usize 2) + (get_length_length (seq_slice_range (cert_60) ((
              usize 1,
              seq_len (cert_60)
            ))))) + (usize 1) in 
  let seq1_len_len_62 : uint_size :=
    get_length_length (seq_slice_range (cert_60) ((skip_61, seq_len (cert_60)
        ))) in 
  let skip_63 : uint_size :=
    (skip_61) + (usize 1) in 
  let seq1_len_64 : uint_size :=
    get_length (seq_slice (cert_60) (skip_63) ((seq_len (cert_60)) - (
          skip_63))) (seq1_len_len_62) in 
  let seq1_65 : seq uint8 :=
    seq_slice_range (cert_60) ((
        (skip_63) + (seq1_len_len_62),
        ((skip_63) + (seq1_len_len_62)) + (seq1_len_64)
      )) in 
  let pk_66 : seq uint8 :=
    seq_new_ (default) (usize 0) in 
  let '(seq1_65, pk_66) :=
    foldi (usize 0) (seq_len (seq1_65)) (fun i_67 '(seq1_65, pk_66) =>
      let '(seq1_65, pk_66) :=
        if (seq_len (seq1_65)) >.? (usize 0):bool then (
          let element_type_68 : int8 :=
            uint8_declassify (seq_index (seq1_65) (usize 0)) in 
          let seq1_65 :=
            seq_slice (seq1_65) (usize 1) ((seq_len (seq1_65)) - (usize 1)) in 
          let len_len_69 : uint_size :=
            get_length_length (seq1_65) in 
          let len_70 : uint_size :=
            get_short_length (seq1_65) in 
          let seq1_65 :=
            seq_slice (seq1_65) (usize 1) ((seq_len (seq1_65)) - (usize 1)) in 
          let '(len_70) :=
            if (len_len_69) !=.? (usize 0):bool then (let len_70 :=
                (get_length (seq1_65) (len_len_69)) + (len_len_69) in 
              (len_70)) else ((len_70)) in 
          let '(pk_66) :=
            if ((element_type_68) =.? (@repr WORDSIZE8 48)) && ((seq_len (
                  pk_66)) =.? (usize 0)):bool then (let seq2_71 : seq uint8 :=
                seq_slice (seq1_65) (len_len_69) (len_70) in 
              let element_type_72 : int8 :=
                uint8_declassify (seq_index (seq2_71) (usize 0)) in 
              let seq2_73 : seq uint8 :=
                seq_slice (seq2_71) (usize 1) ((seq_len (seq2_71)) - (
                    usize 1)) in 
              let '(pk_66) :=
                if (element_type_72) =.? (@repr WORDSIZE8 48):bool then (
                  let len_len_74 : uint_size :=
                    get_length_length (seq2_73) in 
                  let '(pk_66) :=
                    if (len_len_74) =.? (usize 0):bool then (
                      let oid_len_75 : uint_size :=
                        get_short_length (seq2_73) in 
                      let '(pk_66) :=
                        if (oid_len_75) >=.? (usize 9):bool then (
                          let expected_76 : seq uint8 :=
                            seq_from_seq (array_to_seq (array_from_list uint8 (
                                let l :=
                                  [
                                    secret (@repr WORDSIZE8 6) : int8;
                                    secret (@repr WORDSIZE8 7) : int8;
                                    secret (@repr WORDSIZE8 42) : int8;
                                    secret (@repr WORDSIZE8 134) : int8;
                                    secret (@repr WORDSIZE8 72) : int8;
                                    secret (@repr WORDSIZE8 206) : int8;
                                    secret (@repr WORDSIZE8 61) : int8;
                                    secret (@repr WORDSIZE8 2) : int8;
                                    secret (@repr WORDSIZE8 1) : int8
                                  ] in  l))) in 
                          let oid_77 : seq uint8 :=
                            seq_slice (seq2_73) (usize 1) (usize 9) in 
                          let ec_pk_oid_78 : bool :=
                            true in 
                          let ec_pk_oid_78 :=
                            foldi (usize 0) (usize 9) (fun i_79 ec_pk_oid_78 =>
                              let oid_byte_equal_80 : bool :=
                                (uint8_declassify (seq_index (oid_77) (
                                      i_79))) =.? (uint8_declassify (seq_index (
                                      expected_76) (i_79))) in 
                              let ec_pk_oid_78 :=
                                (ec_pk_oid_78) && (oid_byte_equal_80) in 
                              (ec_pk_oid_78))
                            ec_pk_oid_78 in 
                          let '(pk_66) :=
                            if ec_pk_oid_78:bool then (
                              let bit_string_81 : seq uint8 :=
                                seq_slice (seq2_73) ((oid_len_75) + (usize 1)) (
                                  ((seq_len (seq2_73)) - (oid_len_75)) - (
                                    usize 1)) in 
                              let '(pk_66) :=
                                if (uint8_declassify (seq_index (
                                      bit_string_81) (usize 0))) =.? (
                                  @repr WORDSIZE8 3):bool then (
                                  let pk_len_82 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_81) (usize 1)) in 
                                  let zeroes_83 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_81) (usize 2)) in 
                                  let uncompressed_84 : uint_size :=
                                    declassify_usize_from_uint8 (seq_index (
                                        bit_string_81) (usize 3)) in 
                                  let pk_66 :=
                                    seq_slice (bit_string_81) (usize 4) ((
                                        pk_len_82) - (usize 2)) in 
                                  (pk_66)) else ((pk_66)) in 
                              (pk_66)) else ((pk_66)) in 
                          (pk_66)) else ((pk_66)) in 
                      (pk_66)) else ((pk_66)) in 
                  (pk_66)) else ((pk_66)) in 
              (pk_66)) else ((pk_66)) in 
          let seq1_65 :=
            seq_slice (seq1_65) (len_70) ((seq_len (seq1_65)) - (len_70)) in 
          (seq1_65, pk_66)) else ((seq1_65, pk_66)) in 
      (seq1_65, pk_66))
    (seq1_65, pk_66) in 
  (if ((seq_len (pk_66)) =.? (usize 0)):bool then (
      @Err verification_key_t crypto_error_t (InvalidCert)) else (
      @Ok verification_key_t crypto_error_t (pk_66))).

Definition concat_signature
  (r_85 : p256_scalar_t)
  (s_86 : p256_scalar_t)
  : (result signature_t crypto_error_t) :=
  let signature_87 : seq uint8 :=
    seq_concat (seq_concat (seq_new_ (default) (usize 0)) (
        nat_mod_to_byte_seq_be (r_85))) (nat_mod_to_byte_seq_be (s_86)) in 
  @Ok signature_t crypto_error_t (signature_87).

Definition p256_sign
  (ps_88 : signature_key_t)
  (payload_89 : byte_seq)
  (ent_90 : entropy_t)
  : (result signature_t crypto_error_t) :=
  let random_91 : random_t :=
    array_from_seq (32) (seq_slice_range (ent_90) ((usize 0, usize 32))) in 
  let nonce_92 : p256_scalar_t :=
    nat_mod_from_byte_seq_be (array_to_seq (random_91)) : p256_scalar_t in 
  match ecdsa_p256_sha256_sign (payload_89) (nat_mod_from_byte_seq_be (
      ps_88) : p256_scalar_t) (nonce_92) with
  | Ok (r_93, s_94) => concat_signature (r_93) (s_94)
  | Err _ => @Err signature_t crypto_error_t (CryptoError)
  end.

Definition sign
  (sa_95 : signature_scheme_t)
  (ps_96 : signature_key_t)
  (payload_97 : byte_seq)
  (ent_98 : entropy_t)
  : (result signature_t crypto_error_t) :=
  match sa_95 with
  | EcdsaSecp256r1Sha256 => p256_sign (ps_96) (payload_97) (ent_98)
  | ED25519 => @Err signature_t crypto_error_t (UnsupportedAlgorithm)
  | RsaPssRsaSha256 => @Err signature_t crypto_error_t (UnsupportedAlgorithm)
  end.

Definition p256_verify
  (pk_99 : verification_key_t)
  (payload_100 : byte_seq)
  (sig_101 : byte_seq)
  : (result unit crypto_error_t) :=
  let '(pk_x_102, pk_y_103) :=
    (
      nat_mod_from_byte_seq_be (seq_slice (pk_99) (usize 0) (
          usize 32)) : p256_field_element_t,
      nat_mod_from_byte_seq_be (seq_slice (pk_99) (usize 32) (
          usize 32)) : p256_field_element_t
    ) in 
  let '(r_104, s_105) :=
    (
      nat_mod_from_byte_seq_be (seq_slice (sig_101) (usize 0) (
          usize 32)) : p256_scalar_t,
      nat_mod_from_byte_seq_be (seq_slice (sig_101) (usize 32) (
          usize 32)) : p256_scalar_t
    ) in 
  match ecdsa_p256_sha256_verify (payload_100) ((pk_x_102, pk_y_103)) ((
      r_104,
      s_105
    )) with
  | Ok tt => @Ok unit crypto_error_t (tt)
  | Err _ => @Err unit crypto_error_t (VerifyFailed)
  end.

Definition verify
  (sa_106 : signature_scheme_t)
  (pk_107 : verification_key_t)
  (payload_108 : byte_seq)
  (sig_109 : byte_seq)
  : (result unit crypto_error_t) :=
  match sa_106 with
  | EcdsaSecp256r1Sha256 => p256_verify (pk_107) (payload_108) (sig_109)
  | ED25519 => @Err unit crypto_error_t (UnsupportedAlgorithm)
  | RsaPssRsaSha256 => @Err unit crypto_error_t (UnsupportedAlgorithm)
  end.

Definition hkdf_extract
  (ha_110 : hash_algorithm_t)
  (k_111 : key_t)
  (salt_112 : key_t)
  : (result key_t crypto_error_t) :=
  match ha_110 with
  | SHA256 => @Ok key_t crypto_error_t (seq_from_seq (array_to_seq (extract (
        salt_112) (k_111))))
  | SHA384 => @Err key_t crypto_error_t (UnsupportedAlgorithm)
  end.

Definition hkdf_expand
  (ha_113 : hash_algorithm_t)
  (k_114 : key_t)
  (info_115 : byte_seq)
  (len_116 : uint_size)
  : (result key_t crypto_error_t) :=
  match ha_113 with
  | SHA256 => match expand (k_114) (info_115) (len_116) with
  | Ok b_117 => @Ok key_t crypto_error_t (seq_from_seq (b_117))
  | Err _ => @Err key_t crypto_error_t (HkdfError)
  end
  | SHA384 => @Err key_t crypto_error_t (UnsupportedAlgorithm)
  end.

Definition aes128_encrypt
  (k_118 : aead_key_t)
  (iv_119 : aead_iv_t)
  (payload_120 : byte_seq)
  (ad_121 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  let '(ctxt_122, tag_123) :=
    encrypt_aes128 (array_from_seq (_) (k_118)) (array_from_seq (_) (iv_119)) (
      ad_121) (payload_120) in 
  @Ok byte_seq crypto_error_t (seq_concat (ctxt_122) (seq_from_seq (
        array_to_seq (tag_123)))).

Definition chacha_encrypt
  (k_124 : aead_key_t)
  (iv_125 : aead_iv_t)
  (payload_126 : byte_seq)
  (ad_127 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  let '(ctxt_128, tag_129) :=
    chacha20_poly1305_encrypt (array_from_seq (32) (k_124)) (array_from_seq (
        12) (iv_125)) (ad_127) (payload_126) in 
  @Ok byte_seq crypto_error_t (seq_concat (ctxt_128) (array_to_seq (tag_129))).

Definition aead_encrypt
  (a_130 : aead_algorithm_t)
  (k_131 : aead_key_t)
  (iv_132 : aead_iv_t)
  (payload_133 : byte_seq)
  (ad_134 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  match a_130 with
  | Aes128Gcm => aes128_encrypt (k_131) (iv_132) (payload_133) (ad_134)
  | Aes256Gcm => @Err byte_seq crypto_error_t (UnsupportedAlgorithm)
  | Chacha20Poly1305 => chacha_encrypt (k_131) (iv_132) (payload_133) (ad_134)
  end.

Definition aes128_decrypt
  (k_135 : aead_key_t)
  (iv_136 : aead_iv_t)
  (ciphertext_137 : byte_seq)
  (ad_138 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  match decrypt_aes128 (array_from_seq (_) (k_135)) (array_from_seq (_) (
      iv_136)) (ad_138) (seq_slice_range (ciphertext_137) ((
        usize 0,
        (seq_len (ciphertext_137)) - (usize 16)
      ))) (array_from_seq (_) (seq_slice_range (ciphertext_137) ((
          (seq_len (ciphertext_137)) - (usize 16),
          seq_len (ciphertext_137)
        )))) with
  | Ok m_139 => @Ok byte_seq crypto_error_t (m_139)
  | Err _ => @Err byte_seq crypto_error_t (MacFailed)
  end.

Definition chacha_decrypt
  (k_140 : aead_key_t)
  (iv_141 : aead_iv_t)
  (ciphertext_142 : byte_seq)
  (ad_143 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  match chacha20_poly1305_decrypt (array_from_seq (32) (k_140)) (
    array_from_seq (12) (iv_141)) (ad_143) (seq_slice_range (ciphertext_142) ((
        usize 0,
        (seq_len (ciphertext_142)) - (usize 16)
      ))) (array_from_seq (16) (seq_slice_range (ciphertext_142) ((
          (seq_len (ciphertext_142)) - (usize 16),
          seq_len (ciphertext_142)
        )))) with
  | Ok ptxt_144 => @Ok byte_seq crypto_error_t (ptxt_144)
  | Err _ => @Err byte_seq crypto_error_t (MacFailed)
  end.

Definition aead_decrypt
  (a_145 : aead_algorithm_t)
  (k_146 : aead_key_t)
  (iv_147 : aead_iv_t)
  (ciphertext_148 : byte_seq)
  (ad_149 : byte_seq)
  : (result byte_seq crypto_error_t) :=
  match a_145 with
  | Aes128Gcm => aes128_decrypt (k_146) (iv_147) (ciphertext_148) (ad_149)
  | Aes256Gcm => @Err byte_seq crypto_error_t (UnsupportedAlgorithm)
  | Chacha20Poly1305 => chacha_decrypt (k_146) (iv_147) (ciphertext_148) (
    ad_149)
  end.

