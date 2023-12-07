(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Require Import Hacspec_Sha256.

Definition bit_size_v : int32 :=
  @repr WORDSIZE32 2048.

Definition byte_size_v : int32 :=
  (@repr WORDSIZE32 2048) ./ (@repr WORDSIZE32 8).

Definition hlen_v : uint_size :=
  usize 32.

Definition rsa_int_t := nat_mod pow2 2048.

Inductive error_t :=
| InvalidLength : error_t
| MessageTooLarge : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidLength => match y with | InvalidLength=> true | _ => false end
   | MessageTooLarge => match y with | MessageTooLarge=> true | _ => false end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'pk_t'" := ((rsa_int_t × rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t × rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t × sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result rsa_int_t error_t)) : hacspec_scope.

Definition rsaep (pk_1947 : pk_t) (m_1948 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1949, e_1950) :=
    pk_1947 in 
  (if ((m_1948) >.? ((n_1949) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_1948) (e_1950) (n_1949)))).

Definition rsadp (sk_1951 : sk_t) (c_1952 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1953, d_1954) :=
    sk_1951 in 
  (if ((c_1952) >.? ((n_1953) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_1952) (d_1954) (n_1953)))).

Definition rsasp1 (sk_1955 : sk_t) (m_1956 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1957, d_1958) :=
    sk_1955 in 
  (if ((m_1956) >.? ((n_1957) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_1956) (d_1958) (n_1957)))).

Definition rsavp1 (pk_1959 : pk_t) (s_1960 : rsa_int_t) : rsa_int_result_t :=
  let '(n_1961, e_1962) :=
    pk_1959 in 
  (if ((s_1960) >.? ((n_1961) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_1960) (e_1962) (n_1961)))).

Definition i2osp
  (x_1963 : rsa_int_t)
  (x_len_1964 : int32)
  : byte_seq_result_t :=
  (if (((x_1963) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_1964))) && ((
          x_len_1964) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_1963)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_1964))) (@cast _ uint32 _ (x_len_1964))))).

Definition os2ip (x_1965 : byte_seq) : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_1965) : rsa_int_t.

Definition mgf1
  (mgf_seed_1966 : byte_seq)
  (mask_len_1967 : uint_size)
  : byte_seq_result_t :=
  let result_1968 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  ifbnd (mask_len_1967) <.? ((usize 2) .^ ((usize 32) * (hlen_v))) : bool
  thenbnd (let t_1969 : seq uint8 :=
      seq_new_ (default) (usize 0) in 
    bind (foldibnd (usize 0) to (((mask_len_1967) + (usize 32)) / (
          usize 32)) for t_1969 >> (fun i_1970 t_1969 =>
      bind (i2osp (nat_mod_from_literal (0x) (pub_u128 (i_1970)) : rsa_int_t) (
          @repr WORDSIZE32 4)) (fun x_1971 => let t_1969 :=
          seq_concat (t_1969) (array_to_seq (sha256 (seq_concat (
                mgf_seed_1966) (x_1971)))) in 
        Ok ((t_1969))))) (fun t_1969 => let result_1968 :=
        @Ok byte_seq error_t (seq_slice (t_1969) (usize 0) (mask_len_1967)) in 
      Ok ((result_1968))))
  else ((result_1968)) >> (fun '(result_1968) =>
  result_1968).

