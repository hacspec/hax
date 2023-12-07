(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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
| MessageTooLarge : error_t
| DecryptionFailed : error_t
| VerificationFailed : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidLength => match y with | InvalidLength=> true | _ => false end
   | MessageTooLarge => match y with | MessageTooLarge=> true | _ => false end
   | DecryptionFailed => match y with | DecryptionFailed=> true | _ => false end
   | VerificationFailed =>
       match y with
       | VerificationFailed=> true
       | _ => false
       end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Notation "'pk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'sk_t'" := ((rsa_int_t '× rsa_int_t)) : hacspec_scope.

Notation "'key_pair_t'" := ((pk_t '× sk_t)) : hacspec_scope.

Notation "'byte_seq_result_t'" := ((result byte_seq error_t)) : hacspec_scope.

Notation "'rsa_int_result_t'" := ((result rsa_int_t error_t)) : hacspec_scope.

Definition rsaep (pk_2530 : pk_t) (m_2531 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2532, e_2533) :=
    pk_2530 in 
  (if ((m_2531) >.? ((n_2532) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2531) (e_2533) (n_2532)))).

Definition rsadp (sk_2534 : sk_t) (c_2535 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2536, d_2537) :=
    sk_2534 in 
  (if ((c_2535) >.? ((n_2536) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (c_2535) (d_2537) (n_2536)))).

Definition rsasp1 (sk_2538 : sk_t) (m_2539 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2540, d_2541) :=
    sk_2538 in 
  (if ((m_2539) >.? ((n_2540) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (m_2539) (d_2541) (n_2540)))).

Definition rsavp1 (pk_2542 : pk_t) (s_2543 : rsa_int_t) : rsa_int_result_t :=
  let '(n_2544, e_2545) :=
    pk_2542 in 
  (if ((s_2543) >.? ((n_2544) -% (nat_mod_one ))):bool then (
      @Err rsa_int_t error_t (MessageTooLarge)) else (@Ok rsa_int_t error_t (
        nat_mod_pow_mod (s_2543) (e_2545) (n_2544)))).

Definition i2osp
  (x_2546 : rsa_int_t)
  (x_len_2547 : int32)
  : byte_seq_result_t :=
  (if (((x_2546) >=.? (nat_mod_exp (nat_mod_from_literal (0x) (
              @repr WORDSIZE128 256) : rsa_int_t) (x_len_2547))) && ((
          x_len_2547) !=.? (byte_size_v))):bool then (@Err byte_seq error_t (
        InvalidLength)) else (@Ok byte_seq error_t (seq_slice (
          nat_mod_to_byte_seq_be (x_2546)) (@cast _ uint32 _ ((byte_size_v) .- (
              x_len_2547))) (@cast _ uint32 _ (x_len_2547))))).

Definition os2ip (x_2548 : byte_seq) : rsa_int_t :=
  nat_mod_from_byte_seq_be (x_2548) : rsa_int_t.

Definition mgf1
  (mgf_seed_2549 : byte_seq)
  (mask_len_2550 : uint_size)
  : byte_seq_result_t :=
  let result_2551 : (result byte_seq error_t) :=
    @Err byte_seq error_t (InvalidLength) in 
  ifbnd (mask_len_2550) <.? ((usize 2) .^ ((usize 32) * (hlen_v))) : bool
  thenbnd (let t_2552 : seq uint8 :=
      seq_new_ (default : uint8) (usize 0) in 
    bind (foldibnd (usize 0) to (((mask_len_2550) + (usize 32)) / (
          usize 32)) for t_2552 >> (fun i_2553 t_2552 =>
      bind (i2osp (nat_mod_from_literal (0x) (pub_u128 (i_2553)) : rsa_int_t) (
          @repr WORDSIZE32 4)) (fun x_2554 => let t_2552 :=
          seq_concat (t_2552) (array_to_seq (sha256 (seq_concat (
                mgf_seed_2549) (x_2554)))) in 
        @Ok (seq uint8) error_t ((t_2552))))) (fun t_2552 => let result_2551 :=
        @Ok byte_seq error_t (seq_slice (t_2552) (usize 0) (mask_len_2550)) in 
      @Ok ((result byte_seq error_t)) error_t ((result_2551))))
  else ((result_2551)) >> (fun '(result_2551) =>
  result_2551).

