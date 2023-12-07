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

Inductive error_t :=
| InvalidSecretKey : error_t
| InvalidNonceGenerated : error_t
| InvalidPublicKey : error_t
| InvalidXCoordinate : error_t
| InvalidSignature : error_t.

Definition eqb_error_t (x y : error_t) : bool :=
match x with
   | InvalidSecretKey => match y with | InvalidSecretKey=> true | _ => false end
   | InvalidNonceGenerated =>
       match y with
       | InvalidNonceGenerated=> true
       | _ => false
       end
   | InvalidPublicKey => match y with | InvalidPublicKey=> true | _ => false end
   | InvalidXCoordinate =>
       match y with
       | InvalidXCoordinate=> true
       | _ => false
       end
   | InvalidSignature => match y with | InvalidSignature=> true | _ => false end
   end.

Definition eqb_leibniz_error_t (x y : error_t) : eqb_error_t x y = true <-> x = y.
Proof. split. intros; destruct x ; destruct y ; try (f_equal ; apply eqb_leibniz) ; easy. intros ; subst ; destruct y ; try reflexivity ; try (apply eqb_refl). Qed.

Instance eq_dec_error_t : EqDec (error_t) :=
Build_EqDec (error_t) (eqb_error_t) (eqb_leibniz_error_t).


Definition field_canvas_t := nseq (int8) (32).
Definition field_element_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F.

Definition scalar_canvas_t := nseq (int8) (32).
Definition scalar_t :=
  nat_mod 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141.

Definition big_integer_t := nat_mod pow2 256.

Notation "'affine_point_t'" := ((field_element_t '× field_element_t
)) : hacspec_scope.

Definition p_bytes32_t := nseq (int8) (usize 32).

Inductive point_t :=
| Affine : affine_point_t -> point_t
| AtInfinity : point_t.

Definition finite (p_2555 : point_t) : (option affine_point_t) :=
  match p_2555 with
  | Affine (p_2556) => some (p_2556)
  | AtInfinity => @None affine_point_t
  end.

Definition x (p_2557 : affine_point_t) : field_element_t :=
  let '(x_2558, _) :=
    p_2557 in 
  x_2558.

Definition y (p_2559 : affine_point_t) : field_element_t :=
  let '(_, y_2560) :=
    p_2559 in 
  y_2560.

Definition has_even_y (p_2561 : affine_point_t) : bool :=
  ((y (p_2561)) rem (nat_mod_two )) =.? (nat_mod_zero ).

Definition sqrt (y_2562 : field_element_t) : (option field_element_t) :=
  let p1_4_2563 : field_element_t :=
    nat_mod_from_public_byte_seq_be (array_from_list int8 (let l :=
          [
            @repr WORDSIZE8 63;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 191;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 255;
            @repr WORDSIZE8 12
          ] in  l)) in 
  let x_2564 : field_element_t :=
    nat_mod_pow_self (y_2562) (p1_4_2563) in 
  (if ((nat_mod_pow_self (x_2564) (nat_mod_two )) =.? (y_2562)):bool then (
      some (x_2564)) else (@None field_element_t)).

Definition lift_x
  (x_2565 : field_element_t)
  : (result affine_point_t error_t) :=
  let one_2566 : field_element_t :=
    nat_mod_one  in 
  let two_2567 : field_element_t :=
    nat_mod_two  in 
  let three_2568 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  let seven_2569 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 7) : field_element_t in 
  let y_sq_2570 : field_element_t :=
    (nat_mod_pow_self (x_2565) (three_2568)) +% (seven_2569) in 
  bind (option_ok_or (sqrt (y_sq_2570)) (InvalidXCoordinate)) (fun y_2571 =>
    let '(y_2571) :=
      if ((y_2571) rem (two_2567)) =.? (one_2566):bool then (let y_2571 :=
          (nat_mod_zero ) -% (y_2571) in 
        (y_2571)) else ((y_2571)) in 
    @Ok affine_point_t error_t ((x_2565, y_2571))).

Definition compute_lam
  (p1_2572 : affine_point_t)
  (p2_2573 : affine_point_t)
  : field_element_t :=
  let three_2574 : field_element_t :=
    nat_mod_from_literal (
      0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F) (
      @repr WORDSIZE128 3) : field_element_t in 
  (if ((p1_2572) !=.? (p2_2573)):bool then (((y (p2_2573)) -% (y (
            p1_2572))) *% (nat_mod_pow_self ((x (p2_2573)) -% (x (p1_2572))) ((
            nat_mod_zero ) -% (nat_mod_two )))) else ((((three_2574) *% (x (
              p1_2572))) *% (x (p1_2572))) *% (nat_mod_pow_self ((
            nat_mod_two ) *% (y (p1_2572))) ((nat_mod_zero ) -% (
            nat_mod_two ))))).

Definition point_add (p1_2575 : point_t) (p2_2576 : point_t) : point_t :=
  let result_2577 : point_t :=
    AtInfinity in 
  let '(result_2577) :=
    if option_is_none (finite (p1_2575)):bool then (let result_2577 :=
        p2_2576 in 
      (result_2577)) else (let '(result_2577) :=
        if option_is_none (finite (p2_2576)):bool then (let result_2577 :=
            p1_2575 in 
          (result_2577)) else (let p1_2578 : (
              field_element_t '×
              field_element_t
            ) :=
            option_unwrap (finite (p1_2575)) in 
          let p2_2579 : (field_element_t '× field_element_t) :=
            option_unwrap (finite (p2_2576)) in 
          let '(result_2577) :=
            if negb (((x (p1_2578)) =.? (x (p2_2579))) && ((y (p1_2578)) !=.? (
                  y (p2_2579)))):bool then (let lam_2580 : field_element_t :=
                compute_lam (p1_2578) (p2_2579) in 
              let x3_2581 : field_element_t :=
                (((lam_2580) *% (lam_2580)) -% (x (p1_2578))) -% (x (
                    p2_2579)) in 
              let result_2577 :=
                Affine ((
                    x3_2581,
                    ((lam_2580) *% ((x (p1_2578)) -% (x3_2581))) -% (y (
                        p1_2578))
                  )) in 
              (result_2577)) else ((result_2577)) in 
          (result_2577)) in 
      (result_2577)) in 
  result_2577.

Definition point_mul (s_2582 : scalar_t) (p_2583 : point_t) : point_t :=
  let p_2584 : point_t :=
    p_2583 in 
  let q_2585 : point_t :=
    AtInfinity in 
  let '(p_2584, q_2585) :=
    foldi (usize 0) (usize 256) (fun i_2586 '(p_2584, q_2585) =>
      let '(q_2585) :=
        if nat_mod_bit (s_2582) (i_2586):bool then (let q_2585 :=
            point_add (q_2585) (p_2584) in 
          (q_2585)) else ((q_2585)) in 
      let p_2584 :=
        point_add (p_2584) (p_2584) in 
      (p_2584, q_2585))
    (p_2584, q_2585) in 
  q_2585.

Definition point_mul_base (s_2587 : scalar_t) : point_t :=
  let gx_2588 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 121;
          @repr WORDSIZE8 190;
          @repr WORDSIZE8 102;
          @repr WORDSIZE8 126;
          @repr WORDSIZE8 249;
          @repr WORDSIZE8 220;
          @repr WORDSIZE8 187;
          @repr WORDSIZE8 172;
          @repr WORDSIZE8 85;
          @repr WORDSIZE8 160;
          @repr WORDSIZE8 98;
          @repr WORDSIZE8 149;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 135;
          @repr WORDSIZE8 11;
          @repr WORDSIZE8 7;
          @repr WORDSIZE8 2;
          @repr WORDSIZE8 155;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 219;
          @repr WORDSIZE8 45;
          @repr WORDSIZE8 206;
          @repr WORDSIZE8 40;
          @repr WORDSIZE8 217;
          @repr WORDSIZE8 89;
          @repr WORDSIZE8 242;
          @repr WORDSIZE8 129;
          @repr WORDSIZE8 91;
          @repr WORDSIZE8 22;
          @repr WORDSIZE8 248;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 152
        ] in  l) in 
  let gy_2589 : p_bytes32_t :=
    array_from_list int8 (let l :=
        [
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 58;
          @repr WORDSIZE8 218;
          @repr WORDSIZE8 119;
          @repr WORDSIZE8 38;
          @repr WORDSIZE8 163;
          @repr WORDSIZE8 196;
          @repr WORDSIZE8 101;
          @repr WORDSIZE8 93;
          @repr WORDSIZE8 164;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 252;
          @repr WORDSIZE8 14;
          @repr WORDSIZE8 17;
          @repr WORDSIZE8 8;
          @repr WORDSIZE8 168;
          @repr WORDSIZE8 253;
          @repr WORDSIZE8 23;
          @repr WORDSIZE8 180;
          @repr WORDSIZE8 72;
          @repr WORDSIZE8 166;
          @repr WORDSIZE8 133;
          @repr WORDSIZE8 84;
          @repr WORDSIZE8 25;
          @repr WORDSIZE8 156;
          @repr WORDSIZE8 71;
          @repr WORDSIZE8 208;
          @repr WORDSIZE8 143;
          @repr WORDSIZE8 251;
          @repr WORDSIZE8 16;
          @repr WORDSIZE8 212;
          @repr WORDSIZE8 184
        ] in  l) in 
  let g_2590 : point_t :=
    Affine ((
        nat_mod_from_public_byte_seq_be (gx_2588),
        nat_mod_from_public_byte_seq_be (gy_2589)
      )) in 
  point_mul (s_2587) (g_2590).

Definition bytes32_t := nseq (uint8) (usize 32).

Notation "'secret_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'public_key_t'" := (bytes32_t) : hacspec_scope.

Notation "'message_t'" := (bytes32_t) : hacspec_scope.

Notation "'aux_rand_t'" := (bytes32_t) : hacspec_scope.

Definition signature_t := nseq (uint8) (usize 64).

Definition tagged_hash
  (tag_2591 : public_byte_seq)
  (msg_2592 : byte_seq)
  : bytes32_t :=
  let tag_hash_2593 : seq uint8 :=
    array_to_be_bytes (sha256 (seq_from_public_seq (tag_2591))) in 
  let hash_2594 : sha256_digest_t :=
    sha256 (seq_concat (seq_concat (tag_hash_2593) (tag_hash_2593)) (
        msg_2592)) in 
  array_from_seq (32) (array_to_seq (hash_2594)).

Definition tagged_hash_aux_prefix_t := nseq (int8) (usize 11).

Definition bip0340_aux_v : tagged_hash_aux_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 117;
        @repr WORDSIZE8 120
      ] in  l).

Definition hash_aux (aux_rand_2595 : aux_rand_t) : bytes32_t :=
  tagged_hash (seq_from_seq (array_to_seq (bip0340_aux_v))) (seq_from_seq (
      aux_rand_2595)).

Definition tagged_hash_nonce_prefix_t := nseq (int8) (usize 13).

Definition bip0340_nonce_v : tagged_hash_nonce_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 111;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_nonce
  (rand_2596 : bytes32_t)
  (pubkey_2597 : bytes32_t)
  (msg_2598 : message_t)
  : bytes32_t :=
  let c_2599 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rand_2596))) (
        array_to_seq (pubkey_2597))) (msg_2598) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_nonce_v))) (c_2599).

Definition tagged_hash_challenge_prefix_t := nseq (int8) (usize 17).

Definition bip0340_challenge_v : tagged_hash_challenge_prefix_t :=
  array_from_list int8 (let l :=
      [
        @repr WORDSIZE8 66;
        @repr WORDSIZE8 73;
        @repr WORDSIZE8 80;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 51;
        @repr WORDSIZE8 52;
        @repr WORDSIZE8 48;
        @repr WORDSIZE8 47;
        @repr WORDSIZE8 99;
        @repr WORDSIZE8 104;
        @repr WORDSIZE8 97;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 108;
        @repr WORDSIZE8 101;
        @repr WORDSIZE8 110;
        @repr WORDSIZE8 103;
        @repr WORDSIZE8 101
      ] in  l).

Definition hash_challenge
  (rx_2600 : bytes32_t)
  (pubkey_2601 : bytes32_t)
  (msg_2602 : bytes32_t)
  : bytes32_t :=
  let c_2603 : byte_seq :=
    seq_concat (seq_concat (seq_from_seq (array_to_seq (rx_2600))) (
        array_to_seq (pubkey_2601))) (array_to_seq (msg_2602)) in 
  tagged_hash (seq_from_seq (array_to_seq (bip0340_challenge_v))) (c_2603).

Definition bytes_from_point (p_2604 : affine_point_t) : bytes32_t :=
  let '(x_2605, _) :=
    p_2604 in 
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2605)).

Definition bytes_from_scalar (x_2606 : scalar_t) : bytes32_t :=
  array_from_seq (32) (nat_mod_to_byte_seq_be (x_2606)).

Definition scalar_from_bytes (b_2607 : bytes32_t) : scalar_t :=
  nat_mod_from_byte_seq_be (array_to_seq (b_2607)) : scalar_t.

Definition scalar_from_bytes_strict (b_2608 : bytes32_t) : (option scalar_t) :=
  let s_2609 : big_integer_t :=
    nat_mod_from_byte_seq_be (array_to_seq (b_2608)) : big_integer_t in 
  let max_scalar_2610 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2609) >.? (max_scalar_2610)):bool then (@None scalar_t) else (
      @Some scalar_t (nat_mod_from_byte_seq_be (
          array_to_seq (b_2608)) : scalar_t))).

Definition seckey_scalar_from_bytes (b_2611 : bytes32_t) : (option scalar_t) :=
  bind (scalar_from_bytes_strict (b_2611)) (fun s_2612 => (if ((s_2612) =.? (
          nat_mod_zero )):bool then (@None scalar_t) else (@Some scalar_t (
          s_2612)))).

Definition fieldelem_from_bytes
  (b_2613 : public_key_t)
  : (option field_element_t) :=
  let s_2614 : big_integer_t :=
    nat_mod_from_byte_seq_be (b_2613) : big_integer_t in 
  let max_fe_2615 : big_integer_t :=
    nat_mod_from_byte_seq_be (nat_mod_to_byte_seq_be (
        nat_mod_max_val )) : big_integer_t in 
  (if ((s_2614) >.? (max_fe_2615)):bool then (@None field_element_t) else (
      @Some field_element_t (nat_mod_from_byte_seq_be (
          b_2613) : field_element_t))).

Definition xor_bytes (b0_2616 : bytes32_t) (b1_2617 : bytes32_t) : bytes32_t :=
  let b_2618 : seq uint8 :=
    seq_new_ (default : uint8) (array_len (b0_2616)) in 
  let b_2618 :=
    foldi (usize 0) (array_len (b0_2616)) (fun i_2619 b_2618 =>
      let b_2618 :=
        seq_upd b_2618 (i_2619) ((array_index (b0_2616) (i_2619)) .^ (
            array_index (b1_2617) (i_2619))) in 
      (b_2618))
    b_2618 in 
  array_from_seq (32) (b_2618).

Notation "'pubkey_gen_result_t'" := ((
  result public_key_t error_t)) : hacspec_scope.

Definition pubkey_gen (seckey_2620 : secret_key_t) : pubkey_gen_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2620)) (
      InvalidSecretKey)) (fun d0_2621 => let p_2622 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2621))) in 
    @Ok public_key_t error_t (bytes_from_point (p_2622))).

Notation "'sign_result_t'" := ((result signature_t error_t)) : hacspec_scope.

Definition sign
  (msg_2623 : message_t)
  (seckey_2624 : secret_key_t)
  (aux_rand_2625 : aux_rand_t)
  : sign_result_t :=
  bind (option_ok_or (seckey_scalar_from_bytes (seckey_2624)) (
      InvalidSecretKey)) (fun d0_2626 => let p_2627 : (
        field_element_t '×
        field_element_t
      ) :=
      option_unwrap (finite (point_mul_base (d0_2626))) in 
    let d_2628 : scalar_t :=
      (if (has_even_y (p_2627)):bool then (d0_2626) else ((nat_mod_zero ) -% (
            d0_2626))) in 
    let t_2629 : bytes32_t :=
      xor_bytes (bytes_from_scalar (d_2628)) (hash_aux (aux_rand_2625)) in 
    let k0_2630 : scalar_t :=
      scalar_from_bytes (hash_nonce (t_2629) (bytes_from_point (p_2627)) (
          msg_2623)) in 
    ifbnd (k0_2630) =.? (nat_mod_zero ) : bool
    thenbnd (bind (@Err signature_t error_t (InvalidNonceGenerated)) (fun _ =>
        @Ok unit error_t (tt)))
    else (tt) >> (fun 'tt =>
    let r_2631 : (field_element_t '× field_element_t) :=
      option_unwrap (finite (point_mul_base (k0_2630))) in 
    let k_2632 : scalar_t :=
      (if (has_even_y (r_2631)):bool then (k0_2630) else ((nat_mod_zero ) -% (
            k0_2630))) in 
    let e_2633 : scalar_t :=
      scalar_from_bytes (hash_challenge (bytes_from_point (r_2631)) (
          bytes_from_point (p_2627)) (msg_2623)) in 
    let sig_2634 : signature_t :=
      array_update (array_update (array_new_ (default : uint8) (64)) (usize 0) (
          array_to_seq (bytes_from_point (r_2631)))) (usize 32) (
        array_to_seq (bytes_from_scalar ((k_2632) +% ((e_2633) *% (
              d_2628))))) in 
    bind (verify (msg_2623) (bytes_from_point (p_2627)) (sig_2634)) (fun _ =>
      @Ok signature_t error_t (sig_2634)))).

Notation "'verification_result_t'" := ((result unit error_t)) : hacspec_scope.

Definition verify
  (msg_2635 : message_t)
  (pubkey_2636 : public_key_t)
  (sig_2637 : signature_t)
  : verification_result_t :=
  bind (option_ok_or (fieldelem_from_bytes (pubkey_2636)) (InvalidPublicKey)) (
    fun p_x_2638 => bind (lift_x (p_x_2638)) (fun p_2639 => bind (option_ok_or (
          fieldelem_from_bytes (array_from_slice (default : uint8) (32) (
              array_to_seq (sig_2637)) (usize 0) (usize 32))) (
          InvalidSignature)) (fun r_2640 => bind (option_ok_or (
            scalar_from_bytes_strict (array_from_slice (default : uint8) (32) (
                array_to_seq (sig_2637)) (usize 32) (usize 32))) (
            InvalidSignature)) (fun s_2641 => let e_2642 : scalar_t :=
            scalar_from_bytes (hash_challenge (array_from_slice (
                  default : uint8) (32) (array_to_seq (sig_2637)) (usize 0) (
                  usize 32)) (bytes_from_point (p_2639)) (msg_2635)) in 
          bind (option_ok_or (finite (point_add (point_mul_base (s_2641)) (
                  point_mul ((nat_mod_zero ) -% (e_2642)) (Affine (p_2639))))) (
              InvalidSignature)) (fun r_p_2643 => (if ((negb (has_even_y (
                      r_p_2643))) || ((x (r_p_2643)) !=.? (r_2640))):bool then (
                @Err unit error_t (InvalidSignature)) else (@Ok unit error_t (
                  tt)))))))).

