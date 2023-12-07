(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition build_irreducible (p_914 : uint_size) : seq int128 :=
  let irr_915 : seq int128 :=
    seq_new_ (default) ((p_914) + (usize 1)) in 
  let irr_915 :=
    seq_upd irr_915 (usize 0) (- (@repr WORDSIZE128 1)) in 
  let irr_915 :=
    seq_upd irr_915 (usize 1) (- (@repr WORDSIZE128 1)) in 
  let irr_915 :=
    seq_upd irr_915 (p_914) (@repr WORDSIZE128 1) in 
  irr_915.

Definition round_to_3 (poly_916 : seq int128) (q_917 : int128) : seq int128 :=
  let result_918 : seq int128 :=
    (poly_916) in 
  let q_12_919 : int128 :=
    ((q_917) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let result_918 :=
    foldi (usize 0) (seq_len (poly_916)) (fun i_920 result_918 =>
      let '(result_918) :=
        if (seq_index (poly_916) (i_920)) >.? (q_12_919):bool then (
          let result_918 :=
            seq_upd result_918 (i_920) ((seq_index (poly_916) (i_920)) .- (
                q_917)) in 
          (result_918)) else ((result_918)) in 
      (result_918))
    result_918 in 
  let result_918 :=
    foldi (usize 0) (seq_len (result_918)) (fun i_921 result_918 =>
      let '(result_918) :=
        if ((seq_index (result_918) (i_921)) .% (@repr WORDSIZE128 3)) !=.? (
          @repr WORDSIZE128 0):bool then (let result_918 :=
            seq_upd result_918 (i_921) ((seq_index (result_918) (i_921)) .- (
                @repr WORDSIZE128 1)) in 
          let '(result_918) :=
            if ((seq_index (result_918) (i_921)) .% (
                @repr WORDSIZE128 3)) !=.? (@repr WORDSIZE128 0):bool then (
              let result_918 :=
                seq_upd result_918 (i_921) ((seq_index (result_918) (
                      i_921)) .+ (@repr WORDSIZE128 2)) in 
              (result_918)) else ((result_918)) in 
          (result_918)) else ((result_918)) in 
      (result_918))
    result_918 in 
  result_918.

Definition encrypt
  (r_922 : seq int128)
  (h_923 : seq int128)
  (q_924 : int128)
  (irreducible_925 : seq int128)
  : seq int128 :=
  let pre_926 : seq int128 :=
    mul_poly_irr (r_922) (h_923) (irreducible_925) (q_924) in 
  round_to_3 (pre_926) (q_924).

Definition ntru_prime_653_encrypt
  (r_927 : seq int128)
  (h_928 : seq int128)
  : seq int128 :=
  let p_929 : uint_size :=
    usize 653 in 
  let q_930 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_931 : uint_size :=
    usize 288 in 
  let irreducible_932 : seq int128 :=
    build_irreducible (p_929) in 
  encrypt (r_927) (h_928) (q_930) (irreducible_932).

Definition ntru_prime_653_decrypt
  (c_933 : seq int128)
  (key_f_934 : seq int128)
  (key_v_935 : seq int128)
  : (seq int128 × bool) :=
  let p_936 : uint_size :=
    usize 653 in 
  let q_937 : int128 :=
    @repr WORDSIZE128 4621 in 
  let w_938 : uint_size :=
    usize 288 in 
  let irreducible_939 : seq int128 :=
    build_irreducible (p_936) in 
  let f_c_940 : seq int128 :=
    mul_poly_irr (key_f_934) (c_933) (irreducible_939) (q_937) in 
  let f_3_c_and_decryption_ok_941 : (seq int128 × bool) :=
    poly_to_ring (irreducible_939) (add_poly (f_c_940) (add_poly (f_c_940) (
          f_c_940) (q_937)) (q_937)) (q_937) in 
  let '(f_3_c_942, ok_decrypt_943) :=
    f_3_c_and_decryption_ok_941 in 
  let f_3_c_944 : seq int128 :=
    f_3_c_942 in 
  let q_12_945 : int128 :=
    ((q_937) .- (@repr WORDSIZE128 1)) ./ (@repr WORDSIZE128 2) in 
  let f_3_c_944 :=
    foldi (usize 0) (seq_len (f_3_c_944)) (fun i_946 f_3_c_944 =>
      let '(f_3_c_944) :=
        if (seq_index (f_3_c_944) (i_946)) >.? (q_12_945):bool then (
          let f_3_c_944 :=
            seq_upd f_3_c_944 (i_946) ((seq_index (f_3_c_944) (i_946)) .- (
                q_937)) in 
          (f_3_c_944)) else ((f_3_c_944)) in 
      (f_3_c_944))
    f_3_c_944 in 
  let e_947 : seq int128 :=
    seq_new_ (default) (seq_len (f_3_c_944)) in 
  let e_947 :=
    foldi (usize 0) (seq_len (e_947)) (fun i_948 e_947 =>
      let e_947 :=
        seq_upd e_947 (i_948) ((seq_index (f_3_c_944) (i_948)) .% (
            @repr WORDSIZE128 3)) in 
      (e_947))
    e_947 in 
  let e_947 :=
    make_positive (e_947) (@repr WORDSIZE128 3) in 
  let r_949 : seq int128 :=
    mul_poly_irr (e_947) (key_v_935) (irreducible_939) (@repr WORDSIZE128 3) in 
  let r_949 :=
    foldi (usize 0) (seq_len (r_949)) (fun i_950 r_949 =>
      let '(r_949) :=
        if (seq_index (r_949) (i_950)) =.? (@repr WORDSIZE128 2):bool then (
          let r_949 :=
            seq_upd r_949 (i_950) (- (@repr WORDSIZE128 1)) in 
          (r_949)) else ((r_949)) in 
      (r_949))
    r_949 in 
  (r_949, ok_decrypt_943).

