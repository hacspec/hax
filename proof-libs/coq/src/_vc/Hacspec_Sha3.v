(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition rounds_v : uint_size :=
  usize 24.

Definition sha3224_rate_v : uint_size :=
  usize 144.

Definition sha3256_rate_v : uint_size :=
  usize 136.

Definition sha3384_rate_v : uint_size :=
  usize 104.

Definition sha3512_rate_v : uint_size :=
  usize 72.

Definition shake128_rate_v : uint_size :=
  usize 168.

Definition shake256_rate_v : uint_size :=
  usize 136.

Definition state_t := nseq (uint64) (usize 25).

Definition row_t := nseq (uint64) (usize 5).

Definition digest224_t := nseq (uint8) (usize 28).

Definition digest256_t := nseq (uint8) (usize 32).

Definition digest384_t := nseq (uint8) (usize 48).

Definition digest512_t := nseq (uint8) (usize 64).

Definition round_constants_t := nseq (int64) (rounds_v).

Definition rotation_constants_t := nseq (uint_size) (usize 25).

Definition roundconstants_v : round_constants_t :=
  array_from_list int64 (let l :=
      [
        @repr WORDSIZE64 1;
        @repr WORDSIZE64 32898;
        @repr WORDSIZE64 9223372036854808714;
        @repr WORDSIZE64 9223372039002292224;
        @repr WORDSIZE64 32907;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808585;
        @repr WORDSIZE64 138;
        @repr WORDSIZE64 136;
        @repr WORDSIZE64 2147516425;
        @repr WORDSIZE64 2147483658;
        @repr WORDSIZE64 2147516555;
        @repr WORDSIZE64 9223372036854775947;
        @repr WORDSIZE64 9223372036854808713;
        @repr WORDSIZE64 9223372036854808579;
        @repr WORDSIZE64 9223372036854808578;
        @repr WORDSIZE64 9223372036854775936;
        @repr WORDSIZE64 32778;
        @repr WORDSIZE64 9223372039002259466;
        @repr WORDSIZE64 9223372039002292353;
        @repr WORDSIZE64 9223372036854808704;
        @repr WORDSIZE64 2147483649;
        @repr WORDSIZE64 9223372039002292232
      ] in  l).

Definition rotc_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 1;
        usize 62;
        usize 28;
        usize 27;
        usize 36;
        usize 44;
        usize 6;
        usize 55;
        usize 20;
        usize 3;
        usize 10;
        usize 43;
        usize 25;
        usize 39;
        usize 41;
        usize 45;
        usize 15;
        usize 21;
        usize 8;
        usize 18;
        usize 2;
        usize 61;
        usize 56;
        usize 14
      ] in  l).

Definition pi_v : rotation_constants_t :=
  array_from_list uint_size (let l :=
      [
        usize 0;
        usize 6;
        usize 12;
        usize 18;
        usize 24;
        usize 3;
        usize 9;
        usize 10;
        usize 16;
        usize 22;
        usize 1;
        usize 7;
        usize 13;
        usize 19;
        usize 20;
        usize 4;
        usize 5;
        usize 11;
        usize 17;
        usize 23;
        usize 2;
        usize 8;
        usize 14;
        usize 15;
        usize 21
      ] in  l).

Definition theta (s_855 : state_t) : state_t :=
  let b_856 : row_t :=
    array_new_ (default) (5) in 
  let b_856 :=
    foldi (usize 0) (usize 5) (fun i_857 b_856 =>
      let b_856 :=
        array_upd b_856 (i_857) (((((array_index (s_855) (i_857)) .^ (
                  array_index (s_855) ((i_857) + (usize 5)))) .^ (array_index (
                  s_855) ((i_857) + (usize 10)))) .^ (array_index (s_855) ((
                  i_857) + (usize 15)))) .^ (array_index (s_855) ((i_857) + (
                usize 20)))) in 
      (b_856))
    b_856 in 
  let s_855 :=
    foldi (usize 0) (usize 5) (fun i_858 s_855 =>
      let u_859 : uint64 :=
        array_index (b_856) (((i_858) + (usize 1)) %% (usize 5)) in 
      let t_860 : uint64 :=
        (array_index (b_856) (((i_858) + (usize 4)) %% (usize 5))) .^ (
          uint64_rotate_left (u_859) (usize 1)) in 
      let s_855 :=
        foldi (usize 0) (usize 5) (fun j_861 s_855 =>
          let s_855 :=
            array_upd s_855 (((usize 5) * (j_861)) + (i_858)) ((array_index (
                  s_855) (((usize 5) * (j_861)) + (i_858))) .^ (t_860)) in 
          (s_855))
        s_855 in 
      (s_855))
    s_855 in 
  s_855.

Definition rho (s_862 : state_t) : state_t :=
  let s_862 :=
    foldi (usize 0) (usize 25) (fun i_863 s_862 =>
      let u_864 : uint64 :=
        array_index (s_862) (i_863) in 
      let s_862 :=
        array_upd s_862 (i_863) (uint64_rotate_left (u_864) (array_index (
              rotc_v) (i_863))) in 
      (s_862))
    s_862 in 
  s_862.

Definition pi (s_865 : state_t) : state_t :=
  let v_866 : state_t :=
    array_new_ (default) (25) in 
  let v_866 :=
    foldi (usize 0) (usize 25) (fun i_867 v_866 =>
      let v_866 :=
        array_upd v_866 (i_867) (array_index (s_865) (array_index (pi_v) (
              i_867))) in 
      (v_866))
    v_866 in 
  v_866.

Definition chi (s_868 : state_t) : state_t :=
  let b_869 : row_t :=
    array_new_ (default) (5) in 
  let '(s_868, b_869) :=
    foldi (usize 0) (usize 5) (fun i_870 '(s_868, b_869) =>
      let b_869 :=
        foldi (usize 0) (usize 5) (fun j_871 b_869 =>
          let b_869 :=
            array_upd b_869 (j_871) (array_index (s_868) (((usize 5) * (
                    i_870)) + (j_871))) in 
          (b_869))
        b_869 in 
      let s_868 :=
        foldi (usize 0) (usize 5) (fun j_872 s_868 =>
          let u_873 : uint64 :=
            array_index (b_869) (((j_872) + (usize 1)) %% (usize 5)) in 
          let s_868 :=
            array_upd s_868 (((usize 5) * (i_870)) + (j_872)) ((array_index (
                  s_868) (((usize 5) * (i_870)) + (j_872))) .^ ((not (
                    u_873)) .& (array_index (b_869) (((j_872) + (usize 2)) %% (
                      usize 5))))) in 
          (s_868))
        s_868 in 
      (s_868, b_869))
    (s_868, b_869) in 
  s_868.

Definition iota (s_874 : state_t) (rndconst_875 : int64) : state_t :=
  let s_874 :=
    array_upd s_874 (usize 0) ((array_index (s_874) (usize 0)) .^ (
        uint64_classify (rndconst_875))) in 
  s_874.

Definition keccakf1600 (s_876 : state_t) : state_t :=
  let s_876 :=
    foldi (usize 0) (rounds_v) (fun i_877 s_876 =>
      let s_876 :=
        theta (s_876) in 
      let s_876 :=
        rho (s_876) in 
      let s_876 :=
        pi (s_876) in 
      let s_876 :=
        chi (s_876) in 
      let s_876 :=
        iota (s_876) (array_index (roundconstants_v) (i_877)) in 
      (s_876))
    s_876 in 
  s_876.

Definition absorb_block (s_878 : state_t) (block_879 : byte_seq) : state_t :=
  let s_878 :=
    foldi (usize 0) (seq_len (block_879)) (fun i_880 s_878 =>
      let w_881 : uint_size :=
        (i_880) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_882 : uint_size :=
        (usize 8) * ((i_880) .& (usize 7)) in 
      let s_878 :=
        array_upd s_878 (w_881) ((array_index (s_878) (w_881)) .^ ((
              uint64_from_uint8 (seq_index (block_879) (i_880))) shift_left (
              o_882))) in 
      (s_878))
    s_878 in 
  keccakf1600 (s_878).

Definition squeeze
  (s_883 : state_t)
  (nbytes_884 : uint_size)
  (rate_885 : uint_size)
  : byte_seq :=
  let out_886 : seq uint8 :=
    seq_new_ (default) (nbytes_884) in 
  let '(s_883, out_886) :=
    foldi (usize 0) (nbytes_884) (fun i_887 '(s_883, out_886) =>
      let pos_888 : uint_size :=
        (i_887) %% (rate_885) in 
      let w_889 : uint_size :=
        (pos_888) usize_shift_right (@repr WORDSIZE32 3) in 
      let o_890 : uint_size :=
        (usize 8) * ((pos_888) .& (usize 7)) in 
      let b_891 : uint64 :=
        ((array_index (s_883) (w_889)) shift_right (o_890)) .& (
          uint64_classify (@repr WORDSIZE64 255)) in 
      let out_886 :=
        seq_upd out_886 (i_887) (uint8_from_uint64 (b_891)) in 
      let '(s_883) :=
        if (((i_887) + (usize 1)) %% (rate_885)) =.? (usize 0):bool then (
          let s_883 :=
            keccakf1600 (s_883) in 
          (s_883)) else ((s_883)) in 
      (s_883, out_886))
    (s_883, out_886) in 
  out_886.

Definition keccak
  (rate_892 : uint_size)
  (data_893 : byte_seq)
  (p_894 : int8)
  (outbytes_895 : uint_size)
  : byte_seq :=
  let buf_896 : seq uint8 :=
    seq_new_ (default) (rate_892) in 
  let last_block_len_897 : uint_size :=
    usize 0 in 
  let s_898 : state_t :=
    array_new_ (default) (25) in 
  let '(buf_896, last_block_len_897, s_898) :=
    foldi (usize 0) (seq_num_chunks (data_893) (rate_892)) (fun i_899 '(
        buf_896,
        last_block_len_897,
        s_898
      ) =>
      let '(block_len_900, block_901) :=
        seq_get_chunk (data_893) (rate_892) (i_899) in 
      let '(buf_896, last_block_len_897, s_898) :=
        if (block_len_900) =.? (rate_892):bool then (let s_898 :=
            absorb_block (s_898) (block_901) in 
          (buf_896, last_block_len_897, s_898)) else (let buf_896 :=
            seq_update_start (buf_896) (block_901) in 
          let last_block_len_897 :=
            block_len_900 in 
          (buf_896, last_block_len_897, s_898)) in 
      (buf_896, last_block_len_897, s_898))
    (buf_896, last_block_len_897, s_898) in 
  let buf_896 :=
    seq_upd buf_896 (last_block_len_897) (secret (p_894) : int8) in 
  let buf_896 :=
    seq_upd buf_896 ((rate_892) - (usize 1)) ((seq_index (buf_896) ((
            rate_892) - (usize 1))) .| (secret (
          @repr WORDSIZE8 128) : int8)) in 
  let s_898 :=
    absorb_block (s_898) (buf_896) in 
  squeeze (s_898) (outbytes_895) (rate_892).

Definition sha3224 (data_902 : byte_seq) : digest224_t :=
  let t_903 : seq uint8 :=
    keccak (sha3224_rate_v) (data_902) (@repr WORDSIZE8 6) (usize 28) in 
  array_from_seq (28) (t_903).

Definition sha3256 (data_904 : byte_seq) : digest256_t :=
  let t_905 : seq uint8 :=
    keccak (sha3256_rate_v) (data_904) (@repr WORDSIZE8 6) (usize 32) in 
  array_from_seq (32) (t_905).

Definition sha3384 (data_906 : byte_seq) : digest384_t :=
  let t_907 : seq uint8 :=
    keccak (sha3384_rate_v) (data_906) (@repr WORDSIZE8 6) (usize 48) in 
  array_from_seq (48) (t_907).

Definition sha3512 (data_908 : byte_seq) : digest512_t :=
  let t_909 : seq uint8 :=
    keccak (sha3512_rate_v) (data_908) (@repr WORDSIZE8 6) (usize 64) in 
  array_from_seq (64) (t_909).

Definition shake128 (data_910 : byte_seq) (outlen_911 : uint_size) : byte_seq :=
  keccak (shake128_rate_v) (data_910) (@repr WORDSIZE8 31) (outlen_911).

Definition shake256 (data_912 : byte_seq) (outlen_913 : uint_size) : byte_seq :=
  keccak (shake256_rate_v) (data_912) (@repr WORDSIZE8 31) (outlen_913).

