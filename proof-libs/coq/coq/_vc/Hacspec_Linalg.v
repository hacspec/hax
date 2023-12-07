(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t '× dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t '× seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result matrix_t int8)) : hacspec_scope.

Notation "'scal_res_t'" := ((result scalar_t int8)) : hacspec_scope.

Definition dimension_sequence_length_mismatch_v : int8 :=
  @repr WORDSIZE8 10.

Definition index_out_of_bounds_v : int8 :=
  @repr WORDSIZE8 11.

Definition slice_out_of_bounds_v : int8 :=
  @repr WORDSIZE8 12.

Definition dimension_mismatch_v : int8 :=
  @repr WORDSIZE8 13.

Definition new_
  (rows_881 : dim_type_t)
  (cols_882 : dim_type_t)
  (seq_883 : seq scalar_t)
  : mat_res_t :=
  (if (((seq_len (seq_883)) >.? (usize 0)) && (((rows_881) * (cols_882)) =.? (
          seq_len (seq_883)))):bool then (@Ok matrix_t int8 ((
          (rows_881, cols_882),
          seq_883
        ))) else (@Err matrix_t int8 (dimension_sequence_length_mismatch_v))).

Definition repeat
  (n_884 : dim_type_t)
  (m_885 : dim_type_t)
  (scalar_886 : scalar_t)
  : matrix_t :=
  let ret_887 : seq int128 :=
    seq_new_ (default : scalar_t) ((n_884) * (m_885)) in 
  let ret_887 :=
    foldi (usize 0) ((n_884) * (m_885)) (fun i_888 ret_887 =>
      let ret_887 :=
        seq_upd ret_887 (i_888) (scalar_886) in 
      (ret_887))
    ret_887 in 
  ((n_884, m_885), ret_887).

Definition zeros (n_889 : dim_type_t) (m_890 : dim_type_t) : matrix_t :=
  repeat (n_889) (m_890) (pub_int128_zero ).

Definition ones (n_891 : dim_type_t) (m_892 : dim_type_t) : matrix_t :=
  repeat (n_891) (m_892) (pub_int128_one ).

Definition identity (n_893 : dim_type_t) (m_894 : dim_type_t) : matrix_t :=
  let ret_895 : seq int128 :=
    seq_new_ (default : scalar_t) ((n_893) * (m_894)) in 
  let ret_895 :=
    foldi (usize 0) (min (n_893) (m_894)) (fun i_896 ret_895 =>
      let index_897 : uint_size :=
        ((i_896) * (min (n_893) (m_894))) + (i_896) in 
      let ret_895 :=
        seq_upd ret_895 (index_897) (pub_int128_one ) in 
      (ret_895))
    ret_895 in 
  ((n_893, m_894), ret_895).

Definition index
  (m_898 : matrix_t)
  (i_899 : dim_type_t)
  (j_900 : dim_type_t)
  : scal_res_t :=
  let '(dim_901, seq_902) :=
    m_898 in 
  let '(rows_903, cols_904) :=
    dim_901 in 
  let index_905 : uint_size :=
    ((i_899) * (cols_904)) + (j_900) in 
  (if ((index_905) >=.? ((rows_903) * (cols_904))):bool then (
      @Err scalar_t int8 (index_out_of_bounds_v)) else (@Ok scalar_t int8 (
        seq_index (seq_902) (index_905)))).

Definition transpose (matrix_906 : matrix_t) : matrix_t :=
  let '(dim_907, seq_908) :=
    matrix_906 in 
  let '(rows_909, cols_910) :=
    dim_907 in 
  let ret_911 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (seq_908)) in 
  let ret_911 :=
    foldi (usize 0) (rows_909) (fun i_912 ret_911 =>
      let ret_911 :=
        foldi (usize 0) (cols_910) (fun j_913 ret_911 =>
          let seq_index_914 : uint_size :=
            ((i_912) * (cols_910)) + (j_913) in 
          let ret_index_915 : uint_size :=
            ((j_913) * (rows_909)) + (i_912) in 
          let ret_911 :=
            seq_upd ret_911 (ret_index_915) (seq_index (seq_908) (
                seq_index_914)) in 
          (ret_911))
        ret_911 in 
      (ret_911))
    ret_911 in 
  ((cols_910, rows_909), ret_911).

Definition slice
  (matrix_916 : matrix_t)
  (start_917 : dims_t)
  (len_918 : dims_t)
  : mat_res_t :=
  let '(dim_919, seq_920) :=
    matrix_916 in 
  let '(rows_921, cols_922) :=
    dim_919 in 
  let '(start_row_923, start_col_924) :=
    start_917 in 
  let '(len_rows_925, len_cols_926) :=
    len_918 in 
  let start_index_927 : uint_size :=
    ((start_row_923) * (cols_922)) + (start_col_924) in 
  let ret_928 : seq int128 :=
    seq_new_ (default : scalar_t) ((len_rows_925) * (len_cols_926)) in 
  let res_929 : (result matrix_t int8) :=
    @Err matrix_t int8 (slice_out_of_bounds_v) in 
  let '(ret_928, res_929) :=
    if ((start_index_927) + ((len_rows_925) * (len_cols_926))) <=.? ((
        rows_921) * (cols_922)):bool then (let ret_928 :=
        foldi (usize 0) (len_rows_925) (fun i_930 ret_928 =>
          let ret_928 :=
            foldi (usize 0) (len_cols_926) (fun j_931 ret_928 =>
              let ret_index_932 : uint_size :=
                ((i_930) * (len_cols_926)) + (j_931) in 
              let seq_index_933 : uint_size :=
                (((start_row_923) + (i_930)) * (cols_922)) + ((
                    start_col_924) + (j_931)) in 
              let ret_928 :=
                seq_upd ret_928 (ret_index_932) (seq_index (seq_920) (
                    seq_index_933)) in 
              (ret_928))
            ret_928 in 
          (ret_928))
        ret_928 in 
      let res_929 :=
        new_ (len_rows_925) (len_cols_926) (ret_928) in 
      (ret_928, res_929)) else ((ret_928, res_929)) in 
  res_929.

Definition scale (matrix_934 : matrix_t) (scalar_935 : scalar_t) : matrix_t :=
  let '(dim_936, seq_937) :=
    matrix_934 in 
  let ret_938 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (seq_937)) in 
  let ret_938 :=
    foldi (usize 0) (seq_len (seq_937)) (fun i_939 ret_938 =>
      let ret_938 :=
        seq_upd ret_938 (i_939) ((scalar_935) .* (seq_index (seq_937) (
              i_939))) in 
      (ret_938))
    ret_938 in 
  (dim_936, ret_938).

Definition add
  (matrix_1_940 : matrix_t)
  (matrix_2_941 : matrix_t)
  : mat_res_t :=
  let '(m1_dim_942, m1_s_943) :=
    matrix_1_940 in 
  let '(m2_dim_944, m2_s_945) :=
    matrix_2_941 in 
  let ret_946 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_943)) in 
  let res_947 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_946, res_947) :=
    if (m1_dim_942) =.? (m2_dim_944):bool then (let ret_946 :=
        foldi (usize 0) (seq_len (m1_s_943)) (fun i_948 ret_946 =>
          let ret_946 :=
            seq_upd ret_946 (i_948) ((seq_index (m1_s_943) (i_948)) .+ (
                seq_index (m2_s_945) (i_948))) in 
          (ret_946))
        ret_946 in 
      let res_947 :=
        @Ok matrix_t int8 ((m1_dim_942, ret_946)) in 
      (ret_946, res_947)) else ((ret_946, res_947)) in 
  res_947.

Definition sub
  (matrix_1_949 : matrix_t)
  (matrix_2_950 : matrix_t)
  : mat_res_t :=
  let '(m1_dim_951, m1_s_952) :=
    matrix_1_949 in 
  let '(m2_dim_953, m2_s_954) :=
    matrix_2_950 in 
  let ret_955 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_952)) in 
  let res_956 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_955, res_956) :=
    if (m1_dim_951) =.? (m2_dim_953):bool then (let ret_955 :=
        foldi (usize 0) (seq_len (m1_s_952)) (fun i_957 ret_955 =>
          let ret_955 :=
            seq_upd ret_955 (i_957) ((seq_index (m1_s_952) (i_957)) .- (
                seq_index (m2_s_954) (i_957))) in 
          (ret_955))
        ret_955 in 
      let res_956 :=
        @Ok matrix_t int8 ((m1_dim_951, ret_955)) in 
      (ret_955, res_956)) else ((ret_955, res_956)) in 
  res_956.

Definition component_mul
  (matrix_1_958 : matrix_t)
  (matrix_2_959 : matrix_t)
  : mat_res_t :=
  let '(m1_dim_960, m1_s_961) :=
    matrix_1_958 in 
  let '(m2_dim_962, m2_s_963) :=
    matrix_2_959 in 
  let ret_964 : seq int128 :=
    seq_new_ (default : scalar_t) (seq_len (m1_s_961)) in 
  let res_965 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_964, res_965) :=
    if (m1_dim_960) =.? (m2_dim_962):bool then (let ret_964 :=
        foldi (usize 0) (seq_len (m1_s_961)) (fun i_966 ret_964 =>
          let ret_964 :=
            seq_upd ret_964 (i_966) ((seq_index (m1_s_961) (i_966)) .* (
                seq_index (m2_s_963) (i_966))) in 
          (ret_964))
        ret_964 in 
      let res_965 :=
        @Ok matrix_t int8 ((m1_dim_960, ret_964)) in 
      (ret_964, res_965)) else ((ret_964, res_965)) in 
  res_965.

Definition mul
  (matrix_1_967 : matrix_t)
  (matrix_2_968 : matrix_t)
  : mat_res_t :=
  let '(dim_1_969, seq_1_970) :=
    matrix_1_967 in 
  let '(dim_2_971, seq_2_972) :=
    matrix_2_968 in 
  let '(l_973, m_974) :=
    dim_1_969 in 
  let '(m_975, n_976) :=
    dim_2_971 in 
  let ret_977 : seq int128 :=
    seq_new_ (default : scalar_t) ((l_973) * (n_976)) in 
  let res_978 : (result matrix_t int8) :=
    @Err matrix_t int8 (dimension_mismatch_v) in 
  let '(ret_977, res_978) :=
    if (m_974) =.? (m_975):bool then (let ret_977 :=
        foldi (usize 0) (l_973) (fun i_979 ret_977 =>
          let ret_977 :=
            foldi (usize 0) (n_976) (fun j_980 ret_977 =>
              let acc_981 : int128 :=
                pub_int128_zero  in 
              let index_982 : uint_size :=
                ((i_979) * (n_976)) + (j_980) in 
              let acc_981 :=
                foldi (usize 0) (m_974) (fun k_983 acc_981 =>
                  let index_1_984 : uint_size :=
                    ((i_979) * (m_974)) + (k_983) in 
                  let index_2_985 : uint_size :=
                    ((k_983) * (n_976)) + (j_980) in 
                  let acc_981 :=
                    (acc_981) .+ ((seq_index (seq_1_970) (index_1_984)) .* (
                        seq_index (seq_2_972) (index_2_985))) in 
                  (acc_981))
                acc_981 in 
              let ret_977 :=
                seq_upd ret_977 (index_982) (acc_981) in 
              (ret_977))
            ret_977 in 
          (ret_977))
        ret_977 in 
      let res_978 :=
        new_ (l_973) (n_976) (ret_977) in 
      (ret_977, res_978)) else ((ret_977, res_978)) in 
  res_978.

