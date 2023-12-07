(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Notation "'dim_type_t'" := (uint_size) : hacspec_scope.

Notation "'scalar_t'" := (int128) : hacspec_scope.

Notation "'dims_t'" := ((dim_type_t × dim_type_t)) : hacspec_scope.

Notation "'matrix_t'" := ((dims_t × seq scalar_t)) : hacspec_scope.

Notation "'mat_res_t'" := ((result matrix_t unit)) : hacspec_scope.

Definition new_
  (rows_740 : dim_type_t)
  (cols_741 : dim_type_t)
  (seq_742 : seq scalar_t)
  : mat_res_t :=
  (if (((seq_len (seq_742)) >.? (usize 0)) && (((rows_740) * (cols_741)) =.? (
          seq_len (seq_742)))):bool then (@Ok matrix_t unit ((
          (rows_740, cols_741),
          seq_742
        ))) else (@Err matrix_t unit (tt))).

Definition repeat
  (n_743 : dim_type_t)
  (m_744 : dim_type_t)
  (scalar_745 : scalar_t)
  : mat_res_t :=
  let ret_746 : seq int128 :=
    seq_new_ (default) ((n_743) * (m_744)) in 
  let ret_746 :=
    foldi (usize 0) ((n_743) * (m_744)) (fun i_747 ret_746 =>
      let ret_746 :=
        seq_upd ret_746 (i_747) (scalar_745) in 
      (ret_746))
    ret_746 in 
  new_ (n_743) (m_744) (ret_746).

Definition zeros (n_748 : dim_type_t) (m_749 : dim_type_t) : mat_res_t :=
  repeat (n_748) (m_749) (pub_int128_zero ).

Definition ones (n_750 : dim_type_t) (m_751 : dim_type_t) : mat_res_t :=
  repeat (n_750) (m_751) (pub_int128_one ).

Definition identity (n_752 : dim_type_t) (m_753 : dim_type_t) : mat_res_t :=
  let ret_754 : seq int128 :=
    seq_new_ (default) ((n_752) * (m_753)) in 
  let ret_754 :=
    foldi (usize 0) (min (n_752) (m_753)) (fun i_755 ret_754 =>
      let index_756 : uint_size :=
        ((i_755) * (min (n_752) (m_753))) + (i_755) in 
      let ret_754 :=
        seq_upd ret_754 (index_756) (pub_int128_one ) in 
      (ret_754))
    ret_754 in 
  new_ (n_752) (m_753) (ret_754).

