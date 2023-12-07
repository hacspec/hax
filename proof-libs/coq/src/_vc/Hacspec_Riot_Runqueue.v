(** This file was automatically generated using Hacspec **)
Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.
Require Import Hacspec_Lib.

Definition uint32_bits_v : uint_size :=
  (usize 4) * (usize 8).

Definition n_queues_v : uint_size :=
  usize 20.

Definition n_threads_v : uint_size :=
  usize 30.

Definition sentinel_v : int8 :=
  @repr WORDSIZE8 255.

Inductive runqueue_id_t :=
| RunqueueId : int8 -> runqueue_id_t.

Inductive thread_id_t :=
| ThreadId : int8 -> thread_id_t.

Definition tail_t := nseq (int8) (n_queues_v).

Definition next_ids_t := nseq (int8) (n_threads_v).

Inductive clist_t :=
| Clist : (tail_t × next_ids_t) -> clist_t.

Definition clist_new  : clist_t :=
  let tail_1005 : tail_t :=
    array_new_ (default) (n_queues_v) in 
  let tail_1005 :=
    foldi (usize 0) (array_len (tail_1005)) (fun i_1006 tail_1005 =>
      let tail_1005 :=
        array_upd tail_1005 (i_1006) (sentinel_v) in 
      (tail_1005))
    tail_1005 in 
  let next_idxs_1007 : next_ids_t :=
    array_new_ (default) (n_threads_v) in 
  let next_idxs_1007 :=
    foldi (usize 0) (array_len (next_idxs_1007)) (fun i_1008 next_idxs_1007 =>
      let next_idxs_1007 :=
        array_upd next_idxs_1007 (i_1008) (sentinel_v) in 
      (next_idxs_1007))
    next_idxs_1007 in 
  Clist ((tail_1005, next_idxs_1007)).

Definition clist_is_empty (x_1009 : clist_t) (rq_1010 : runqueue_id_t) : bool :=
  let 'RunqueueId (rq_1011) :=
    rq_1010 in 
  let 'Clist ((tail_1012, next_ids_1013)) :=
    x_1009 in 
  (array_index (tail_1012) (@cast _ uint32 _ (rq_1011))) =.? (sentinel_v).

Definition clist_push
  (x_1014 : clist_t)
  (n_1015 : thread_id_t)
  (rq_1016 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1017) :=
    rq_1016 in 
  let 'ThreadId (n_1018) :=
    n_1015 in 
  let 'Clist ((tail_1019, next_idxs_1020)) :=
    x_1014 in 
  let '(tail_1019, next_idxs_1020) :=
    if (array_index (next_idxs_1020) (@cast _ uint32 _ (n_1018))) =.? (
      sentinel_v):bool then (let '(tail_1019, next_idxs_1020) :=
        if (array_index (tail_1019) (@cast _ uint32 _ (rq_1017))) =.? (
          sentinel_v):bool then (let tail_1019 :=
            array_upd tail_1019 (@cast _ uint32 _ (rq_1017)) (n_1018) in 
          let next_idxs_1020 :=
            array_upd next_idxs_1020 (@cast _ uint32 _ (n_1018)) (n_1018) in 
          (tail_1019, next_idxs_1020)) else (let next_idxs_1020 :=
            array_upd next_idxs_1020 (@cast _ uint32 _ (n_1018)) (array_index (
                next_idxs_1020) (@cast _ uint32 _ (array_index (tail_1019) (
                    @cast _ uint32 _ (rq_1017))))) in 
          let next_idxs_1020 :=
            array_upd next_idxs_1020 (@cast _ uint32 _ (array_index (
                  tail_1019) (@cast _ uint32 _ (rq_1017)))) (n_1018) in 
          let tail_1019 :=
            array_upd tail_1019 (@cast _ uint32 _ (rq_1017)) (n_1018) in 
          (tail_1019, next_idxs_1020)) in 
      (tail_1019, next_idxs_1020)) else ((tail_1019, next_idxs_1020)) in 
  Clist ((tail_1019, next_idxs_1020)).

Definition clist_pop_head
  (x_1021 : clist_t)
  (rq_1022 : runqueue_id_t)
  : (clist_t × (option int8)) :=
  let 'RunqueueId (rq_1023) :=
    rq_1022 in 
  let 'Clist ((tail_1024, next_idxs_1025)) :=
    x_1021 in 
  let out_1026 : (option int8) :=
    @None int8 in 
  let '(tail_1024, next_idxs_1025, out_1026) :=
    if (array_index (tail_1024) (@cast _ uint32 _ (rq_1023))) =.? (
      sentinel_v):bool then ((tail_1024, next_idxs_1025, out_1026)) else (
      let head_1027 : int8 :=
        array_index (next_idxs_1025) (@cast _ uint32 _ (array_index (
              tail_1024) (@cast _ uint32 _ (rq_1023)))) in 
      let '(tail_1024, next_idxs_1025) :=
        if (head_1027) =.? (array_index (tail_1024) (@cast _ uint32 _ (
              rq_1023))):bool then (let tail_1024 :=
            array_upd tail_1024 (@cast _ uint32 _ (rq_1023)) (sentinel_v) in 
          (tail_1024, next_idxs_1025)) else (let next_idxs_1025 :=
            array_upd next_idxs_1025 (@cast _ uint32 _ (array_index (
                  tail_1024) (@cast _ uint32 _ (rq_1023)))) (array_index (
                next_idxs_1025) (@cast _ uint32 _ (head_1027))) in 
          (tail_1024, next_idxs_1025)) in 
      let next_idxs_1025 :=
        array_upd next_idxs_1025 (@cast _ uint32 _ (head_1027)) (sentinel_v) in 
      let out_1026 :=
        @Some int8 (head_1027) in 
      (tail_1024, next_idxs_1025, out_1026)) in 
  (Clist ((tail_1024, next_idxs_1025)), out_1026).

Definition clist_peek_head
  (x_1028 : clist_t)
  (rq_1029 : runqueue_id_t)
  : (option int8) :=
  let 'RunqueueId (rq_1030) :=
    rq_1029 in 
  let 'Clist ((tail_1031, next_idxs_1032)) :=
    x_1028 in 
  (if ((array_index (tail_1031) (@cast _ uint32 _ (rq_1030))) =.? (
        sentinel_v)):bool then (@None int8) else (@Some int8 (array_index (
          next_idxs_1032) (@cast _ uint32 _ (array_index (tail_1031) (
              @cast _ uint32 _ (rq_1030))))))).

Definition clist_advance
  (x_1033 : clist_t)
  (rq_1034 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1035) :=
    rq_1034 in 
  let 'Clist ((tail_1036, next_idxs_1037)) :=
    x_1033 in 
  let '(tail_1036) :=
    if (array_index (tail_1036) (@cast _ uint32 _ (rq_1035))) !=.? (
      sentinel_v):bool then (let tail_1036 :=
        array_upd tail_1036 (@cast _ uint32 _ (rq_1035)) (array_index (
            next_idxs_1037) (@cast _ uint32 _ (array_index (tail_1036) (
                @cast _ uint32 _ (rq_1035))))) in 
      (tail_1036)) else ((tail_1036)) in 
  Clist ((tail_1036, next_idxs_1037)).

Inductive run_queue_t :=
| RunQueue : (int32 × clist_t) -> run_queue_t.

Definition runqueue_new  : run_queue_t :=
  RunQueue ((@repr WORDSIZE32 0, clist_new )).

Definition runqueue_add
  (y_1038 : run_queue_t)
  (n_1039 : thread_id_t)
  (rq_1040 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1041) :=
    rq_1040 in 
  let 'RunQueue ((bitcache_1042, queues_1043)) :=
    y_1038 in 
  let bitcache_1042 :=
    (bitcache_1042) .| ((@repr WORDSIZE32 1) shift_left (@cast _ uint32 _ (
          rq_u8_1041))) in 
  let queues_1043 :=
    clist_push (queues_1043) (n_1039) (rq_1040) in 
  RunQueue ((bitcache_1042, queues_1043)).

Definition runqueue_del
  (y_1044 : run_queue_t)
  (n_1045 : thread_id_t)
  (rq_1046 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1047) :=
    rq_1046 in 
  let 'RunQueue ((bitcache_1048, queues_1049)) :=
    y_1044 in 
  let '(queues_1050, popped_1051) :=
    clist_pop_head (queues_1049) (rq_1046) in 
  let '(bitcache_1048) :=
    if clist_is_empty (queues_1050) (rq_1046):bool then (let bitcache_1048 :=
        (bitcache_1048) .& (not ((@repr WORDSIZE32 1) shift_left (
              @cast _ uint32 _ (rq_u8_1047)))) in 
      (bitcache_1048)) else ((bitcache_1048)) in 
  RunQueue ((bitcache_1048, queues_1050)).

Definition runqueue_ffs (val_1052 : int32) : int32 :=
  (pub_u32 (uint32_bits_v)) .- (pub_uint32_leading_zeros (val_1052)).

Definition runqueue_get_next (y_1053 : run_queue_t) : (option int8) :=
  let 'RunQueue ((bitcache_1054, queues_1055)) :=
    y_1053 in 
  let rq_ffs_1056 : int32 :=
    runqueue_ffs ((bitcache_1054)) in 
  let out_1057 : (option int8) :=
    @None int8 in 
  let '(out_1057) :=
    if (rq_ffs_1056) >.? (@repr WORDSIZE32 0):bool then (
      let rq_1058 : runqueue_id_t :=
        RunqueueId (@cast _ uint8 _ ((rq_ffs_1056) .- (@repr WORDSIZE32 1))) in 
      let out_1057 :=
        clist_peek_head (queues_1055) (rq_1058) in 
      (out_1057)) else ((out_1057)) in 
  out_1057.

Definition runqueue_advance
  (y_1059 : run_queue_t)
  (rq_1060 : runqueue_id_t)
  : run_queue_t :=
  let 'RunQueue ((bitcache_1061, queues_1062)) :=
    y_1059 in 
  let queues_1062 :=
    clist_advance (queues_1062) (rq_1060) in 
  RunQueue ((bitcache_1061, queues_1062)).

