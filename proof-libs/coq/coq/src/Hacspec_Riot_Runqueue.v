(** This file was automatically generated using Hacspec **)
Set Warnings "-notation-overridden,-ambiguous-paths".
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
| Clist : (tail_t '× next_ids_t) -> clist_t.

Definition clist_new  : clist_t :=
  let tail_1347 : tail_t :=
    array_new_ (default : int8) (n_queues_v) in 
  let tail_1347 :=
    foldi (usize 0) (array_len (tail_1347)) (fun i_1348 tail_1347 =>
      let tail_1347 :=
        array_upd tail_1347 (i_1348) (sentinel_v) in 
      (tail_1347))
    tail_1347 in 
  let next_idxs_1349 : next_ids_t :=
    array_new_ (default : int8) (n_threads_v) in 
  let next_idxs_1349 :=
    foldi (usize 0) (array_len (next_idxs_1349)) (fun i_1350 next_idxs_1349 =>
      let next_idxs_1349 :=
        array_upd next_idxs_1349 (i_1350) (sentinel_v) in 
      (next_idxs_1349))
    next_idxs_1349 in 
  Clist ((tail_1347, next_idxs_1349)).

Definition clist_is_empty (x_1351 : clist_t) (rq_1352 : runqueue_id_t) : bool :=
  let 'RunqueueId (rq_1353) :=
    rq_1352 in 
  let 'Clist ((tail_1354, next_ids_1355)) :=
    x_1351 in 
  (array_index (tail_1354) (@cast _ uint32 _ (rq_1353))) =.? (sentinel_v).

Definition clist_push
  (x_1356 : clist_t)
  (n_1357 : thread_id_t)
  (rq_1358 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1359) :=
    rq_1358 in 
  let 'ThreadId (n_1360) :=
    n_1357 in 
  let 'Clist ((tail_1361, next_idxs_1362)) :=
    x_1356 in 
  let '(tail_1361, next_idxs_1362) :=
    if (array_index (next_idxs_1362) (@cast _ uint32 _ (n_1360))) =.? (
      sentinel_v):bool then (let '(tail_1361, next_idxs_1362) :=
        if (array_index (tail_1361) (@cast _ uint32 _ (rq_1359))) =.? (
          sentinel_v):bool then (let tail_1361 :=
            array_upd tail_1361 (@cast _ uint32 _ (rq_1359)) (n_1360) in 
          let next_idxs_1362 :=
            array_upd next_idxs_1362 (@cast _ uint32 _ (n_1360)) (n_1360) in 
          (tail_1361, next_idxs_1362)) else (let next_idxs_1362 :=
            array_upd next_idxs_1362 (@cast _ uint32 _ (n_1360)) (array_index (
                next_idxs_1362) (@cast _ uint32 _ (array_index (tail_1361) (
                    @cast _ uint32 _ (rq_1359))))) in 
          let next_idxs_1362 :=
            array_upd next_idxs_1362 (@cast _ uint32 _ (array_index (
                  tail_1361) (@cast _ uint32 _ (rq_1359)))) (n_1360) in 
          let tail_1361 :=
            array_upd tail_1361 (@cast _ uint32 _ (rq_1359)) (n_1360) in 
          (tail_1361, next_idxs_1362)) in 
      (tail_1361, next_idxs_1362)) else ((tail_1361, next_idxs_1362)) in 
  Clist ((tail_1361, next_idxs_1362)).

Definition clist_pop_head
  (x_1363 : clist_t)
  (rq_1364 : runqueue_id_t)
  : (clist_t '× (option int8)) :=
  let 'RunqueueId (rq_1365) :=
    rq_1364 in 
  let 'Clist ((tail_1366, next_idxs_1367)) :=
    x_1363 in 
  let out_1368 : (option int8) :=
    @None int8 in 
  let '(tail_1366, next_idxs_1367, out_1368) :=
    if (array_index (tail_1366) (@cast _ uint32 _ (rq_1365))) =.? (
      sentinel_v):bool then ((tail_1366, next_idxs_1367, out_1368)) else (
      let head_1369 : int8 :=
        array_index (next_idxs_1367) (@cast _ uint32 _ (array_index (
              tail_1366) (@cast _ uint32 _ (rq_1365)))) in 
      let '(tail_1366, next_idxs_1367) :=
        if (head_1369) =.? (array_index (tail_1366) (@cast _ uint32 _ (
              rq_1365))):bool then (let tail_1366 :=
            array_upd tail_1366 (@cast _ uint32 _ (rq_1365)) (sentinel_v) in 
          (tail_1366, next_idxs_1367)) else (let next_idxs_1367 :=
            array_upd next_idxs_1367 (@cast _ uint32 _ (array_index (
                  tail_1366) (@cast _ uint32 _ (rq_1365)))) (array_index (
                next_idxs_1367) (@cast _ uint32 _ (head_1369))) in 
          (tail_1366, next_idxs_1367)) in 
      let next_idxs_1367 :=
        array_upd next_idxs_1367 (@cast _ uint32 _ (head_1369)) (sentinel_v) in 
      let out_1368 :=
        @Some int8 (head_1369) in 
      (tail_1366, next_idxs_1367, out_1368)) in 
  (Clist ((tail_1366, next_idxs_1367)), out_1368).

Definition clist_peek_head
  (x_1370 : clist_t)
  (rq_1371 : runqueue_id_t)
  : (option int8) :=
  let 'RunqueueId (rq_1372) :=
    rq_1371 in 
  let 'Clist ((tail_1373, next_idxs_1374)) :=
    x_1370 in 
  (if ((array_index (tail_1373) (@cast _ uint32 _ (rq_1372))) =.? (
        sentinel_v)):bool then (@None int8) else (@Some int8 (array_index (
          next_idxs_1374) (@cast _ uint32 _ (array_index (tail_1373) (
              @cast _ uint32 _ (rq_1372))))))).

Definition clist_advance
  (x_1375 : clist_t)
  (rq_1376 : runqueue_id_t)
  : clist_t :=
  let 'RunqueueId (rq_1377) :=
    rq_1376 in 
  let 'Clist ((tail_1378, next_idxs_1379)) :=
    x_1375 in 
  let '(tail_1378) :=
    if (array_index (tail_1378) (@cast _ uint32 _ (rq_1377))) !=.? (
      sentinel_v):bool then (let tail_1378 :=
        array_upd tail_1378 (@cast _ uint32 _ (rq_1377)) (array_index (
            next_idxs_1379) (@cast _ uint32 _ (array_index (tail_1378) (
                @cast _ uint32 _ (rq_1377))))) in 
      (tail_1378)) else ((tail_1378)) in 
  Clist ((tail_1378, next_idxs_1379)).

Inductive run_queue_t :=
| RunQueue : (int32 '× clist_t) -> run_queue_t.

Definition runqueue_new  : run_queue_t :=
  RunQueue ((@repr WORDSIZE32 0, clist_new )).

Definition runqueue_add
  (y_1380 : run_queue_t)
  (n_1381 : thread_id_t)
  (rq_1382 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1383) :=
    rq_1382 in 
  let 'RunQueue ((bitcache_1384, queues_1385)) :=
    y_1380 in 
  let bitcache_1384 :=
    (bitcache_1384) .| ((@repr WORDSIZE32 1) shift_left (@cast _ uint32 _ (
          rq_u8_1383))) in 
  let queues_1385 :=
    clist_push (queues_1385) (n_1381) (rq_1382) in 
  RunQueue ((bitcache_1384, queues_1385)).

Definition runqueue_del
  (y_1386 : run_queue_t)
  (n_1387 : thread_id_t)
  (rq_1388 : runqueue_id_t)
  : run_queue_t :=
  let 'RunqueueId (rq_u8_1389) :=
    rq_1388 in 
  let 'RunQueue ((bitcache_1390, queues_1391)) :=
    y_1386 in 
  let '(queues_1392, popped_1393) :=
    clist_pop_head (queues_1391) (rq_1388) in 
  let '(bitcache_1390) :=
    if clist_is_empty (queues_1392) (rq_1388):bool then (let bitcache_1390 :=
        (bitcache_1390) .& (not ((@repr WORDSIZE32 1) shift_left (
              @cast _ uint32 _ (rq_u8_1389)))) in 
      (bitcache_1390)) else ((bitcache_1390)) in 
  RunQueue ((bitcache_1390, queues_1392)).

Definition runqueue_ffs (val_1394 : int32) : int32 :=
  (pub_u32 (uint32_bits_v)) .- (pub_uint32_leading_zeros (val_1394)).

Definition runqueue_get_next (y_1395 : run_queue_t) : (option int8) :=
  let 'RunQueue ((bitcache_1396, queues_1397)) :=
    y_1395 in 
  let rq_ffs_1398 : int32 :=
    runqueue_ffs ((bitcache_1396)) in 
  let out_1399 : (option int8) :=
    @None int8 in 
  let '(out_1399) :=
    if (rq_ffs_1398) >.? (@repr WORDSIZE32 0):bool then (
      let rq_1400 : runqueue_id_t :=
        RunqueueId (@cast _ uint8 _ ((rq_ffs_1398) .- (@repr WORDSIZE32 1))) in 
      let out_1399 :=
        clist_peek_head (queues_1397) (rq_1400) in 
      (out_1399)) else ((out_1399)) in 
  out_1399.

Definition runqueue_advance
  (y_1401 : run_queue_t)
  (rq_1402 : runqueue_id_t)
  : run_queue_t :=
  let 'RunQueue ((bitcache_1403, queues_1404)) :=
    y_1401 in 
  let queues_1404 :=
    clist_advance (queues_1404) (rq_1402) in 
  RunQueue ((bitcache_1403, queues_1404)).

