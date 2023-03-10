#![no_std]
use hacspec_lib::*;

const U32_BITS: usize = 4 * 8;
const N_QUEUES: usize = 20;
const N_THREADS: usize = 30;
const SENTINEL: u8 = 0xFFu8;

#[derive(Clone, Copy, Debug)]
pub struct RunqueueId(pub u8);
#[derive(Clone, Copy, Debug)]
pub struct ThreadId(pub u8);

public_bytes!(Tail, N_QUEUES);
public_bytes!(NextIds, N_THREADS);

#[derive(Clone, Copy, Debug)]
pub struct Clist(Tail, NextIds);

pub fn clist_new() -> Clist {
    let mut tail = Tail::new();
    for i in 0..tail.len() {
        tail[i] = SENTINEL;
    }
    let mut next_idxs = NextIds::new();
    for i in 0..next_idxs.len() {
        next_idxs[i] = SENTINEL;
    }
    Clist(tail, next_idxs)
}

pub fn clist_is_empty(x: &Clist, rq: RunqueueId) -> bool {
    let RunqueueId(rq) = rq;
    let Clist(tail, _next_ids) = x;
    tail[rq as usize] == SENTINEL
}

pub fn clist_push(x: Clist, n: ThreadId, rq: RunqueueId) -> Clist {
    let RunqueueId(rq) = rq;
    let ThreadId(n) = n;
    // assert!(n < SENTINEL);
    let Clist(mut tail, mut next_idxs) = x;
    if next_idxs[n as usize] == SENTINEL {
        if tail[rq as usize] == SENTINEL {
            // rq is empty, link both tail and n.next to n
            tail[rq as usize] = n;
            next_idxs[n as usize] = n;
        } else {
            // rq has an entry already, so
            // 1. n.next = old_tail.next ("first" in list)
            next_idxs[n as usize] = next_idxs[tail[rq as usize] as usize];
            // 2. old_tail.next = n
            next_idxs[tail[rq as usize] as usize] = n;
            // 3. tail = n
            tail[rq as usize] = n;
        }
    }
    Clist(tail, next_idxs)
}

pub fn clist_pop_head(x: Clist, rq: RunqueueId) -> (Clist, Option<u8>) {
    let RunqueueId(rq) = rq;
    let Clist(mut tail, mut next_idxs) = x;
    let mut out: Option<u8> = Option::<u8>::None;
    if tail[rq as usize] == SENTINEL {
        // rq is empty, do nothing
    } else {
        let head = next_idxs[tail[rq as usize] as usize];
        if head == tail[rq as usize] {
            // rq's tail bites itself, so there's only one entry.
            // so, clear tail.
            tail[rq as usize] = SENTINEL;
            // rq is now empty
        } else {
            // rq has multiple entries,
            // so set tail.next to head.next (second in list)
            next_idxs[tail[rq as usize] as usize] = next_idxs[head as usize];
        }

        // now clear head's next value
        next_idxs[head as usize] = SENTINEL;
        out = Option::<u8>::Some(head);
    }
    (Clist(tail, next_idxs), out)
}

pub fn clist_peek_head(x: &Clist, rq: RunqueueId) -> Option<u8> {
    let RunqueueId(rq) = rq;
    let Clist(tail, next_idxs) = x;
    if tail[rq as usize] == SENTINEL {
        Option::<u8>::None
    } else {
        Option::<u8>::Some(next_idxs[tail[rq as usize] as usize])
    }
}

pub fn clist_advance(x: Clist, rq: RunqueueId) -> Clist {
    let RunqueueId(rq) = rq;
    let Clist(mut tail, next_idxs) = x;
    if tail[rq as usize] != SENTINEL {
        tail[rq as usize] = next_idxs[tail[rq as usize] as usize];
    }
    Clist(tail, next_idxs)
}

#[derive(Clone, Copy, Debug)]
pub struct RunQueue(u32, Clist);

pub fn runqueue_new() -> RunQueue {
    RunQueue(0u32, clist_new())
}

pub fn runqueue_add(y: RunQueue, n: ThreadId, rq: RunqueueId) -> RunQueue {
    // debug_assert!(n < N_THREADS);
    // debug_assert!(rq < N_QUEUES);
    let RunqueueId(rq_u8) = rq;
    let RunQueue(mut bitcache, mut queues) = y;
    bitcache = bitcache | (1u32 << (rq_u8 as u32));
    queues = clist_push(queues, n, rq);
    RunQueue(bitcache, queues)
}

pub fn runqueue_del(y: RunQueue, _n: ThreadId, rq: RunqueueId) -> RunQueue {
    // debug_assert!(n < N_THREADS);
    // debug_assert!(rq < N_QUEUES);
    let RunqueueId(rq_u8) = rq;
    let RunQueue(mut bitcache, queues) = y;
    let (queues, _popped) = clist_pop_head(queues, rq);
    // assert_eq!(popped, Some(n as u8));
    if clist_is_empty(&queues, rq) {
        bitcache = bitcache & !(1u32 << (rq_u8 as u32));
    }
    RunQueue(bitcache, queues)
}

pub fn runqueue_ffs(val: u32) -> u32 {
    U32_BITS as u32 - val.leading_zeros()
}

/// get pid that should run next
/// returns the next runnable thread of
/// the runqueue with the highest index
pub fn runqueue_get_next(y: &RunQueue) -> Option<u8> {
    let RunQueue(bitcache, queues) = y;
    let rq_ffs = runqueue_ffs(bitcache.clone());
    let mut out = Option::<u8>::None;
    if rq_ffs > 0u32 {
        let rq = RunqueueId((rq_ffs - 1u32) as u8);
        out = clist_peek_head(queues, rq)
    }
    out
}

/// advance runqueue number rq
/// (this is used to "yield" to another thread of *the same* priority)
pub fn runqueue_advance(y: RunQueue, rq: RunqueueId) -> RunQueue {
    // debug_assert!(rq < N_QUEUES);
    let RunQueue(bitcache, mut queues) = y;
    queues = clist_advance(queues, rq);
    RunQueue(bitcache, queues)
}
