module Riot_rs_runqueue.Runqueue.Clist
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_CList (#v_N_QUEUES: usize) (#v_N_THREADS: usize) = {
  f_tail:t_Array u8 v_N_QUEUES;
  f_next_idxs:t_Array u8 v_N_THREADS
}

let impl__new (#v_N_QUEUES #v_N_THREADS: usize) : t_CList v_N_QUEUES v_N_THREADS =
  {
    f_tail = Rust_primitives.Hax.repeat (impl__sentinel <: u8) v_N_QUEUES;
    f_next_idxs = Rust_primitives.Hax.repeat (impl__sentinel <: u8) v_N_THREADS
  }

let impl__sentinel (#v_N_QUEUES #v_N_THREADS: usize) : u8 = 255uy

let impl__is_empty (#v_N_QUEUES #v_N_THREADS: usize) (self: t_CList v_N_QUEUES v_N_THREADS) (rq: u8)
    : bool = (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)

let impl__push (#v_N_QUEUES #v_N_THREADS: usize) (self: t_CList v_N_QUEUES v_N_THREADS) (n rq: u8)
    : t_CList v_N_QUEUES v_N_THREADS =
  let _:Prims.unit =
    if ~.(n <. (impl__sentinel <: u8) <: bool)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: n < Self::sentinel()"

          <:
          Rust_primitives.Hax.t_Never)
  in
  let output:Prims.unit =
    if (self.f_next_idxs.[ cast n <: usize ] <: u8) =. (impl__sentinel <: u8)
    then
      if (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)
      then
        let _:Prims.unit = Rust_primitives.Hax.failure "" "(self.f_tail[cast(rq)] = n)" in
        let _:Prims.unit = Rust_primitives.Hax.failure "" "(self.f_next_idxs[cast(n)] = n)" in
        ()
      else
        let _:Prims.unit =
          Rust_primitives.Hax.failure ""
            "(self.f_next_idxs[cast(n)] = core::ops::index::Index::index(\n        proj_riot_rs_runqueue::runqueue::clist::f_next_idxs(self),\n        cast(core::ops::index::Index::index(\n            proj_riot_rs_runqueue::runqueue::clist::f_tail(self),\n            cast(rq),\n        )),\n    ))"

        in
        let _:Prims.unit =
          Rust_primitives.Hax.failure ""
            "(self.f_next_idxs[cast(core::ops::index::Index::index(\n        proj_riot_rs_runqueue::runqueue::clist::f_tail(self),\n        cast(rq),\n    ))] = n)"

        in
        let _:Prims.unit = Rust_primitives.Hax.failure "" "(self.f_tail[cast(rq)] = n)" in
        ()
  in
  self

let impl__pop_head (#v_N_QUEUES #v_N_THREADS: usize) (self: t_CList v_N_QUEUES v_N_THREADS) (rq: u8)
    : (t_CList v_N_QUEUES v_N_THREADS & Core.Option.t_Option u8) =
  let output:Core.Option.t_Option u8 =
    if (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)
    then Core.Option.Option_None
    else
      let head:u8 = self.f_next_idxs.[ cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize ] in
      let _:Prims.unit =
        if head =. (self.f_tail.[ cast rq <: usize ] <: u8)
        then
          let _:Prims.unit =
            Rust_primitives.Hax.failure ""
              "(self.f_tail[cast(rq)] = riot_rs_runqueue::runqueue::clist::impl__sentinel())"
          in
          ()
        else
          let _:Prims.unit =
            Rust_primitives.Hax.failure ""
              "(self.f_next_idxs[cast(core::ops::index::Index::index(\n        proj_riot_rs_runqueue::runqueue::clist::f_tail(self),\n        cast(rq),\n    ))] = core::ops::index::Index::index(\n        proj_riot_rs_runqueue::runqueue::clist::f_next_idxs(self),\n        cast(head),\n    ))"

          in
          ()
      in
      let _:Prims.unit =
        Rust_primitives.Hax.failure ""
          "(self.f_next_idxs[cast(head)] = riot_rs_runqueue::runqueue::clist::impl__sentinel())"
      in
      Core.Option.Option_Some head
  in
  self, output

let impl__peek_head
      (#v_N_QUEUES #v_N_THREADS: usize)
      (self: t_CList v_N_QUEUES v_N_THREADS)
      (rq: u8)
    : Core.Option.t_Option u8 =
  if (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)
  then Core.Option.Option_None
  else
    Core.Option.Option_Some
    self.f_next_idxs.[ cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize ]

let impl__advance (#v_N_QUEUES #v_N_THREADS: usize) (self: t_CList v_N_QUEUES v_N_THREADS) (rq: u8)
    : t_CList v_N_QUEUES v_N_THREADS =
  let output:Prims.unit =
    if (self.f_tail.[ cast rq <: usize ] <: u8) <>. (impl__sentinel <: u8)
    then
      let _:Prims.unit =
        Rust_primitives.Hax.failure ""
          "(self.f_tail[cast(rq)] = core::ops::index::Index::index(\n        proj_riot_rs_runqueue::runqueue::clist::f_next_idxs(self),\n        cast(core::ops::index::Index::index(\n            proj_riot_rs_runqueue::runqueue::clist::f_tail(self),\n            cast(rq),\n        )),\n    ))"

      in
      ()
  in
  self