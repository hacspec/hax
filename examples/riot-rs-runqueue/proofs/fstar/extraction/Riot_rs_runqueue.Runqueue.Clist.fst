module Riot_rs_runqueue.Runqueue.Clist
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

type t_CList (#v_N_QUEUES: usize) (#v_N_THREADS: usize) = {
  f_tail:t_Array u8 v_N_QUEUES;
  f_next_idxs:t_Array u8 v_N_THREADS
}

let impl__sentinel (#v_N_QUEUES #v_N_THREADS: usize) : u8 = 255uy

let impl__new (#v_N_QUEUES #v_N_THREADS: usize) : t_CList v_N_QUEUES v_N_THREADS =
  {
    f_tail = Rust_primitives.Hax.repeat (impl__sentinel <: u8) v_N_QUEUES;
    f_next_idxs = Rust_primitives.Hax.repeat (impl__sentinel <: u8) v_N_THREADS
  }

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
  let self, output:(t_CList v_N_QUEUES v_N_THREADS & Prims.unit) =
    if (self.f_next_idxs.[ cast n <: usize ] <: u8) =. (impl__sentinel <: u8)
    then
      if (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)
      then
        let self:t_CList v_N_QUEUES v_N_THREADS =
          {
            self with
            f_tail
            =
            Rust_primitives.Hax.update_at (self.f_tail <: t_CList v_N_QUEUES v_N_THREADS)
              (cast rq <: usize)
              n
          }
        in
        let self:t_CList v_N_QUEUES v_N_THREADS =
          {
            self with
            f_next_idxs
            =
            Rust_primitives.Hax.update_at (self.f_next_idxs <: t_CList v_N_QUEUES v_N_THREADS)
              (cast n <: usize)
              n
          }
        in
        self, ()
      else
        let self:t_CList v_N_QUEUES v_N_THREADS =
          {
            self with
            f_next_idxs
            =
            Rust_primitives.Hax.update_at (self.f_next_idxs <: t_CList v_N_QUEUES v_N_THREADS)
              (cast n <: usize)
              (self.f_next_idxs.[ cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize ] <: u8)
          }
        in
        let self:t_CList v_N_QUEUES v_N_THREADS =
          {
            self with
            f_next_idxs
            =
            Rust_primitives.Hax.update_at (self.f_next_idxs <: t_CList v_N_QUEUES v_N_THREADS)
              (cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize)
              n
          }
        in
        let self:t_CList v_N_QUEUES v_N_THREADS =
          {
            self with
            f_tail
            =
            Rust_primitives.Hax.update_at (self.f_tail <: t_CList v_N_QUEUES v_N_THREADS)
              (cast rq <: usize)
              n
          }
        in
        self, ()
    else self, ()
  in
  self

let impl__pop_head (#v_N_QUEUES #v_N_THREADS: usize) (self: t_CList v_N_QUEUES v_N_THREADS) (rq: u8)
    : (t_CList v_N_QUEUES v_N_THREADS & Core.Option.t_Option u8) =
  let self, output:(t_CList v_N_QUEUES v_N_THREADS & Core.Option.t_Option u8) =
    if (self.f_tail.[ cast rq <: usize ] <: u8) =. (impl__sentinel <: u8)
    then self, Core.Option.Option_None
    else
      let head:u8 = self.f_next_idxs.[ cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize ] in
      let self:t_CList v_N_QUEUES v_N_THREADS =
        if head =. (self.f_tail.[ cast rq <: usize ] <: u8)
        then
          let self:t_CList v_N_QUEUES v_N_THREADS =
            {
              self with
              f_tail
              =
              Rust_primitives.Hax.update_at (self.f_tail <: t_CList v_N_QUEUES v_N_THREADS)
                (cast rq <: usize)
                (impl__sentinel <: u8)
            }
          in
          self
        else
          let self:t_CList v_N_QUEUES v_N_THREADS =
            {
              self with
              f_next_idxs
              =
              Rust_primitives.Hax.update_at (self.f_next_idxs <: t_CList v_N_QUEUES v_N_THREADS)
                (cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize)
                (self.f_next_idxs.[ cast head <: usize ] <: u8)
            }
          in
          self
      in
      let self:t_CList v_N_QUEUES v_N_THREADS =
        {
          self with
          f_next_idxs
          =
          Rust_primitives.Hax.update_at (self.f_next_idxs <: t_CList v_N_QUEUES v_N_THREADS)
            (cast head <: usize)
            (impl__sentinel <: u8)
        }
      in
      self, Core.Option.Option_Some head
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
  let self, output:(t_CList v_N_QUEUES v_N_THREADS & Prims.unit) =
    if (self.f_tail.[ cast rq <: usize ] <: u8) <>. (impl__sentinel <: u8)
    then
      let self:t_CList v_N_QUEUES v_N_THREADS =
        {
          self with
          f_tail
          =
          Rust_primitives.Hax.update_at (self.f_tail <: t_CList v_N_QUEUES v_N_THREADS)
            (cast rq <: usize)
            (self.f_next_idxs.[ cast (self.f_tail.[ cast rq <: usize ] <: u8) <: usize ] <: u8)
        }
      in
      self, ()
    else self, ()
  in
  self