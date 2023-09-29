module Lob_backend
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let t_OrderId = u64

type t_Side =
  | Side_Buy : t_Side
  | Side_Sell : t_Side

let t_Price = u64

let t_Quantity = u64

type t_Order = {
  f_id:u64;
  f_side:t_Side;
  f_price:u64;
  f_quantity:u64
}

type t_Match = {
  f_bid_id:u64;
  f_ask_id:u64;
  f_price:u64;
  f_quantity:u64
}

let is_match (order other: t_Order) : bool =
  order.f_quantity >. 0uL && other.f_quantity >. 0uL && order.f_side <>. other.f_side &&
  (order.f_side =. Side_Buy && order.f_price >=. other.f_price ||
  order.f_side =. Side_Sell && order.f_price <=. other.f_price)

let try_match_under_impl (self other: t_Order) : Core.Option.t_Option t_Match =
  if is_match self other
  then
    let quantity:u64 = Core.Cmp.min self.f_quantity other.f_quantity in
    let bid_id, ask_id:(u64 & u64) =
      if self.f_side =. Side_Buy then self.f_id, other.f_id else other.f_id, self.f_id
    in
    Core.Option.Option_Some
    ({ f_bid_id = bid_id; f_ask_id = ask_id; f_price = self.f_price; f_quantity = quantity })
  else Core.Option.Option_None

instance impl_2: Core.Cmp.t_Ord t_Order =
  {
    f_cmp
    =
    fun (self: t_Order) (other: t_Order) ->
      Core.Cmp.then_under_impl (Core.Cmp.f_cmp self.f_price other.f_price)
        (Core.Cmp.f_cmp self.f_id other.f_id)
  }
  
instance impl_1: Core.Cmp.t_PartialOrd t_Order t_Order =
  {
    __constraint_Rhs_t_PartialEq = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp
    =
    fun (self: t_Order) (other: t_Order) -> Core.Option.Option_Some (Core.Cmp.f_cmp self other)
  }

instance impl_3: Core.Convert.t_From t_Order (Core.Cmp.t_Reverse t_Order) =
  { f_from = fun (other: Core.Cmp.t_Reverse t_Order) -> other.Core.Cmp._0 }

instance impl_4: Core.Convert.t_From (Core.Cmp.t_Reverse t_Order) t_Order =
  { f_from = fun (value: t_Order) -> Core.Cmp.Reverse value }

type t_OrderBook = {
  f_bids:Alloc.Collections.Binary_heap.t_BinaryHeap t_Order;
  f_asks:Alloc.Collections.Binary_heap.t_BinaryHeap (Core.Cmp.t_Reverse t_Order)
}

let new_under_impl_5: t_OrderBook =
  {
    f_bids = Alloc.Collections.Binary_heap.new_under_impl_9;
    f_asks = Alloc.Collections.Binary_heap.new_under_impl_9
  }

unfold type accType v_T = (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
  t_Order &
  Alloc.Collections.Binary_heap.t_BinaryHeap v_T)

let process_order
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7622056925298315612: Core.Marker.t_Sized v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i8042177119965911781:
          Core.Convert.t_Into v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()]
          i9328066132609353763:
          Core.Convert.t_From v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8880357094332718191: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9024736138855468982: Core.Clone.t_Clone v_T)
      (order: t_Order)
      (other_side: Alloc.Collections.Binary_heap.t_BinaryHeap v_T)
    : (Alloc.Collections.Binary_heap.t_BinaryHeap v_T &
      (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
  let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global = Alloc.Vec.new_under_impl in
  let done:bool = false in
  let whatever: accType v_T = (done, matches, order, other_side) in
  let whatever: accType v_T =
  // let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
  //   t_Order &
  //   Alloc.Collections.Binary_heap.t_BinaryHeap v_T) =
    Core.Iter.Traits.Iterator.Iterator.fold #accType  (Core.Iter.Traits.Collect.IntoIterator.into_iter ({
              Core.Ops.Range.f_start = 1sz;
              Core.Ops.Range.f_end = Alloc.Collections.Binary_heap.len_under_impl_10 other_side
            }))
      whatever
      (fun (done, matches, order, other_side) v__i ->
          if ~.done
          then
            match
              Core.Option.and_then_under_impl (Alloc.Collections.Binary_heap.peek_under_impl_10 other_side
                  )
                (fun other ->
                    try_match_under_impl (Core.Convert.f_into (Core.Clone.clone other))
                      order)
            with
            | Core.Option.Option_Some m ->
              let order:t_Order = { order with f_quantity = order.f_quantity -. m.f_quantity } in
              let tmp0, out:(Alloc.Collections.Binary_heap.t_BinaryHeap v_T &
                Core.Option.t_Option v_T) =
                Alloc.Collections.Binary_heap.pop_under_impl_9 other_side
              in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T = tmp0 in
              let hoist1//:(Alloc.Collections.Binary_heap.t_BinaryHeap v_T & Core.Option.t_Option v_T)
              =
                out
              in
              let hoist2:v_T = Core.Option.unwrap_under_impl hoist1 in
              let (other: t_Order):t_Order = Core.Convert.f_into hoist2 in
              let other:t_Order = { other with f_quantity = other.f_quantity -. m.f_quantity } in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T =
                if other.f_quantity >. 0uL
                then
                  let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T =
                    Alloc.Collections.Binary_heap.push_under_impl_9 other_side
                      (Core.Convert.f_from (Core.Clone.clone other))
                  in
                  other_side
                else other_side
              in
              let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global =
                Alloc.Vec.push_under_impl_1 matches m
              in
              done, matches, order, other_side
            | _ ->
              let done:bool = true in
              done, matches, order, other_side
          else done, matches, order, other_side)
  in
  admit ()

let _ = 
  let (done, matches, order, other_side) = whatever in
  let output:(Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order) =
    matches,
    (if order.f_quantity >. 0uL then Core.Option.Option_Some order else Core.Option.Option_None)
  in
  other_side, output


let add_order_under_impl_5 (self: t_OrderBook) (order: t_Order)
    : (t_OrderBook & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global) =
  let _:Prims.unit =
    if ~.(order.f_quantity >. 0uL)
    then
      Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: order.quantity > 0")
  in
  let _:Prims.unit =
    if ~.(order.f_price >. 0uL)
    then Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: order.price > 0")
  in
  let self, output:(t_OrderBook & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global) =
    match order.f_side with
    | Side_Buy  ->
      let tmp0, out:(Alloc.Collections.Binary_heap.t_BinaryHeap (Core.Cmp.t_Reverse t_Order) &
        (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
        process_order order self.f_asks
      in
      let self:t_OrderBook = { self with f_asks = tmp0 } in
      let matches, opt_remaining_bid
      // :(Alloc.Collections.Binary_heap.t_BinaryHeap
      //   (Core.Cmp.t_Reverse t_Order) &
      //   (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
      =
        out
      in
      let self:t_OrderBook =
        match opt_remaining_bid with
        | Core.Option.Option_Some remaining_bid ->
          let self:t_OrderBook =
            {
              self with
              f_bids = Alloc.Collections.Binary_heap.push_under_impl_9 self.f_bids remaining_bid
            }
          in
          self
        | _ -> self
      in
      self, matches
    | Side_Sell  ->
      let tmp0, out:(Alloc.Collections.Binary_heap.t_BinaryHeap t_Order &
        (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
        process_order order self.f_bids
      in
      let self:t_OrderBook = { self with f_bids = tmp0 } in
      let matches, opt_remaining_ask
        // :(Alloc.Collections.Binary_heap.t_BinaryHeap t_Order &
        // (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
        =
        out
      in
      let self:t_OrderBook =
        match opt_remaining_ask with
        | Core.Option.Option_Some remaining_ask ->
          let self:t_OrderBook =
            {
              self with
              f_asks
              =
              Alloc.Collections.Binary_heap.push_under_impl_9 self.f_asks
                (Core.Cmp.Reverse remaining_ask)
            }
          in
          self
        | _ -> self
      in
      self, matches
  in
  self, output

instance collect_tc_slice_vec (t: eqtype): collect_tc (slice t) (Alloc.Vec.t_Vec t Alloc.Alloc.t_Global)
  = magic ()


let list_bids_under_impl_5 (self: t_OrderBook) : Alloc.Vec.t_Vec t_Order Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.cloned (Alloc.Collections.Binary_heap.iter_under_impl_10
            self.f_bids))

let list_asks_under_impl_5 (self: t_OrderBook) : Alloc.Vec.t_Vec t_Order Alloc.Alloc.t_Global =
  Core.Iter.Traits.Iterator.Iterator.collect (Core.Iter.Traits.Iterator.Iterator.map (Core.Iter.Traits.Iterator.Iterator.cloned
            (Alloc.Collections.Binary_heap.iter_under_impl_10 self.f_asks))
        (fun (Core.Cmp.Reverse { Core.Cmp._0 = order }) -> order))

