module Lob_backend
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Side =
  | Side_Buy : t_Side
  | Side_Sell : t_Side

type t_Match = {
  f_bid_id:u64;
  f_ask_id:u64;
  f_price:u64;
  f_quantity:u64
}

type t_Order = {
  f_id:u64;
  f_side:t_Side;
  f_price:u64;
  f_quantity:u64
}

let is_match (order other: t_Order) : bool =
  order.f_quantity >. 0uL && other.f_quantity >. 0uL && order.f_side <>. other.f_side &&
  (order.f_side =. (Side_Buy <: t_Side) && order.f_price >=. other.f_price ||
  order.f_side =. (Side_Sell <: t_Side) && order.f_price <=. other.f_price)

let impl__Order__try_match (self other: t_Order) : Core.Option.t_Option t_Match =
  if is_match self other
  then
    let quantity:u64 = Core.Cmp.min self.f_quantity other.f_quantity in
    let bid_id, ask_id:(u64 & u64) =
      if self.f_side =. (Side_Buy <: t_Side)
      then self.f_id, other.f_id <: (u64 & u64)
      else other.f_id, self.f_id <: (u64 & u64)
    in
    Core.Option.Option_Some
    ({ f_bid_id = bid_id; f_ask_id = ask_id; f_price = self.f_price; f_quantity = quantity }
      <:
      t_Match)
    <:
    Core.Option.t_Option t_Match
  else Core.Option.Option_None <: Core.Option.t_Option t_Match

let process_order
      (#v_T: Type)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii0: Core.Marker.t_Sized v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii1: Core.Convert.t_Into v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii2: Core.Convert.t_From v_T t_Order)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii3: Core.Cmp.t_Ord v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] ii4: Core.Clone.t_Clone v_T)
      (order: t_Order)
      (other_side: Alloc.Collections.Binary_heap.t_BinaryHeap v_T)
    : (Alloc.Collections.Binary_heap.t_BinaryHeap v_T &
      (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)) =
  let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global = Alloc.Vec.impl__new () in
  let done:bool = false in
  let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
    t_Order &
    Alloc.Collections.Binary_heap.t_BinaryHeap v_T) =
    Core.Iter.Traits.Iterator.f_fold (Core.Iter.Traits.Collect.f_into_iter ({
              Core.Ops.Range.f_start = sz 1;
              Core.Ops.Range.f_end = Alloc.Collections.Binary_heap.impl_10__len other_side <: usize
            }
            <:
            Core.Ops.Range.t_Range usize)
        <:
        Core.Ops.Range.t_Range usize)
      (done, matches, order, other_side
        <:
        (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
          Alloc.Collections.Binary_heap.t_BinaryHeap v_T))
      (fun temp_0_ v__i ->
          let done, matches, order, other_side:(bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global &
            t_Order &
            Alloc.Collections.Binary_heap.t_BinaryHeap v_T) =
            temp_0_
          in
          let v__i:usize = v__i in
          if ~.done <: bool
          then
            match
              Core.Option.impl__and_then (Alloc.Collections.Binary_heap.impl_10__peek other_side
                  <:
                  Core.Option.t_Option v_T)
                (fun other ->
                    let other:v_T = other in
                    impl__Order__try_match (Core.Convert.f_into (Core.Clone.f_clone other <: v_T)
                        <:
                        t_Order)
                      order
                    <:
                    Core.Option.t_Option t_Match)
              <:
              Core.Option.t_Option t_Match
            with
            | Core.Option.Option_Some m ->
              let order:t_Order =
                { order with f_quantity = order.f_quantity -! m.f_quantity } <: t_Order
              in
              let tmp0, out:(Alloc.Collections.Binary_heap.t_BinaryHeap v_T &
                Core.Option.t_Option v_T) =
                Alloc.Collections.Binary_heap.impl_9__pop other_side
              in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T = tmp0 in
              let hoist1:Core.Option.t_Option v_T = out in
              let hoist2:v_T = Core.Option.impl__unwrap hoist1 in
              let (other: t_Order):t_Order = Core.Convert.f_into hoist2 in
              let other:t_Order =
                { other with f_quantity = other.f_quantity -! m.f_quantity } <: t_Order
              in
              let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T =
                if other.f_quantity >. 0uL
                then
                  let other_side:Alloc.Collections.Binary_heap.t_BinaryHeap v_T =
                    Alloc.Collections.Binary_heap.impl_9__push other_side
                      (Core.Convert.f_from (Core.Clone.f_clone other <: t_Order) <: v_T)
                  in
                  other_side
                else other_side
              in
              let matches:Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global =
                Alloc.Vec.impl_1__push matches m
              in
              done, matches, order, other_side
              <:
              (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
                Alloc.Collections.Binary_heap.t_BinaryHeap v_T)
            | _ ->
              let done:bool = true in
              done, matches, order, other_side
              <:
              (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
                Alloc.Collections.Binary_heap.t_BinaryHeap v_T)
          else
            done, matches, order, other_side
            <:
            (bool & Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & t_Order &
              Alloc.Collections.Binary_heap.t_BinaryHeap v_T))
  in
  let hax_temp_output:(Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)
  =
    matches,
    (if order.f_quantity >. 0uL
      then Core.Option.Option_Some order <: Core.Option.t_Option t_Order
      else Core.Option.Option_None <: Core.Option.t_Option t_Order)
    <:
    (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order)
  in
  other_side, hax_temp_output
  <:
  (Alloc.Collections.Binary_heap.t_BinaryHeap v_T &
    (Alloc.Vec.t_Vec t_Match Alloc.Alloc.t_Global & Core.Option.t_Option t_Order))
