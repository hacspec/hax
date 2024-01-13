module Rust_primitives.Hax.Monomorphized_update_at

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range

let update_at_usize s i x = 
  update_at s i x

let update_at_range #n s i x = 
  let res = update_at s i x in
  admit(); // To be proved
  res
  
let update_at_range_to #n s i x =
  let res = update_at s i x in
  admit();
  res
  
let update_at_range_from #n s i x = 
  let res = update_at s i x in
  admit();
  res

let update_at_range_full s i x =
  let res = update_at s i x in
  admit();
  res


