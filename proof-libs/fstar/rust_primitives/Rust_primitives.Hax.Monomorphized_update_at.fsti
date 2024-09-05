module Rust_primitives.Hax.Monomorphized_update_at
#set-options "--z3rlimit 30"

/// Monomorphized versions of the `update_at` operator.

open Rust_primitives
open Rust_primitives.Hax
open Core.Ops.Range

let update_at_usize
  (#t: Type0)
  (s: t_Slice t)
  (i: usize {v i < Seq.length s})
  (x: t)
  : t_Array t (length s)
  = Seq.upd #t s (v i) x
  // : Pure (t_Array t (length s))
  //   (requires (v i < Seq.length s))
  //   (ensures (fun res -> res == Seq.upd s (v i) x))

val update_at_range #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_Range (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_start >= 0 /\ v i.f_start <= Seq.length s /\
               v i.f_end <= Seq.length s /\
               Seq.length x == v i.f_end - v i.f_start))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_start) == Seq.slice s 0 (v i.f_start) /\
                Seq.slice res (v i.f_start) (v i.f_end) == x /\
                Seq.slice res (v i.f_end) (Seq.length res) == Seq.slice s (v i.f_end) (Seq.length s)))

val update_at_range_to #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeTo (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (v i.f_end >= 0 /\ v i.f_end <= Seq.length s /\
               Seq.length x == v i.f_end))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_end) == x /\
                Seq.slice res (v i.f_end) (Seq.length res) == Seq.slice s (v i.f_end) (Seq.length s)))

val update_at_range_from #n
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeFrom (int_t n))
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires ( v i.f_start >= 0 /\ v i.f_start <= Seq.length s /\
                Seq.length x == Seq.length s - v i.f_start))
    (ensures (fun res ->
                Seq.slice res 0 (v i.f_start) == Seq.slice s 0 (v i.f_start) /\
                Seq.slice res (v i.f_start) (Seq.length res) == x))

val update_at_range_full
  (#t: Type0)
  (s: t_Slice t)
  (i: t_RangeFull)
  (x: t_Slice t)
  : Pure (t_Array t (length s))
    (requires (Seq.length x == Seq.length s))
    (ensures (fun res -> res == x))
