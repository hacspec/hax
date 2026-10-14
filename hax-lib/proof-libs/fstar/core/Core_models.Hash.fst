module Core_models.Hash
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

/// See [`std::hash::BuildHasherDefault`]
type t_BuildHasherDefault (v_H: Type0) =
  | BuildHasherDefault : Core_models.Marker.t_PhantomData v_H -> t_BuildHasherDefault v_H

/// See [`std::hash::BuildHasherDefault::new`]
let impl_1__new (#v_H: Type0) (_: Prims.unit) : t_BuildHasherDefault v_H =
  BuildHasherDefault (Core_models.Marker.PhantomData <: Core_models.Marker.t_PhantomData v_H)
  <:
  t_BuildHasherDefault v_H

/// See [`std::default::Default`] for [`BuildHasherDefault`]
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5 (#v_H: Type0) : Core_models.Default.t_Default (t_BuildHasherDefault v_H) =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_BuildHasherDefault v_H) -> true);
    f_default = fun (_: Prims.unit) -> impl_1__new #v_H ()
  }

/// See [`std::cmp::PartialEq`] for [`BuildHasherDefault`]
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6 (#v_H: Type0)
    : Core_models.Cmp.t_PartialEq (t_BuildHasherDefault v_H) (t_BuildHasherDefault v_H) =
  {
    f_eq_pre = (fun (self: t_BuildHasherDefault v_H) (other: t_BuildHasherDefault v_H) -> true);
    f_eq_post
    =
    (fun (self: t_BuildHasherDefault v_H) (other: t_BuildHasherDefault v_H) (out: bool) -> true);
    f_eq = fun (self: t_BuildHasherDefault v_H) (other: t_BuildHasherDefault v_H) -> true
  }

/// See [`std::cmp::Eq`] for [`BuildHasherDefault`]
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7 (#v_H: Type0) : Core_models.Cmp.t_Eq (t_BuildHasherDefault v_H) =
  { _super_i0 = FStar.Tactics.Typeclasses.solve }

/// See [`std::hash::Hasher`]
class t_Hasher (v_Self: Type0) = {
  f_finish_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_finish_post:v_Self -> u64 -> Type0;
  f_finish:x0: v_Self -> Prims.Pure u64 (f_finish_pre x0) (fun result -> f_finish_post x0 result);
  f_write_pre:self_: v_Self -> bytes: t_Slice u8 -> pred: Type0{true ==> pred};
  f_write_post:v_Self -> t_Slice u8 -> v_Self -> Type0;
  f_write:x0: v_Self -> x1: t_Slice u8
    -> Prims.Pure v_Self (f_write_pre x0 x1) (fun result -> f_write_post x0 x1 result)
}

let write_u8_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: u8)
    : v_H =
  let h:v_H =
    f_write #v_H
      #FStar.Tactics.Typeclasses.solve
      h
      ((let list = [i] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
          Rust_primitives.Hax.array_of_list 1 list)
        <:
        t_Slice u8)
  in
  h

let write_u16_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: u16)
    : v_H =
  let h:v_H =
    f_write #v_H
      #FStar.Tactics.Typeclasses.solve
      h
      ((let list = [cast (i <: u16) <: u8; cast (i >>! mk_i32 8 <: u16) <: u8] in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice u8)
  in
  h

let write_u32_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: u32)
    : v_H =
  let h:v_H =
    f_write #v_H
      #FStar.Tactics.Typeclasses.solve
      h
      ((let list =
            [
              cast (i <: u32) <: u8;
              cast (i >>! mk_i32 8 <: u32) <: u8;
              cast (i >>! mk_i32 16 <: u32) <: u8;
              cast (i >>! mk_i32 24 <: u32) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 4);
          Rust_primitives.Hax.array_of_list 4 list)
        <:
        t_Slice u8)
  in
  h

let write_u64_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: u64)
    : v_H =
  let h:v_H =
    f_write #v_H
      #FStar.Tactics.Typeclasses.solve
      h
      ((let list =
            [
              cast (i <: u64) <: u8;
              cast (i >>! mk_i32 8 <: u64) <: u8;
              cast (i >>! mk_i32 16 <: u64) <: u8;
              cast (i >>! mk_i32 24 <: u64) <: u8;
              cast (i >>! mk_i32 32 <: u64) <: u8;
              cast (i >>! mk_i32 40 <: u64) <: u8;
              cast (i >>! mk_i32 48 <: u64) <: u8;
              cast (i >>! mk_i32 56 <: u64) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 8);
          Rust_primitives.Hax.array_of_list 8 list)
        <:
        t_Slice u8)
  in
  h

let write_u128_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: u128)
    : v_H =
  let h:v_H =
    f_write #v_H
      #FStar.Tactics.Typeclasses.solve
      h
      ((let list =
            [
              cast (i <: u128) <: u8; cast (i >>! mk_i32 8 <: u128) <: u8;
              cast (i >>! mk_i32 16 <: u128) <: u8; cast (i >>! mk_i32 24 <: u128) <: u8;
              cast (i >>! mk_i32 32 <: u128) <: u8; cast (i >>! mk_i32 40 <: u128) <: u8;
              cast (i >>! mk_i32 48 <: u128) <: u8; cast (i >>! mk_i32 56 <: u128) <: u8;
              cast (i >>! mk_i32 64 <: u128) <: u8; cast (i >>! mk_i32 72 <: u128) <: u8;
              cast (i >>! mk_i32 80 <: u128) <: u8; cast (i >>! mk_i32 88 <: u128) <: u8;
              cast (i >>! mk_i32 96 <: u128) <: u8; cast (i >>! mk_i32 104 <: u128) <: u8;
              cast (i >>! mk_i32 112 <: u128) <: u8; cast (i >>! mk_i32 120 <: u128) <: u8
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 16);
          Rust_primitives.Hax.array_of_list 16 list)
        <:
        t_Slice u8)
  in
  h

let write_usize_le
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (h: v_H)
      (i: usize)
    : v_H =
  let h:v_H = write_u64_le #v_H h (cast (i <: usize) <: u64) in
  h

/// See [`std::hash::Hash`]
class t_Hash (v_Self: Type0) = {
  f_hash_pre:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> self_: v_Self -> state: v_H
    -> pred: Type0{true ==> pred};
  f_hash_post:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> v_Self -> v_H -> v_H -> Type0;
  f_hash:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> x0: v_Self -> x1: v_H
    -> Prims.Pure v_H (f_hash_pre #v_H #i1 x0 x1) (fun result -> f_hash_post #v_H #i1 x0 x1 result)
}

class t_HasherDefaults (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Hasher v_Self;
  f_write_u8_pre:self_: v_Self -> i: u8 -> pred: Type0{true ==> pred};
  f_write_u8_post:v_Self -> u8 -> v_Self -> Type0;
  f_write_u8:x0: v_Self -> x1: u8
    -> Prims.Pure v_Self (f_write_u8_pre x0 x1) (fun result -> f_write_u8_post x0 x1 result);
  f_write_u16_pre:self_: v_Self -> i: u16 -> pred: Type0{true ==> pred};
  f_write_u16_post:v_Self -> u16 -> v_Self -> Type0;
  f_write_u16:x0: v_Self -> x1: u16
    -> Prims.Pure v_Self (f_write_u16_pre x0 x1) (fun result -> f_write_u16_post x0 x1 result);
  f_write_u32_pre:self_: v_Self -> i: u32 -> pred: Type0{true ==> pred};
  f_write_u32_post:v_Self -> u32 -> v_Self -> Type0;
  f_write_u32:x0: v_Self -> x1: u32
    -> Prims.Pure v_Self (f_write_u32_pre x0 x1) (fun result -> f_write_u32_post x0 x1 result);
  f_write_u64_pre:self_: v_Self -> i: u64 -> pred: Type0{true ==> pred};
  f_write_u64_post:v_Self -> u64 -> v_Self -> Type0;
  f_write_u64:x0: v_Self -> x1: u64
    -> Prims.Pure v_Self (f_write_u64_pre x0 x1) (fun result -> f_write_u64_post x0 x1 result);
  f_write_u128_pre:self_: v_Self -> i: u128 -> pred: Type0{true ==> pred};
  f_write_u128_post:v_Self -> u128 -> v_Self -> Type0;
  f_write_u128:x0: v_Self -> x1: u128
    -> Prims.Pure v_Self (f_write_u128_pre x0 x1) (fun result -> f_write_u128_post x0 x1 result);
  f_write_usize_pre:self_: v_Self -> i: usize -> pred: Type0{true ==> pred};
  f_write_usize_post:v_Self -> usize -> v_Self -> Type0;
  f_write_usize:x0: v_Self -> x1: usize
    -> Prims.Pure v_Self (f_write_usize_pre x0 x1) (fun result -> f_write_usize_post x0 x1 result);
  f_write_i8_pre:self_: v_Self -> i: i8 -> pred: Type0{true ==> pred};
  f_write_i8_post:v_Self -> i8 -> v_Self -> Type0;
  f_write_i8:x0: v_Self -> x1: i8
    -> Prims.Pure v_Self (f_write_i8_pre x0 x1) (fun result -> f_write_i8_post x0 x1 result);
  f_write_i16_pre:self_: v_Self -> i: i16 -> pred: Type0{true ==> pred};
  f_write_i16_post:v_Self -> i16 -> v_Self -> Type0;
  f_write_i16:x0: v_Self -> x1: i16
    -> Prims.Pure v_Self (f_write_i16_pre x0 x1) (fun result -> f_write_i16_post x0 x1 result);
  f_write_i32_pre:self_: v_Self -> i: i32 -> pred: Type0{true ==> pred};
  f_write_i32_post:v_Self -> i32 -> v_Self -> Type0;
  f_write_i32:x0: v_Self -> x1: i32
    -> Prims.Pure v_Self (f_write_i32_pre x0 x1) (fun result -> f_write_i32_post x0 x1 result);
  f_write_i64_pre:self_: v_Self -> i: i64 -> pred: Type0{true ==> pred};
  f_write_i64_post:v_Self -> i64 -> v_Self -> Type0;
  f_write_i64:x0: v_Self -> x1: i64
    -> Prims.Pure v_Self (f_write_i64_pre x0 x1) (fun result -> f_write_i64_post x0 x1 result);
  f_write_i128_pre:self_: v_Self -> i: i128 -> pred: Type0{true ==> pred};
  f_write_i128_post:v_Self -> i128 -> v_Self -> Type0;
  f_write_i128:x0: v_Self -> x1: i128
    -> Prims.Pure v_Self (f_write_i128_pre x0 x1) (fun result -> f_write_i128_post x0 x1 result);
  f_write_isize_pre:self_: v_Self -> i: isize -> pred: Type0{true ==> pred};
  f_write_isize_post:v_Self -> isize -> v_Self -> Type0;
  f_write_isize:x0: v_Self -> x1: isize
    -> Prims.Pure v_Self (f_write_isize_pre x0 x1) (fun result -> f_write_isize_post x0 x1 result);
  f_write_length_prefix_pre:self_: v_Self -> len: usize -> pred: Type0{true ==> pred};
  f_write_length_prefix_post:v_Self -> usize -> v_Self -> Type0;
  f_write_length_prefix:x0: v_Self -> x1: usize
    -> Prims.Pure v_Self
        (f_write_length_prefix_pre x0 x1)
        (fun result -> f_write_length_prefix_post x0 x1 result);
  f_write_str_pre:self_: v_Self -> s: string -> pred: Type0{true ==> pred};
  f_write_str_post:v_Self -> string -> v_Self -> Type0;
  f_write_str:x0: v_Self -> x1: string
    -> Prims.Pure v_Self (f_write_str_pre x0 x1) (fun result -> f_write_str_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_HasherDefaults v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8 (#v_H: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
    : t_HasherDefaults v_H =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_write_u8_pre = (fun (self: v_H) (i: u8) -> true);
    f_write_u8_post = (fun (self: v_H) (i: u8) (out: v_H) -> true);
    f_write_u8
    =
    (fun (self: v_H) (i: u8) ->
        let self:v_H = write_u8_le #v_H self i in
        self);
    f_write_u16_pre = (fun (self: v_H) (i: u16) -> true);
    f_write_u16_post = (fun (self: v_H) (i: u16) (out: v_H) -> true);
    f_write_u16
    =
    (fun (self: v_H) (i: u16) ->
        let self:v_H = write_u16_le #v_H self i in
        self);
    f_write_u32_pre = (fun (self: v_H) (i: u32) -> true);
    f_write_u32_post = (fun (self: v_H) (i: u32) (out: v_H) -> true);
    f_write_u32
    =
    (fun (self: v_H) (i: u32) ->
        let self:v_H = write_u32_le #v_H self i in
        self);
    f_write_u64_pre = (fun (self: v_H) (i: u64) -> true);
    f_write_u64_post = (fun (self: v_H) (i: u64) (out: v_H) -> true);
    f_write_u64
    =
    (fun (self: v_H) (i: u64) ->
        let self:v_H = write_u64_le #v_H self i in
        self);
    f_write_u128_pre = (fun (self: v_H) (i: u128) -> true);
    f_write_u128_post = (fun (self: v_H) (i: u128) (out: v_H) -> true);
    f_write_u128
    =
    (fun (self: v_H) (i: u128) ->
        let self:v_H = write_u128_le #v_H self i in
        self);
    f_write_usize_pre = (fun (self: v_H) (i: usize) -> true);
    f_write_usize_post = (fun (self: v_H) (i: usize) (out: v_H) -> true);
    f_write_usize
    =
    (fun (self: v_H) (i: usize) ->
        let self:v_H = write_usize_le #v_H self i in
        self);
    f_write_i8_pre = (fun (self: v_H) (i: i8) -> true);
    f_write_i8_post = (fun (self: v_H) (i: i8) (out: v_H) -> true);
    f_write_i8
    =
    (fun (self: v_H) (i: i8) ->
        let self:v_H = write_u8_le #v_H self (cast (i <: i8) <: u8) in
        self);
    f_write_i16_pre = (fun (self: v_H) (i: i16) -> true);
    f_write_i16_post = (fun (self: v_H) (i: i16) (out: v_H) -> true);
    f_write_i16
    =
    (fun (self: v_H) (i: i16) ->
        let self:v_H = write_u16_le #v_H self (cast (i <: i16) <: u16) in
        self);
    f_write_i32_pre = (fun (self: v_H) (i: i32) -> true);
    f_write_i32_post = (fun (self: v_H) (i: i32) (out: v_H) -> true);
    f_write_i32
    =
    (fun (self: v_H) (i: i32) ->
        let self:v_H = write_u32_le #v_H self (cast (i <: i32) <: u32) in
        self);
    f_write_i64_pre = (fun (self: v_H) (i: i64) -> true);
    f_write_i64_post = (fun (self: v_H) (i: i64) (out: v_H) -> true);
    f_write_i64
    =
    (fun (self: v_H) (i: i64) ->
        let self:v_H = write_u64_le #v_H self (cast (i <: i64) <: u64) in
        self);
    f_write_i128_pre = (fun (self: v_H) (i: i128) -> true);
    f_write_i128_post = (fun (self: v_H) (i: i128) (out: v_H) -> true);
    f_write_i128
    =
    (fun (self: v_H) (i: i128) ->
        let self:v_H = write_u128_le #v_H self (cast (i <: i128) <: u128) in
        self);
    f_write_isize_pre = (fun (self: v_H) (i: isize) -> true);
    f_write_isize_post = (fun (self: v_H) (i: isize) (out: v_H) -> true);
    f_write_isize
    =
    (fun (self: v_H) (i: isize) ->
        let self:v_H = write_usize_le #v_H self (cast (i <: isize) <: usize) in
        self);
    f_write_length_prefix_pre = (fun (self: v_H) (len: usize) -> true);
    f_write_length_prefix_post = (fun (self: v_H) (len: usize) (out: v_H) -> true);
    f_write_length_prefix
    =
    (fun (self: v_H) (len: usize) ->
        let self:v_H = write_usize_le #v_H self len in
        self);
    f_write_str_pre = (fun (self: v_H) (s: string) -> true);
    f_write_str_post = (fun (self: v_H) (s: string) (out: v_H) -> true);
    f_write_str
    =
    fun (self: v_H) (s: string) ->
      let self:v_H =
        f_write #v_H
          #FStar.Tactics.Typeclasses.solve
          self
          (Rust_primitives.String.str_as_bytes s <: t_Slice u8)
      in
      let self:v_H = write_u8_le #v_H self (mk_u8 255) in
      self
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_u8: t_Hash u8 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u8)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u8)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: u8)
      (state: v_H)
      ->
      let state:v_H = f_write_u8 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_u16: t_Hash u16 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u16)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u16)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: u16)
      (state: v_H)
      ->
      let state:v_H = f_write_u16 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_u32: t_Hash u32 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u32)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u32)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: u32)
      (state: v_H)
      ->
      let state:v_H = f_write_u32 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_u64: t_Hash u64 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u64)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u64)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: u64)
      (state: v_H)
      ->
      let state:v_H = f_write_u64 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_u128: t_Hash u128 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u128)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: u128)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: u128)
      (state: v_H)
      ->
      let state:v_H = f_write_u128 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_usize: t_Hash usize =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: usize)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: usize)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: usize)
      (state: v_H)
      ->
      let state:v_H = f_write_usize #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_i8: t_Hash i8 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i8)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i8)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: i8)
      (state: v_H)
      ->
      let state:v_H = f_write_i8 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_i16: t_Hash i16 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i16)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i16)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: i16)
      (state: v_H)
      ->
      let state:v_H = f_write_i16 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_i32: t_Hash i32 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i32)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i32)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: i32)
      (state: v_H)
      ->
      let state:v_H = f_write_i32 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_i64: t_Hash i64 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i64)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i64)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: i64)
      (state: v_H)
      ->
      let state:v_H = f_write_i64 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_i128: t_Hash i128 =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i128)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: i128)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: i128)
      (state: v_H)
      ->
      let state:v_H = f_write_i128 #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_isize: t_Hash isize =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: isize)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: isize)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: isize)
      (state: v_H)
      ->
      let state:v_H = f_write_isize #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

/// See [`std::hash::Hash`] for `bool`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_bool: t_Hash bool =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: bool)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: bool)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: bool)
      (state: v_H)
      ->
      let state:v_H =
        f_write_u8 #v_H #FStar.Tactics.Typeclasses.solve state (cast (self <: bool) <: u8)
      in
      state
  }

/// See [`std::hash::Hash`] for `str`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_str: t_Hash string =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: string)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: string)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: string)
      (state: v_H)
      ->
      let state:v_H = f_write_str #v_H #FStar.Tactics.Typeclasses.solve state self in
      state
  }

/// See [`std::hash::Hash`] for `()`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_Hash_for_tuple_: t_Hash Prims.unit =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: Prims.unit)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
        (self: Prims.unit)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hasher v_H)
      (self: Prims.unit)
      (state: v_H)
      ->
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27
      (#v_T #v_B: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
    : t_Hash (v_T & v_B) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher v_S)
        (self: (v_T & v_B))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher v_S)
        (self: (v_T & v_B))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher v_S)
      (self: (v_T & v_B))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28
      (#v_T #v_B #v_C: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
    : t_Hash (v_T & v_B & v_C) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hasher v_S)
        (self: (v_T & v_B & v_C))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hasher v_S)
        (self: (v_T & v_B & v_C))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hasher v_S)
      (self: (v_T & v_B & v_C))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29
      (#v_T #v_B #v_C #v_D: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
    : t_Hash (v_T & v_B & v_C & v_D) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30
      (#v_T #v_B #v_C #v_D #v_E: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
    : t_Hash (v_T & v_B & v_C & v_D & v_E) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31
      (#v_T #v_B #v_C #v_D #v_E #v_F: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G #v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hash v_H)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      let state:v_S = f_hash #v_H #FStar.Tactics.Typeclasses.solve #v_S self._8 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G #v_H #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hash v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hash v_I)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      let state:v_S = f_hash #v_H #FStar.Tactics.Typeclasses.solve #v_S self._8 state in
      let state:v_S = f_hash #v_I #FStar.Tactics.Typeclasses.solve #v_S self._9 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G #v_H #v_I #v_J: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hash v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hash v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hash v_J)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i10: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i10: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i10: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      let state:v_S = f_hash #v_H #FStar.Tactics.Typeclasses.solve #v_S self._8 state in
      let state:v_S = f_hash #v_I #FStar.Tactics.Typeclasses.solve #v_S self._9 state in
      let state:v_S = f_hash #v_J #FStar.Tactics.Typeclasses.solve #v_S self._10 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G #v_H #v_I #v_J #v_K: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hash v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hash v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hash v_J)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i10: t_Hash v_K)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i11: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i11: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i11: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      let state:v_S = f_hash #v_H #FStar.Tactics.Typeclasses.solve #v_S self._8 state in
      let state:v_S = f_hash #v_I #FStar.Tactics.Typeclasses.solve #v_S self._9 state in
      let state:v_S = f_hash #v_J #FStar.Tactics.Typeclasses.solve #v_S self._10 state in
      let state:v_S = f_hash #v_K #FStar.Tactics.Typeclasses.solve #v_S self._11 state in
      state
  }

/// See [`std::hash::Hash`] for tuples
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37
      (#v_T #v_B #v_C #v_D #v_E #v_F #v_G #v_H #v_I #v_J #v_K #v_L: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_B)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hash v_C)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: t_Hash v_D)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i4: t_Hash v_E)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i5: t_Hash v_F)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i6: t_Hash v_G)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i7: t_Hash v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i8: t_Hash v_I)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i9: t_Hash v_J)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i10: t_Hash v_K)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i11: t_Hash v_L)
    : t_Hash (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K & v_L) =
  {
    f_hash_pre
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i12: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K & v_L))
        (state: v_S)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_S: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i12: t_Hasher v_S)
        (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K & v_L))
        (state: v_S)
        (out: v_S)
        ->
        true);
    f_hash
    =
    fun
      (#v_S: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i12: t_Hasher v_S)
      (self: (v_T & v_B & v_C & v_D & v_E & v_F & v_G & v_H & v_I & v_J & v_K & v_L))
      (state: v_S)
      ->
      let state:v_S = f_hash #v_T #FStar.Tactics.Typeclasses.solve #v_S self._1 state in
      let state:v_S = f_hash #v_B #FStar.Tactics.Typeclasses.solve #v_S self._2 state in
      let state:v_S = f_hash #v_C #FStar.Tactics.Typeclasses.solve #v_S self._3 state in
      let state:v_S = f_hash #v_D #FStar.Tactics.Typeclasses.solve #v_S self._4 state in
      let state:v_S = f_hash #v_E #FStar.Tactics.Typeclasses.solve #v_S self._5 state in
      let state:v_S = f_hash #v_F #FStar.Tactics.Typeclasses.solve #v_S self._6 state in
      let state:v_S = f_hash #v_G #FStar.Tactics.Typeclasses.solve #v_S self._7 state in
      let state:v_S = f_hash #v_H #FStar.Tactics.Typeclasses.solve #v_S self._8 state in
      let state:v_S = f_hash #v_I #FStar.Tactics.Typeclasses.solve #v_S self._9 state in
      let state:v_S = f_hash #v_J #FStar.Tactics.Typeclasses.solve #v_S self._10 state in
      let state:v_S = f_hash #v_K #FStar.Tactics.Typeclasses.solve #v_S self._11 state in
      let state:v_S = f_hash #v_L #FStar.Tactics.Typeclasses.solve #v_S self._12 state in
      state
  }

/// See [`std::hash::BuildHasher`]
class t_BuildHasher (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]f_Hasher:Type0;
  f_Hasher_i0:t_Hasher f_Hasher;
  f_build_hasher_pre:self_: v_Self -> pred: Type0{true ==> pred};
  f_build_hasher_post:v_Self -> f_Hasher -> Type0;
  f_build_hasher:x0: v_Self
    -> Prims.Pure f_Hasher (f_build_hasher_pre x0) (fun result -> f_build_hasher_post x0 result)
}

class t_HashDefaults (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_Hash v_Self;
  f_hash_slice_pre:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> data: t_Slice v_Self -> state: v_H
    -> pred: Type0{true ==> pred};
  f_hash_slice_post:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> t_Slice v_Self -> v_H -> v_H -> Type0;
  f_hash_slice:#v_H: Type0 -> {| i1: t_Hasher v_H |} -> x0: t_Slice v_Self -> x1: v_H
    -> Prims.Pure v_H
        (f_hash_slice_pre #v_H #i1 x0 x1)
        (fun result -> f_hash_slice_post #v_H #i1 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_HashDefaults v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: Core_models.Default.t_Default v_H)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
    : t_BuildHasher (t_BuildHasherDefault v_H) =
  {
    f_Hasher = v_H;
    f_Hasher_i0 = FStar.Tactics.Typeclasses.solve;
    f_build_hasher_pre = (fun (self: t_BuildHasherDefault v_H) -> true);
    f_build_hasher_post = (fun (self: t_BuildHasherDefault v_H) (out: v_H) -> true);
    f_build_hasher
    =
    fun (self: t_BuildHasherDefault v_H) ->
      Core_models.Default.f_default #v_H #FStar.Tactics.Typeclasses.solve ()
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
    : t_HashDefaults v_T =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_hash_slice_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
        (data: t_Slice v_T)
        (state: v_H)
        ->
        true);
    f_hash_slice_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
        (data: t_Slice v_T)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash_slice
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
      (data: t_Slice v_T)
      (state: v_H)
      ->
      let state:v_H =
        Rust_primitives.Hax.Folds.fold_range (mk_usize 0)
          (Rust_primitives.Slice.slice_length #v_T data <: usize)
          (fun state temp_1_ ->
              let state:v_H = state in
              let _:usize = temp_1_ in
              true)
          state
          (fun state i ->
              let state:v_H = state in
              let i:usize = i in
              f_hash #v_T
                #FStar.Tactics.Typeclasses.solve
                #v_H
                (Rust_primitives.Slice.slice_index #v_T data i <: v_T)
                state
              <:
              v_H)
      in
      state
  }

/// See [`std::hash::Hash`] for `[T]`
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_Hash v_T)
    : t_Hash (t_Slice v_T) =
  {
    f_hash_pre
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
        (self: t_Slice v_T)
        (state: v_H)
        ->
        true);
    f_hash_post
    =
    (fun
        (#v_H: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
        (self: t_Slice v_T)
        (state: v_H)
        (out: v_H)
        ->
        true);
    f_hash
    =
    fun
      (#v_H: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hasher v_H)
      (self: t_Slice v_T)
      (state: v_H)
      ->
      let state:v_H =
        f_write_length_prefix #v_H
          #FStar.Tactics.Typeclasses.solve
          state
          (Rust_primitives.Slice.slice_length #v_T self <: usize)
      in
      let state:v_H = f_hash_slice #v_T #FStar.Tactics.Typeclasses.solve #v_H self state in
      state
  }

class t_BuildHasherDefaults (v_Self: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_i0:t_BuildHasher v_Self;
  f_hash_one_pre:
      #v_T: Type0 ->
      {| i1: t_Hash v_T |} ->
      {| i2: t_Hasher (_super_i0).f_Hasher |} ->
      self_: v_Self ->
      x: v_T
    -> pred: Type0{true ==> pred};
  f_hash_one_post:
      #v_T: Type0 ->
      {| i1: t_Hash v_T |} ->
      {| i2: t_Hasher (_super_i0).f_Hasher |} ->
      v_Self ->
      v_T ->
      u64
    -> Type0;
  f_hash_one:
      #v_T: Type0 ->
      {| i1: t_Hash v_T |} ->
      {| i2: t_Hasher (_super_i0).f_Hasher |} ->
      x0: v_Self ->
      x1: v_T
    -> Prims.Pure u64
        (f_hash_one_pre #v_T #i1 #i2 x0 x1)
        (fun result -> f_hash_one_post #v_T #i1 #i2 x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let _ = fun (v_Self:Type0) {|i: t_BuildHasherDefaults v_Self|} -> i._super_i0

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10 (#v_B: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i0: t_BuildHasher v_B)
    : t_BuildHasherDefaults v_B =
  {
    _super_i0 = FStar.Tactics.Typeclasses.solve;
    f_hash_one_pre
    =
    (fun
        (#v_T: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_T)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher i0.f_Hasher)
        (self: v_B)
        (x: v_T)
        ->
        true);
    f_hash_one_post
    =
    (fun
        (#v_T: Type0)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_T)
        (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher i0.f_Hasher)
        (self: v_B)
        (x: v_T)
        (out: u64)
        ->
        true);
    f_hash_one
    =
    fun
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_Hash v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: t_Hasher i0.f_Hasher)
      (self: v_B)
      (x: v_T)
      ->
      let hasher = f_build_hasher #v_B #FStar.Tactics.Typeclasses.solve self in
      let hasher = f_hash #v_T #FStar.Tactics.Typeclasses.solve #i0.f_Hasher x hasher in
      f_finish #i0.f_Hasher #FStar.Tactics.Typeclasses.solve hasher
  }
