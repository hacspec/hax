module Core.Array.Rec_bundle_579704328
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_TryFromSliceError = | TryFromSliceError : Prims.unit -> t_TryFromSliceError

type t_Seq (v_T: Type0) = { f_v:Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Seq v_T) =
  {
    f_clone_pre = (fun (self: t_Seq v_T) -> true);
    f_clone_post = (fun (self: t_Seq v_T) (out: t_Seq v_T) -> true);
    f_clone
    =
    fun (self: t_Seq v_T) ->
      {
        f_v
        =
        Core.Clone.f_clone #(Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
          #FStar.Tactics.Typeclasses.solve
          self.f_v
      }
      <:
      t_Seq v_T
  }

type t_LIST (v_T: Type0) =
  | LIST_NIL : t_LIST v_T
  | LIST_CONS : v_T -> t_Seq v_T -> t_LIST v_T

let nil
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (_: Prims.unit)
    : t_Seq v_T = { f_v = Alloc.Vec.impl__new #v_T () } <: t_Seq v_T

type t_Slice (v_T: Type0) = { f_v:t_Seq v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Slice v_T) (t_Slice v_T) =
  {
    f_from_pre = (fun (x: t_Slice v_T) -> true);
    f_from_post = (fun (x: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_from
    =
    fun (x: t_Slice v_T) ->
      { f_v = { f_v = Alloc.Slice.impl__to_vec #v_T x } <: t_Seq v_T } <: t_Slice v_T
  }

type t_Array (v_T: Type0) (v_N: usize) = { f_v:t_Slice v_T }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Clone.t_Clone (t_Array v_T v_N) =
  {
    f_clone_pre = (fun (self: t_Array v_T v_N) -> true);
    f_clone_post = (fun (self: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_clone
    =
    fun (self: t_Array v_T v_N) ->
      { f_v = Core.Clone.f_clone #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve self.f_v }
      <:
      t_Array v_T v_N
  }

let cast
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (self: t_Array v_T v_N)
    : t_Slice v_T = self.f_v

type t_i128 = | C_i128 : Core.Base_interface.Int.t_I128 -> t_i128

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Clone.t_Clone t_i128 =
  {
    f_clone_pre = (fun (self: t_i128) -> true);
    f_clone_post = (fun (self: t_i128) (out: t_i128) -> true);
    f_clone
    =
    fun (self: t_i128) ->
      t_i128
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I128 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i128
  }

type t_i16 = | C_i16 : Core.Base_interface.Int.t_I16 -> t_i16

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Clone.t_Clone t_i16 =
  {
    f_clone_pre = (fun (self: t_i16) -> true);
    f_clone_post = (fun (self: t_i16) (out: t_i16) -> true);
    f_clone
    =
    fun (self: t_i16) ->
      t_i16
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I16 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i16
  }

type t_i32 = | C_i32 : Core.Base_interface.Int.t_I32 -> t_i32

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Clone.t_Clone t_i32 =
  {
    f_clone_pre = (fun (self: t_i32) -> true);
    f_clone_post = (fun (self: t_i32) (out: t_i32) -> true);
    f_clone
    =
    fun (self: t_i32) ->
      t_i32
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I32 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i32
  }

type t_i64 = | C_i64 : Core.Base_interface.Int.t_I64 -> t_i64

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Clone.t_Clone t_i64 =
  {
    f_clone_pre = (fun (self: t_i64) -> true);
    f_clone_post = (fun (self: t_i64) (out: t_i64) -> true);
    f_clone
    =
    fun (self: t_i64) ->
      t_i64
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i64
  }

type t_i8 = | C_i8 : Core.Base_interface.Int.t_I8 -> t_i8

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Clone.t_Clone t_i8 =
  {
    f_clone_pre = (fun (self: t_i8) -> true);
    f_clone_post = (fun (self: t_i8) (out: t_i8) -> true);
    f_clone
    =
    fun (self: t_i8) ->
      t_i8
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I8 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i8
  }

type t_isize = | C_isize : Core.Base_interface.Int.t_I64 -> t_isize

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Clone.t_Clone t_isize =
  {
    f_clone_pre = (fun (self: t_isize) -> true);
    f_clone_post = (fun (self: t_isize) (out: t_isize) -> true);
    f_clone
    =
    fun (self: t_isize) ->
      t_isize
      (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Convert.t_From t_isize t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: t_isize) -> true);
    f_from
    =
    fun (x: t_i64) ->
      t_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Convert.t_From t_i64 t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: t_i64) -> true);
    f_from
    =
    fun (x: t_isize) ->
      t_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i64
  }

type t_u128 = | C_u128 : Core.Base_interface.Int.t_U128 -> t_u128

let from_le715594649 (x: t_u128) : t_u128 = x

let to_le902648378 (self: t_u128) : t_u128 = self

type t_u16 = | C_u16 : Core.Base_interface.Int.t_U16 -> t_u16

let from_le793045973 (x: t_u16) : t_u16 = x

let to_le1012469456 (self: t_u16) : t_u16 = self

type t_u32 = | C_u32 : Core.Base_interface.Int.t_U32 -> t_u32

let from_le706338679 (x: t_u32) : t_u32 = x

let to_le724624277 (self: t_u32) : t_u32 = self

type t_u64 = | C_u64 : Core.Base_interface.Int.t_U64 -> t_u64

let from_le435089922 (x: t_u64) : t_u64 = x

let to_le2703875 (self: t_u64) : t_u64 = self

type t_u8 = | C_u8 : Core.Base_interface.Int.t_U8 -> t_u8

let from_le529489651 (x: t_u8) : t_u8 = x

let to_le523556665 (self: t_u8) : t_u8 = self

type t_usize = | C_usize : Core.Base_interface.Int.t_U64 -> t_usize

let from_le418743864 (x: t_usize) : t_usize = x

let to_le946822077 (self: t_usize) : t_usize = self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Convert.t_From t_usize t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: t_usize) -> true);
    f_from
    =
    fun (x: t_u64) ->
      t_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Convert.t_From t_u64 t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: t_u64) -> true);
    f_from
    =
    fun (x: t_usize) ->
      t_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u64
  }

class v_Sealed (v_Self: Type0) = { __marker_trait_v_Sealed:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: v_Sealed t_usize = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: v_Sealed (Core.Ops.Range.t_Range usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: v_Sealed (Core.Ops.Range.t_RangeTo usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: v_Sealed (Core.Ops.Range.t_RangeFrom usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: v_Sealed Core.Ops.Range.t_RangeFull = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: v_Sealed (Core.Ops.Range.t_RangeInclusive usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: v_Sealed (Core.Ops.Range.t_RangeToInclusive usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: v_Sealed (Core.Ops.Range.t_Bound usize & Core.Ops.Range.t_Bound usize) =
  { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: v_Sealed Core.Ops.Index_range.t_IndexRange = { __marker_trait = () }

let v_BITS80497669: t_u32 = t_u32 Core.Base_interface.Int.impl_97__BITS <: t_u32

let v_MAX626626007: t_i8 =
  t_i8 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_i8

let v_MIN19747349: t_i8 =
  t_i8 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_i8

let v_BITS421056295: t_u32 = t_u32 Core.Base_interface.Int.impl_83__BITS <: t_u32

let v_MAX474501300: t_i16 =
  t_i16 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_i16

let v_MIN776391606: t_i16 =
  t_i16 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_i16

let v_BITS465526498: t_u32 = t_u32 Core.Base_interface.Int.impl_69__BITS <: t_u32

let v_MAX106630818: t_i32 =
  t_i32 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_i32

let v_MIN682967538: t_i32 =
  t_i32 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_i32

let v_BITS419886578: t_u32 = t_u32 Core.Base_interface.Int.impl_55__BITS <: t_u32

let v_MAX527043787: t_i64 =
  t_i64 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_i64

let v_MIN654206259: t_i64 =
  t_i64 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_i64

let v_BITS992667165: t_u32 = t_u32 Core.Base_interface.Int.impl_41__BITS <: t_u32

let v_MAX375377319: t_i128 =
  t_i128 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_i128

let v_MIN79612531: t_i128 =
  t_i128 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_i128

let v_BITS211584016: t_u32 = t_u32 Core.Base_interface.Int.impl_55__BITS <: t_u32

let v_MAX937003029: t_isize =
  t_isize (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_isize

let v_MIN1017039533: t_isize =
  t_isize (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_isize

let v_BITS690311813: t_u32 = t_u32 Core.Base_interface.Int.impl_219__BITS <: t_u32

let v_MAX310118176: t_u8 =
  t_u8 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_u8

let v_MIN41851434: t_u8 =
  t_u8 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_u8

let v_BITS277333551: t_u32 = t_u32 Core.Base_interface.Int.impl_192__BITS <: t_u32

let v_MAX487295910: t_u16 =
  t_u16 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_u16

let v_MIN592300287: t_u16 =
  t_u16 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_u16

let v_BITS473478051: t_u32 = t_u32 Core.Base_interface.Int.impl_165__BITS <: t_u32

let v_MAX826434525: t_u32 =
  t_u32 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_u32

let v_MIN932777089: t_u32 =
  t_u32 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_u32

let v_BITS177666292: t_u32 = t_u32 Core.Base_interface.Int.impl_138__BITS <: t_u32

let v_MAX815180633: t_u64 =
  t_u64 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_u64

let v_MIN631333594: t_u64 =
  t_u64 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_u64

let v_BITS136999051: t_u32 = t_u32 Core.Base_interface.Int.impl_111__BITS <: t_u32

let v_MAX404543799: t_u128 =
  t_u128 (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_u128

let v_MIN668621698: t_u128 =
  t_u128 (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_u128

let v_BITS229952196: t_u32 = t_u32 Core.Base_interface.Int.impl_138__BITS <: t_u32

let v_MAX750570916: t_usize =
  t_usize (Core.Base_interface.Int.f_MAX #FStar.Tactics.Typeclasses.solve) <: t_usize

let v_MIN861571008: t_usize =
  t_usize (Core.Base_interface.Int.f_MIN #FStar.Tactics.Typeclasses.solve) <: t_usize

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T #v_I: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i3: Core.Ops.Index.t_Index (t_Slice v_T) v_I)
    : Core.Ops.Index.t_Index (t_Array v_T v_N) v_I =
  {
    f_Output = i3.f_Output;
    f_index_pre = (fun (self: t_Array v_T v_N) (index: v_I) -> true);
    f_index_post = (fun (self: t_Array v_T v_N) (index: v_I) (out: i3.f_Output) -> true);
    f_index
    =
    fun (self: t_Array v_T v_N) (index: v_I) -> (cast #v_T v_N self <: t_Slice v_T).[ index ]
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Array v_T v_N) (t_Array v_T v_N) =
  {
    f_from_pre = (fun (x: t_Array v_T v_N) -> true);
    f_from_post = (fun (x: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_from
    =
    fun (x: t_Array v_T v_N) ->
      match
        Core.Convert.f_try_into #(Alloc.Vec.t_Vec v_T Alloc.Alloc.t_Global)
          #(t_Array v_T v_N)
          #FStar.Tactics.Typeclasses.solve
          x.f_v.f_v.f_v
      with
      | Core.Result.Result_Ok x -> x
      | _ ->
        Rust_primitives.Hax.never_to_any (Core.Panicking.panic_fmt (Core.Fmt.impl_2__new_const (sz 1
                  )
                  (let list = ["some error?"] in
                    FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                    Rust_primitives.Hax.array_of_list 1 list)
                <:
                Core.Fmt.t_Arguments)
            <:
            Rust_primitives.Hax.t_Never)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Clone.t_Clone t_u8 =
  {
    f_clone_pre = (fun (self: t_u8) -> true);
    f_clone_post = (fun (self: t_u8) (out: t_u8) -> true);
    f_clone
    =
    fun (self: t_u8) ->
      t_u8
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U8 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Clone.t_Clone t_u16 =
  {
    f_clone_pre = (fun (self: t_u16) -> true);
    f_clone_post = (fun (self: t_u16) (out: t_u16) -> true);
    f_clone
    =
    fun (self: t_u16) ->
      t_u16
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U16 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Clone.t_Clone t_u32 =
  {
    f_clone_pre = (fun (self: t_u32) -> true);
    f_clone_post = (fun (self: t_u32) (out: t_u32) -> true);
    f_clone
    =
    fun (self: t_u32) ->
      t_u32
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U32 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Clone.t_Clone t_u64 =
  {
    f_clone_pre = (fun (self: t_u64) -> true);
    f_clone_post = (fun (self: t_u64) (out: t_u64) -> true);
    f_clone
    =
    fun (self: t_u64) ->
      t_u64
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Clone.t_Clone t_u128 =
  {
    f_clone_pre = (fun (self: t_u128) -> true);
    f_clone_post = (fun (self: t_u128) (out: t_u128) -> true);
    f_clone
    =
    fun (self: t_u128) ->
      t_u128
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U128 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Clone.t_Clone t_usize =
  {
    f_clone_pre = (fun (self: t_usize) -> true);
    f_clone_post = (fun (self: t_usize) (out: t_usize) -> true);
    f_clone
    =
    fun (self: t_usize) ->
      t_usize
      (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_usize
  }

class v_SliceIndex (v_Self: Type0) (v_T: Type0) = {
  [@@@ FStar.Tactics.Typeclasses.no_method]_super_9346575357466912174:v_Sealed v_Self;
  f_Output:Type0;
  f_index_pre:v_Self -> v_T -> Type0;
  f_index_post:v_Self -> v_T -> f_Output -> Type0;
  f_index:x0: v_Self -> x1: v_T
    -> Prims.Pure f_Output (f_index_pre x0 x1) (fun result -> f_index_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T #v_I: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: v_SliceIndex v_I (t_Slice v_T))
    : Core.Ops.Index.t_Index (t_Slice v_T) v_I =
  {
    f_Output = i2.f_Output;
    f_index_pre = (fun (self: t_Slice v_T) (index: v_I) -> true);
    f_index_post = (fun (self: t_Slice v_T) (index: v_I) (out: i2.f_Output) -> true);
    f_index
    =
    fun (self: t_Slice v_T) (index: v_I) ->
      Core.Slice.Index.f_index #v_I #(t_Slice v_T) #FStar.Tactics.Typeclasses.solve index self
  }

let cons
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: t_Seq v_T)
      (t: v_T)
    : t_Seq v_T =
  {
    f_v
    =
    Alloc.Slice.impl__concat #(t_Slice v_T)
      #v_T
      ((let list =
            [
              (let list = [t] in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list).[ Core.Ops.Range.RangeFull
                <:
                Core.Ops.Range.t_RangeFull ];
              s.f_v.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
            ]
          in
          FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 2);
          Rust_primitives.Hax.array_of_list 2 list)
        <:
        t_Slice (t_Slice v_T))
  }
  <:
  t_Seq v_T

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_From (t_Array v_T v_N) (t_Array v_T v_N) =
  {
    f_from_pre = (fun (x: t_Array v_T v_N) -> true);
    f_from_post = (fun (x: t_Array v_T v_N) (out: t_Array v_T v_N) -> true);
    f_from
    =
    fun (x: t_Array v_T v_N) ->
      {
        f_v
        =
        {
          f_v
          =
          {
            f_v
            =
            Alloc.Slice.impl__to_vec #v_T
              (x.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ] <: t_Slice v_T)
          }
          <:
          t_Seq v_T
        }
        <:
        t_Slice v_T
      }
      <:
      t_Array v_T v_N
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2 (#v_T: Type0) : v_SliceIndex Core.Ops.Range.t_RangeFull (t_Slice v_T) =
  {
    _super_9346575357466912174 = FStar.Tactics.Typeclasses.solve;
    f_Output = t_Slice v_T;
    f_index_pre = (fun (self: Core.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> true);
    f_index_post
    =
    (fun (self: Core.Ops.Range.t_RangeFull) (slice: t_Slice v_T) (out: t_Slice v_T) -> true);
    f_index = fun (self: Core.Ops.Range.t_RangeFull) (slice: t_Slice v_T) -> slice
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl
      (#v_T: Type0)
      (v_N: usize)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : Core.Convert.t_AsRef (t_Array v_T v_N) (t_Slice v_T) =
  {
    f_as_ref_pre = (fun (self: t_Array v_T v_N) -> true);
    f_as_ref_post = (fun (self: t_Array v_T v_N) (out: t_Slice v_T) -> true);
    f_as_ref
    =
    fun (self: t_Array v_T v_N) -> self.[ Core.Ops.Range.RangeFull <: Core.Ops.Range.t_RangeFull ]
  }

let match_list
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
      (s: t_Seq v_T)
    : t_LIST v_T =
  if
    Rust_primitives.Usize.eq (Alloc.Vec.impl_1__len #v_T #Alloc.Alloc.t_Global s.f_v <: usize)
      (sz 0)
  then LIST_NIL <: t_LIST v_T
  else
    LIST_CONS (Core.Clone.f_clone #v_T #FStar.Tactics.Typeclasses.solve (s.f_v.[ sz 0 ] <: v_T))
      ({
          f_v
          =
          Alloc.Slice.impl__concat #(t_Slice v_T)
            #v_T
            ((let list =
                  [s.f_v.[ { Core.Ops.Range.f_start = sz 1 } <: Core.Ops.Range.t_RangeFrom usize ]]
                in
                FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 1);
                Rust_primitives.Hax.array_of_list 1 list)
              <:
              t_Slice (t_Slice v_T))
        }
        <:
        t_Seq v_T)
    <:
    t_LIST v_T

let rec from_u128_binary (x: u128)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U128.ne x (pub_u128 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U128.eq x (pub_u128 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U128.eq (Rust_primitives.U128.rem x (pub_u128 2) <: u128) (pub_u128 0)
    then
      Core.Base.Spec.Binary.Positive.xO (from_u128_binary (Rust_primitives.U128.div x (pub_u128 2)
              <:
              u128)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u128_binary (Rust_primitives.U128.div x (pub_u128 2)
              <:
              u128)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u128 =
  {
    f_from_pre = (fun (x: u128) -> true);
    f_from_post = (fun (x: u128) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u128) ->
      if Rust_primitives.U128.eq x (pub_u128 0)
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u128_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From Core.Base.Spec.Z.t_Z i128 =
  {
    f_from_pre = (fun (x: i128) -> true);
    f_from_post = (fun (x: i128) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i128) ->
      match Core.Cmp.f_cmp #i128 #FStar.Tactics.Typeclasses.solve x (pub_i128 0) with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u128_binary (Core.Num.impl__i128__unsigned_abs x <: u128))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u16_binary (x: u16)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U16.ne x 0us)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U16.eq x 1us
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U16.eq (Rust_primitives.U16.rem x 2us <: u16) 0us
    then
      Core.Base.Spec.Binary.Positive.xO (from_u16_binary (Rust_primitives.U16.div x 2us <: u16)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u16_binary (Rust_primitives.U16.div x 2us <: u16)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u16) ->
      if Rust_primitives.U16.eq x 0us
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u16_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From Core.Base.Spec.Z.t_Z i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i16) ->
      match Core.Cmp.f_cmp #i16 #FStar.Tactics.Typeclasses.solve x 0s with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u16_binary (Core.Num.impl__i16__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u16_binary (Core.Num.impl__i16__unsigned_abs x <: u16))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u32_binary (x: u32)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U32.ne x 0ul)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U32.eq x 1ul
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U32.eq (Rust_primitives.U32.rem x 2ul <: u32) 0ul
    then
      Core.Base.Spec.Binary.Positive.xO (from_u32_binary (Rust_primitives.U32.div x 2ul <: u32)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u32_binary (Rust_primitives.U32.div x 2ul <: u32)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u32) ->
      if Rust_primitives.U32.eq x 0ul
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u32_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From Core.Base.Spec.Z.t_Z i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i32) ->
      match Core.Cmp.f_cmp #i32 #FStar.Tactics.Typeclasses.solve x 0l with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u32_binary (Core.Num.impl_2__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u32_binary (Core.Num.impl_2__unsigned_abs x <: u32))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u64_binary (x: u64)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U64.ne x 0uL)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U64.eq x 1uL
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U64.eq (Rust_primitives.U64.rem x 2uL <: u64) 0uL
    then
      Core.Base.Spec.Binary.Positive.xO (from_u64_binary (Rust_primitives.U64.div x 2uL <: u64)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u64_binary (Rust_primitives.U64.div x 2uL <: u64)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u64) ->
      if Rust_primitives.U64.eq x 0uL
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u64_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From Core.Base.Spec.Z.t_Z i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i64) ->
      match Core.Cmp.f_cmp #i64 #FStar.Tactics.Typeclasses.solve x 0L with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u64_binary (Core.Num.impl__i64__unsigned_abs x <: u64))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_u8_binary (x: u8)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.U8.ne x 0uy)
      (fun _ -> Prims.l_True) =
  if Rust_primitives.U8.eq x 1uy
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.U8.eq (Rust_primitives.U8.rem x 2uy <: u8) 0uy
    then
      Core.Base.Spec.Binary.Positive.xO (from_u8_binary (Rust_primitives.U8.div x 2uy <: u8)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_u8_binary (Rust_primitives.U8.div x 2uy <: u8)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: u8) ->
      if Rust_primitives.U8.eq x 0uy
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_u8_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From Core.Base.Spec.Z.t_Z i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: i8) ->
      match Core.Cmp.f_cmp #i8 #FStar.Tactics.Typeclasses.solve x 0y with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_u8_binary (Core.Num.impl__i8__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_u8_binary (Core.Num.impl__i8__unsigned_abs x <: u8))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec from_usize_binary (x: usize)
    : Prims.Pure Core.Base.Spec.Binary.Positive.t_Positive
      (requires Rust_primitives.Usize.ne x (sz 0))
      (fun _ -> Prims.l_True) =
  if Rust_primitives.Usize.eq x (sz 1)
  then Core.Base.Spec.Binary.Positive.xH
  else
    if Rust_primitives.Usize.eq (Rust_primitives.Usize.rem x (sz 2) <: usize) (sz 0)
    then
      Core.Base.Spec.Binary.Positive.xO (from_usize_binary (Rust_primitives.Usize.div x (sz 2)
              <:
              usize)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    else
      Core.Base.Spec.Binary.Positive.xI (from_usize_binary (Rust_primitives.Usize.div x (sz 2)
              <:
              usize)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From Core.Base.Spec.Haxint.t_HaxInt usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from
    =
    fun (x: usize) ->
      if Rust_primitives.Usize.eq x (sz 0)
      then Core.Base.Spec.Haxint.v_HaxInt_ZERO
      else
        Core.Base.Spec.Binary.Positive.positive_to_int (from_usize_binary x
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From Core.Base.Spec.Z.t_Z isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: Core.Base.Spec.Z.t_Z) -> true);
    f_from
    =
    fun (x: isize) ->
      match Core.Cmp.f_cmp #isize #FStar.Tactics.Typeclasses.solve x (isz 0) with
      | Core.Cmp.Ordering_Equal  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Less  ->
        Core.Base.Spec.Z.Z_NEG (from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
      | Core.Cmp.Ordering_Greater  ->
        Core.Base.Spec.Z.Z_POS (from_usize_binary (Core.Num.impl__isize__unsigned_abs x <: usize))
        <:
        Core.Base.Spec.Z.t_Z
  }

let rec to_u128_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u128 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> pub_u128 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U128.mul (to_u128_binary p <: u128) (pub_u128 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U128.add (Rust_primitives.U128.mul (to_u128_binary p <: u128) (pub_u128 2)
        <:
        u128)
      (pub_u128 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u128 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u128) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> pub_u128 0
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u128_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From i128 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i128) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I128.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U128.sub (to_u128_binary
                          x
                        <:
                        u128)
                      (pub_u128 1)
                    <:
                    u128)
                <:
                i128)
            <:
            i128)
          (pub_i128 1)
      | Core.Base.Spec.Z.Z_ZERO  -> pub_i128 0
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u128_binary x <: u128) <: i128
  }

let rec to_u16_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u16 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U16.mul (to_u16_binary p <: u16) 2us
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U16.add (Rust_primitives.U16.mul (to_u16_binary p <: u16) 2us <: u16) 1us

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From u16 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u16) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0us
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u16_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From i16 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i16) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I16.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U16.sub (to_u16_binary
                          x
                        <:
                        u16)
                      1us
                    <:
                    u16)
                <:
                i16)
            <:
            i16)
          1s
      | Core.Base.Spec.Z.Z_ZERO  -> 0s
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u16_binary x <: u16) <: i16
  }

let rec to_u32_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u32 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U32.mul (to_u32_binary p <: u32) 2ul
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U32.add (Rust_primitives.U32.mul (to_u32_binary p <: u32) 2ul <: u32) 1ul

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From u32 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u32) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0ul
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u32_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From i32 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i32) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I32.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U32.sub (to_u32_binary
                          x
                        <:
                        u32)
                      1ul
                    <:
                    u32)
                <:
                i32)
            <:
            i32)
          1l
      | Core.Base.Spec.Z.Z_ZERO  -> 0l
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u32_binary x <: u32) <: i32
  }

let rec to_u64_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u64 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U64.mul (to_u64_binary p <: u64) 2uL
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U64.add (Rust_primitives.U64.mul (to_u64_binary p <: u64) 2uL <: u64) 1uL

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From u64 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u64) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0uL
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u64_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From i64 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i64) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I64.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U64.sub (to_u64_binary
                          x
                        <:
                        u64)
                      1uL
                    <:
                    u64)
                <:
                i64)
            <:
            i64)
          1L
      | Core.Base.Spec.Z.Z_ZERO  -> 0L
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u64_binary x <: u64) <: i64
  }

let rec to_u8_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : u8 =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> 1uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.U8.mul (to_u8_binary p <: u8) 2uy
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.U8.add (Rust_primitives.U8.mul (to_u8_binary p <: u8) 2uy <: u8) 1uy

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u8 Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: u8) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> 0uy
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_u8_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From i8 Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: i8) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.I8.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.U8.sub (to_u8_binary x
                        <:
                        u8)
                      1uy
                    <:
                    u8)
                <:
                i8)
            <:
            i8)
          1y
      | Core.Base.Spec.Z.Z_ZERO  -> 0y
      | Core.Base.Spec.Z.Z_POS x -> cast (to_u8_binary x <: u8) <: i8
  }

let rec to_usize_binary (self: Core.Base.Spec.Binary.Positive.t_Positive) : usize =
  match Core.Base.Spec.Binary.Positive.match_positive self with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> sz 1
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Rust_primitives.Usize.mul (to_usize_binary p <: usize) (sz 2)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Rust_primitives.Usize.add (Rust_primitives.Usize.mul (to_usize_binary p <: usize) (sz 2)
        <:
        usize)
      (sz 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From usize Core.Base.Spec.Haxint.t_HaxInt =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Haxint.t_HaxInt) (out: usize) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Haxint.t_HaxInt) ->
      match Core.Base.Spec.Binary.Pos.match_pos x with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> sz 0
      | Core.Base.Spec.Binary.Pos.POS_POS p -> to_usize_binary p
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From isize Core.Base.Spec.Z.t_Z =
  {
    f_from_pre = (fun (x: Core.Base.Spec.Z.t_Z) -> true);
    f_from_post = (fun (x: Core.Base.Spec.Z.t_Z) (out: isize) -> true);
    f_from
    =
    fun (x: Core.Base.Spec.Z.t_Z) ->
      match x with
      | Core.Base.Spec.Z.Z_NEG x ->
        Rust_primitives.Isize.sub (Core.Ops.Arith.Neg.neg (cast (Rust_primitives.Usize.sub (to_usize_binary
                          x
                        <:
                        usize)
                      (sz 1)
                    <:
                    usize)
                <:
                isize)
            <:
            isize)
          (isz 1)
      | Core.Base.Spec.Z.Z_ZERO  -> isz 0
      | Core.Base.Spec.Z.Z_POS x -> cast (to_usize_binary x <: usize) <: isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Cmp.t_PartialEq t_u8 t_u8 =
  {
    f_eq_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_eq_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_eq = (fun (self: t_u8) (rhs: t_u8) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_ne_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_ne = fun (self: t_u8) (rhs: t_u8) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Cmp.t_PartialOrd t_u8 t_u8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u8) (rhs: t_u8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_lt_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_le_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_gt_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u8) (rhs: t_u8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
            #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_ge_post = (fun (self: t_u8) (rhs: t_u8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u8) (rhs: t_u8) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Cmp.t_PartialEq t_u16 t_u16 =
  {
    f_eq_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_eq_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_eq = (fun (self: t_u16) (rhs: t_u16) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_ne_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_ne = fun (self: t_u16) (rhs: t_u16) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Cmp.t_PartialOrd t_u16 t_u16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u16) (rhs: t_u16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_lt_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_le_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_gt_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u16) (rhs: t_u16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
            #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u16) (rhs: t_u16) -> true);
    f_ge_post = (fun (self: t_u16) (rhs: t_u16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u16) (rhs: t_u16) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Cmp.t_PartialEq t_u32 t_u32 =
  {
    f_eq_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_eq_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_eq = (fun (self: t_u32) (rhs: t_u32) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_ne_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_ne = fun (self: t_u32) (rhs: t_u32) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Cmp.t_PartialOrd t_u32 t_u32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u32) (rhs: t_u32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_lt_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_le_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_gt_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u32) (rhs: t_u32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
            #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_ge_post = (fun (self: t_u32) (rhs: t_u32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u32) (rhs: t_u32) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Cmp.t_PartialEq t_u64 t_u64 =
  {
    f_eq_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_eq_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_eq = (fun (self: t_u64) (rhs: t_u64) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_ne_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_ne = fun (self: t_u64) (rhs: t_u64) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Cmp.t_PartialOrd t_u64 t_u64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u64) (rhs: t_u64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_lt_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_le_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_gt_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u64) (rhs: t_u64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u64) (rhs: t_u64) -> true);
    f_ge_post = (fun (self: t_u64) (rhs: t_u64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u64) (rhs: t_u64) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Cmp.t_PartialEq t_u128 t_u128 =
  {
    f_eq_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_eq_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_eq = (fun (self: t_u128) (rhs: t_u128) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_ne_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_ne = fun (self: t_u128) (rhs: t_u128) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Cmp.t_PartialOrd t_u128 t_u128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_u128) (rhs: t_u128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_lt_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_le_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_gt_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_u128) (rhs: t_u128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
            #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_ge_post = (fun (self: t_u128) (rhs: t_u128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_u128) (rhs: t_u128) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Cmp.t_PartialEq t_usize t_usize =
  {
    f_eq_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_eq_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_eq = (fun (self: t_usize) (rhs: t_usize) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_ne_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_ne = fun (self: t_usize) (rhs: t_usize) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Cmp.t_PartialOrd t_usize t_usize =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_usize) (rhs: t_usize) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_lt_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_le_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_le
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_gt_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_usize) (rhs: t_usize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
            #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_usize) (rhs: t_usize) -> true);
    f_ge_post = (fun (self: t_usize) (rhs: t_usize) (out: bool) -> true);
    f_ge
    =
    fun (self: t_usize) (rhs: t_usize) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Cmp.t_PartialEq t_i8 t_i8 =
  {
    f_eq_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_eq_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_eq = (fun (self: t_i8) (rhs: t_i8) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_ne_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_ne = fun (self: t_i8) (rhs: t_i8) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Cmp.t_PartialOrd t_i8 t_i8 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i8) (rhs: t_i8) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_lt_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_le_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_gt_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i8) (rhs: t_i8) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
            #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i8) (rhs: t_i8) -> true);
    f_ge_post = (fun (self: t_i8) (rhs: t_i8) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i8) (rhs: t_i8) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Cmp.t_PartialEq t_i16 t_i16 =
  {
    f_eq_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_eq_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_eq = (fun (self: t_i16) (rhs: t_i16) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_ne_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_ne = fun (self: t_i16) (rhs: t_i16) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Cmp.t_PartialOrd t_i16 t_i16 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i16) (rhs: t_i16) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_lt_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_le_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_gt_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i16) (rhs: t_i16) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
            #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i16) (rhs: t_i16) -> true);
    f_ge_post = (fun (self: t_i16) (rhs: t_i16) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i16) (rhs: t_i16) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Cmp.t_PartialEq t_i32 t_i32 =
  {
    f_eq_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_eq_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_eq = (fun (self: t_i32) (rhs: t_i32) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_ne_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_ne = fun (self: t_i32) (rhs: t_i32) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Cmp.t_PartialOrd t_i32 t_i32 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i32) (rhs: t_i32) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_lt_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_le_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_gt_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i32) (rhs: t_i32) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
            #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i32) (rhs: t_i32) -> true);
    f_ge_post = (fun (self: t_i32) (rhs: t_i32) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i32) (rhs: t_i32) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Cmp.t_PartialEq t_i64 t_i64 =
  {
    f_eq_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_eq_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_eq = (fun (self: t_i64) (rhs: t_i64) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_ne_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_ne = fun (self: t_i64) (rhs: t_i64) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Cmp.t_PartialOrd t_i64 t_i64 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i64) (rhs: t_i64) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_lt_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_le_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_gt_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i64) (rhs: t_i64) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i64) (rhs: t_i64) -> true);
    f_ge_post = (fun (self: t_i64) (rhs: t_i64) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i64) (rhs: t_i64) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Cmp.t_PartialEq t_i128 t_i128 =
  {
    f_eq_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_eq_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_eq = (fun (self: t_i128) (rhs: t_i128) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_ne_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_ne = fun (self: t_i128) (rhs: t_i128) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Cmp.t_PartialOrd t_i128 t_i128 =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_i128) (rhs: t_i128) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_lt_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_le_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_le
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_gt_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_i128) (rhs: t_i128) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
            #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_i128) (rhs: t_i128) -> true);
    f_ge_post = (fun (self: t_i128) (rhs: t_i128) (out: bool) -> true);
    f_ge
    =
    fun (self: t_i128) (rhs: t_i128) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Cmp.t_PartialEq t_isize t_isize =
  {
    f_eq_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_eq_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_eq = (fun (self: t_isize) (rhs: t_isize) -> self._0 =. rhs._0);
    f_ne_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_ne_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_ne = fun (self: t_isize) (rhs: t_isize) -> ~.(self._0 =. rhs._0 <: bool)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Cmp.t_PartialOrd t_isize t_isize =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_partial_cmp_post
    =
    (fun (self: t_isize) (rhs: t_isize) (out: Core.Option.t_Option Core.Cmp.t_Ordering) -> true);
    f_partial_cmp
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0);
    f_lt_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_lt_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_lt
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
        | _ -> false);
    f_le_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_le_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_le
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_gt_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_gt
    =
    (fun (self: t_isize) (rhs: t_isize) ->
        match
          Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
            #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            self._0
            rhs._0
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: t_isize) (rhs: t_isize) -> true);
    f_ge_post = (fun (self: t_isize) (rhs: t_isize) (out: bool) -> true);
    f_ge
    =
    fun (self: t_isize) (rhs: t_isize) ->
      match
        Core.Cmp.f_partial_cmp #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          self._0
          rhs._0
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_u8 u8 =
  {
    f_from_pre = (fun (x: u8) -> true);
    f_from_post = (fun (x: u8) (out: t_u8) -> true);
    f_from
    =
    fun (x: u8) ->
      t_u8
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u8 #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_U8)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From u8 t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: u8) -> true);
    f_from
    =
    fun (x: t_u8) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u8
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_u16 u16 =
  {
    f_from_pre = (fun (x: u16) -> true);
    f_from_post = (fun (x: u16) (out: t_u16) -> true);
    f_from
    =
    fun (x: u16) ->
      t_u16
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u16
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U16)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From u16 t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: u16) -> true);
    f_from
    =
    fun (x: t_u16) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u16
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From t_u32 u32 =
  {
    f_from_pre = (fun (x: u32) -> true);
    f_from_post = (fun (x: u32) (out: t_u32) -> true);
    f_from
    =
    fun (x: u32) ->
      t_u32
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u32
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U32)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From u32 t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: u32) -> true);
    f_from
    =
    fun (x: t_u32) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u32
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From t_u64 u64 =
  {
    f_from_pre = (fun (x: u64) -> true);
    f_from_post = (fun (x: u64) (out: t_u64) -> true);
    f_from
    =
    fun (x: u64) ->
      t_u64
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u64
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U64)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From u64 t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: u64) -> true);
    f_from
    =
    fun (x: t_u64) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u64
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From t_u128 u128 =
  {
    f_from_pre = (fun (x: u128) -> true);
    f_from_post = (fun (x: u128) (out: t_u128) -> true);
    f_from
    =
    fun (x: u128) ->
      t_u128
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #u128
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U128)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From u128 t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: u128) -> true);
    f_from
    =
    fun (x: t_u128) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #u128
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_usize usize =
  {
    f_from_pre = (fun (x: usize) -> true);
    f_from_post = (fun (x: usize) (out: t_usize) -> true);
    f_from
    =
    fun (x: usize) ->
      t_usize
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #usize
            #Core.Base.Spec.Haxint.t_HaxInt
            #FStar.Tactics.Typeclasses.solve
            x
        }
        <:
        Core.Base_interface.Int.t_U64)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From usize t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: usize) -> true);
    f_from
    =
    fun (x: t_usize) ->
      Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
        #usize
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Convert.t_From t_i8 i8 =
  {
    f_from_pre = (fun (x: i8) -> true);
    f_from_post = (fun (x: i8) (out: t_i8) -> true);
    f_from
    =
    fun (x: i8) ->
      t_i8
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i8 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I8)
      <:
      t_i8
  }

let is_negative350273175 (self: t_i8) : bool =
  self <. (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)

let is_positive286955196 (self: t_i8) : bool =
  self >. (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)

let signum721334203 (self: t_i8) : t_i8 =
  if
    (Core.Clone.f_clone #t_i8 #FStar.Tactics.Typeclasses.solve self <: t_i8) <.
    (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)
  then Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve (-1y)
  else
    if self =. (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)
    then Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y
    else Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 1y

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Convert.t_From i8 t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: i8) -> true);
    f_from
    =
    fun (x: t_i8) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i8
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Convert.t_From t_i16 i16 =
  {
    f_from_pre = (fun (x: i16) -> true);
    f_from_post = (fun (x: i16) (out: t_i16) -> true);
    f_from
    =
    fun (x: i16) ->
      t_i16
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i16 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I16)
      <:
      t_i16
  }

let is_negative477067241 (self: t_i16) : bool =
  self <. (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s <: t_i16)

let is_positive821581438 (self: t_i16) : bool =
  self >. (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s <: t_i16)

let signum243706004 (self: t_i16) : t_i16 =
  if
    (Core.Clone.f_clone #t_i16 #FStar.Tactics.Typeclasses.solve self <: t_i16) <.
    (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s <: t_i16)
  then Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve (-1s)
  else
    if self =. (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s <: t_i16)
    then Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s
    else Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 1s

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Convert.t_From i16 t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: i16) -> true);
    f_from
    =
    fun (x: t_i16) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i16
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Convert.t_From t_i32 i32 =
  {
    f_from_pre = (fun (x: i32) -> true);
    f_from_post = (fun (x: i32) (out: t_i32) -> true);
    f_from
    =
    fun (x: i32) ->
      t_i32
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i32 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I32)
      <:
      t_i32
  }

let is_negative1035644813 (self: t_i32) : bool =
  self <. (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l <: t_i32)

let is_positive401652342 (self: t_i32) : bool =
  self >. (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l <: t_i32)

let signum323641039 (self: t_i32) : t_i32 =
  if
    (Core.Clone.f_clone #t_i32 #FStar.Tactics.Typeclasses.solve self <: t_i32) <.
    (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l <: t_i32)
  then Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve (-1l)
  else
    if self =. (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l <: t_i32)
    then Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l
    else Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 1l

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Convert.t_From i32 t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: i32) -> true);
    f_from
    =
    fun (x: t_i32) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i32
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Convert.t_From t_i64 i64 =
  {
    f_from_pre = (fun (x: i64) -> true);
    f_from_post = (fun (x: i64) (out: t_i64) -> true);
    f_from
    =
    fun (x: i64) ->
      t_i64
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i64 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I64)
      <:
      t_i64
  }

let is_negative1066124578 (self: t_i64) : bool =
  self <. (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L <: t_i64)

let is_positive16569358 (self: t_i64) : bool =
  self >. (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L <: t_i64)

let signum582963664 (self: t_i64) : t_i64 =
  if
    (Core.Clone.f_clone #t_i64 #FStar.Tactics.Typeclasses.solve self <: t_i64) <.
    (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L <: t_i64)
  then Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve (-1L)
  else
    if self =. (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L <: t_i64)
    then Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L
    else Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 1L

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Convert.t_From i64 t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: i64) -> true);
    f_from
    =
    fun (x: t_i64) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i64
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Convert.t_From t_i128 i128 =
  {
    f_from_pre = (fun (x: i128) -> true);
    f_from_post = (fun (x: i128) (out: t_i128) -> true);
    f_from
    =
    fun (x: i128) ->
      t_i128
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #i128 #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I128)
      <:
      t_i128
  }

let is_negative221698470 (self: t_i128) : bool =
  self <.
  (Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0) <: t_i128)

let is_positive883218309 (self: t_i128) : bool =
  self >.
  (Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0) <: t_i128)

let signum408800799 (self: t_i128) : t_i128 =
  if
    (Core.Clone.f_clone #t_i128 #FStar.Tactics.Typeclasses.solve self <: t_i128) <.
    (Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0) <: t_i128)
  then Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 (-1))
  else
    if
      self =.
      (Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0) <: t_i128)
    then Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0)
    else Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Convert.t_From i128 t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: i128) -> true);
    f_from
    =
    fun (x: t_i128) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #i128
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Convert.t_From t_isize isize =
  {
    f_from_pre = (fun (x: isize) -> true);
    f_from_post = (fun (x: isize) (out: t_isize) -> true);
    f_from
    =
    fun (x: isize) ->
      t_isize
      ({
          Core.Base_interface.Int.f_v
          =
          Core.Convert.f_into #isize #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve x
        }
        <:
        Core.Base_interface.Int.t_I64)
      <:
      t_isize
  }

let is_negative693446369 (self: t_isize) : bool =
  self <. (Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0) <: t_isize)

let is_positive169998680 (self: t_isize) : bool =
  self >. (Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0) <: t_isize)

let signum91486536 (self: t_isize) : t_isize =
  if
    (Core.Clone.f_clone #t_isize #FStar.Tactics.Typeclasses.solve self <: t_isize) <.
    (Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0) <: t_isize)
  then Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz (-1))
  else
    if
      self =.
      (Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0) <: t_isize)
    then Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0)
    else Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 1)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Convert.t_From isize t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: isize) -> true);
    f_from
    =
    fun (x: t_isize) ->
      Core.Convert.f_into #Core.Base.Spec.Z.t_Z
        #isize
        #FStar.Tactics.Typeclasses.solve
        x._0.Core.Base_interface.Int.f_v
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_i16 t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: t_i16) -> true);
    f_from
    =
    fun (x: t_i8) ->
      t_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From t_i32 t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: t_i32) -> true);
    f_from
    =
    fun (x: t_i8) ->
      t_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From t_i64 t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: t_i64) -> true);
    f_from
    =
    fun (x: t_i8) ->
      t_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From t_i128 t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: t_i128) -> true);
    f_from
    =
    fun (x: t_i8) ->
      t_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From t_isize t_i8 =
  {
    f_from_pre = (fun (x: t_i8) -> true);
    f_from_post = (fun (x: t_i8) (out: t_isize) -> true);
    f_from
    =
    fun (x: t_i8) ->
      t_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I8
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From t_i8 t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: t_i8) -> true);
    f_from
    =
    fun (x: t_i16) ->
      t_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From t_i32 t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: t_i32) -> true);
    f_from
    =
    fun (x: t_i16) ->
      t_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From t_i64 t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: t_i64) -> true);
    f_from
    =
    fun (x: t_i16) ->
      t_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From t_i128 t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: t_i128) -> true);
    f_from
    =
    fun (x: t_i16) ->
      t_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From t_isize t_i16 =
  {
    f_from_pre = (fun (x: t_i16) -> true);
    f_from_post = (fun (x: t_i16) (out: t_isize) -> true);
    f_from
    =
    fun (x: t_i16) ->
      t_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I16
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From t_i8 t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: t_i8) -> true);
    f_from
    =
    fun (x: t_i32) ->
      t_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From t_i16 t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: t_i16) -> true);
    f_from
    =
    fun (x: t_i32) ->
      t_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Convert.t_From t_i64 t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: t_i64) -> true);
    f_from
    =
    fun (x: t_i32) ->
      t_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Convert.t_From t_i128 t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: t_i128) -> true);
    f_from
    =
    fun (x: t_i32) ->
      t_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Convert.t_From t_isize t_i32 =
  {
    f_from_pre = (fun (x: t_i32) -> true);
    f_from_post = (fun (x: t_i32) (out: t_isize) -> true);
    f_from
    =
    fun (x: t_i32) ->
      t_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I32
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Convert.t_From t_i8 t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: t_i8) -> true);
    f_from
    =
    fun (x: t_i64) ->
      t_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Convert.t_From t_i16 t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: t_i16) -> true);
    f_from
    =
    fun (x: t_i64) ->
      t_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Convert.t_From t_i32 t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: t_i32) -> true);
    f_from
    =
    fun (x: t_i64) ->
      t_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Convert.t_From t_i128 t_i64 =
  {
    f_from_pre = (fun (x: t_i64) -> true);
    f_from_post = (fun (x: t_i64) (out: t_i128) -> true);
    f_from
    =
    fun (x: t_i64) ->
      t_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Convert.t_From t_i8 t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: t_i8) -> true);
    f_from
    =
    fun (x: t_i128) ->
      t_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Convert.t_From t_i16 t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: t_i16) -> true);
    f_from
    =
    fun (x: t_i128) ->
      t_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Convert.t_From t_i32 t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: t_i32) -> true);
    f_from
    =
    fun (x: t_i128) ->
      t_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Convert.t_From t_i64 t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: t_i64) -> true);
    f_from
    =
    fun (x: t_i128) ->
      t_i64
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Convert.t_From t_isize t_i128 =
  {
    f_from_pre = (fun (x: t_i128) -> true);
    f_from_post = (fun (x: t_i128) (out: t_isize) -> true);
    f_from
    =
    fun (x: t_i128) ->
      t_isize
      (Core.Convert.f_into #Core.Base_interface.Int.t_I128
          #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Convert.t_From t_i8 t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: t_i8) -> true);
    f_from
    =
    fun (x: t_isize) ->
      t_i8
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Convert.t_From t_i16 t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: t_i16) -> true);
    f_from
    =
    fun (x: t_isize) ->
      t_i16
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Convert.t_From t_i32 t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: t_i32) -> true);
    f_from
    =
    fun (x: t_isize) ->
      t_i32
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Convert.t_From t_i128 t_isize =
  {
    f_from_pre = (fun (x: t_isize) -> true);
    f_from_post = (fun (x: t_isize) (out: t_i128) -> true);
    f_from
    =
    fun (x: t_isize) ->
      t_i128
      (Core.Convert.f_into #Core.Base_interface.Int.t_I64
          #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_i128
  }

/// The methods `index` and `index_mut` panic if the index is out of bounds.
[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1 (#v_T: Type0) (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: Core.Clone.t_Clone v_T)
    : v_SliceIndex t_usize (t_Slice v_T) =
  {
    _super_9346575357466912174 = FStar.Tactics.Typeclasses.solve;
    f_Output = v_T;
    f_index_pre = (fun (self: t_usize) (slice: t_Slice v_T) -> true);
    f_index_post = (fun (self: t_usize) (slice: t_Slice v_T) (out: v_T) -> true);
    f_index
    =
    fun (self: t_usize) (slice: t_Slice v_T) ->
      let (x: usize):usize =
        Core.Convert.f_into #Core.Base.Spec.Haxint.t_HaxInt
          #usize
          #FStar.Tactics.Typeclasses.solve
          self._0.Core.Base_interface.Int.f_v
      in
      slice.f_v.f_v.[ x ]
  }

let add_with_overflow_i128 (x y: t_i128) : (t_i128 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I128):Core.Base_interface.Int.t_I128 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I128
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_i128 (Core.Clone.f_clone #Core.Base_interface.Int.t_I128 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_i128),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_i128 & bool)

let add_with_overflow_i16 (x y: t_i16) : (t_i16 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I16):Core.Base_interface.Int.t_I16 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I16
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_i16 (Core.Clone.f_clone #Core.Base_interface.Int.t_I16 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_i16),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_i16 & bool)

let add_with_overflow_i32 (x y: t_i32) : (t_i32 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I32):Core.Base_interface.Int.t_I32 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I32
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_i32 (Core.Clone.f_clone #Core.Base_interface.Int.t_I32 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_i32),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_i32 & bool)

let add_with_overflow_i64 (x y: t_i64) : (t_i64 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I64):Core.Base_interface.Int.t_I64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_i64 (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_i64),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_i64 & bool)

let add_with_overflow_i8 (x y: t_i8) : (t_i8 & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I8):Core.Base_interface.Int.t_I8 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I8
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_i8 (Core.Clone.f_clone #Core.Base_interface.Int.t_I8 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_i8),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_i8 & bool)

let add_with_overflow_isize (x y: t_isize) : (t_isize & bool) =
  let overflow:Core.Base.Spec.Z.t_Z =
    Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Z.t_Z)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Z.t_Z)
  in
  let (res: Core.Base_interface.Int.t_I64):Core.Base_interface.Int.t_I64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Z.t_Z
      #Core.Base_interface.Int.t_I64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Z.t_Z)
  in
  (t_isize (Core.Clone.f_clone #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_isize),
  Core.Base.Z.z_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Z.t_Z)
    overflow
  <:
  (t_isize & bool)

let unchecked_add_i128 (x y: t_i128) : t_i128 =
  t_i128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I128)
  <:
  t_i128

let unchecked_add_i16 (x y: t_i16) : t_i16 =
  t_i16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I16)
  <:
  t_i16

let unchecked_add_i32 (x y: t_i32) : t_i32 =
  t_i32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I32)
  <:
  t_i32

let unchecked_add_i64 (x y: t_i64) : t_i64 =
  t_i64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  t_i64

let unchecked_add_i8 (x y: t_i8) : t_i8 =
  t_i8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I8)
  <:
  t_i8

let unchecked_add_isize (x y: t_isize) : t_isize =
  t_isize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  t_isize

let unchecked_add_u128 (x y: t_u128) : t_u128 =
  t_u128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U128)
  <:
  t_u128

let unchecked_add_u16 (x y: t_u16) : t_u16 =
  t_u16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U16)
  <:
  t_u16

let unchecked_add_u32 (x y: t_u32) : t_u32 =
  t_u32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U32)
  <:
  t_u32

let unchecked_add_u64 (x y: t_u64) : t_u64 =
  t_u64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  t_u64

let unchecked_add_u8 (x y: t_u8) : t_u8 =
  t_u8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U8)
  <:
  t_u8

let unchecked_add_usize (x y: t_usize) : t_usize =
  t_usize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  t_usize

let checked_add268751055 (self rhs: t_u8) : Core.Option.t_Option t_u8 =
  Core.Option.Option_Some (unchecked_add_u8 self rhs) <: Core.Option.t_Option t_u8

let checked_add132377399 (self rhs: t_u16) : Core.Option.t_Option t_u16 =
  Core.Option.Option_Some (unchecked_add_u16 self rhs) <: Core.Option.t_Option t_u16

let checked_add985437730 (self rhs: t_u32) : Core.Option.t_Option t_u32 =
  Core.Option.Option_Some (unchecked_add_u32 self rhs) <: Core.Option.t_Option t_u32

let checked_add586246465 (self rhs: t_u64) : Core.Option.t_Option t_u64 =
  Core.Option.Option_Some (unchecked_add_u64 self rhs) <: Core.Option.t_Option t_u64

let checked_add218978451 (self rhs: t_u128) : Core.Option.t_Option t_u128 =
  Core.Option.Option_Some (unchecked_add_u128 self rhs) <: Core.Option.t_Option t_u128

let checked_add984013567 (self rhs: t_usize) : Core.Option.t_Option t_usize =
  Core.Option.Option_Some (unchecked_add_usize self rhs) <: Core.Option.t_Option t_usize

let add_with_overflow_u128 (x y: t_u128) : (t_u128 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U128):Core.Base_interface.Int.t_U128 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U128
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_u128 (Core.Clone.f_clone #Core.Base_interface.Int.t_U128 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_u128),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_u128 & bool)

let add_with_overflow_u16 (x y: t_u16) : (t_u16 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U16):Core.Base_interface.Int.t_U16 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U16
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_u16 (Core.Clone.f_clone #Core.Base_interface.Int.t_U16 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_u16),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_u16 & bool)

let add_with_overflow_u32 (x y: t_u32) : (t_u32 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U32):Core.Base_interface.Int.t_U32 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U32
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_u32 (Core.Clone.f_clone #Core.Base_interface.Int.t_U32 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_u32),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_u32 & bool)

let add_with_overflow_u64 (x y: t_u64) : (t_u64 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U64):Core.Base_interface.Int.t_U64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_u64 (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_u64),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_u64 & bool)

let add_with_overflow_u8 (x y: t_u8) : (t_u8 & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U8):Core.Base_interface.Int.t_U8 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U8
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_u8 (Core.Clone.f_clone #Core.Base_interface.Int.t_U8 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_u8),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_u8 & bool)

let add_with_overflow_usize (x y: t_usize) : (t_usize & bool) =
  let overflow:Core.Base.Spec.Haxint.t_HaxInt =
    Core.Base.Pos.haxint_add (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
      (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          y._0
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  let (res: Core.Base_interface.Int.t_U64):Core.Base_interface.Int.t_U64 =
    Core.Base_interface.Coerce.f_concretize #Core.Base.Spec.Haxint.t_HaxInt
      #Core.Base_interface.Int.t_U64
      #FStar.Tactics.Typeclasses.solve
      (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve overflow
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  in
  (t_usize (Core.Clone.f_clone #Core.Base_interface.Int.t_U64 #FStar.Tactics.Typeclasses.solve res)
    <:
    t_usize),
  Core.Base.Pos.haxint_lt (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
        #FStar.Tactics.Typeclasses.solve
        res
      <:
      Core.Base.Spec.Haxint.t_HaxInt)
    overflow
  <:
  (t_usize & bool)

let unchecked_div_u128 (x y: t_u128) : t_u128 =
  t_u128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U128
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U128)
  <:
  t_u128

let unchecked_div_u16 (x y: t_u16) : t_u16 =
  t_u16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U16
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U16)
  <:
  t_u16

let unchecked_div_u32 (x y: t_u32) : t_u32 =
  t_u32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U32
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U32)
  <:
  t_u32

let unchecked_div_u64 (x y: t_u64) : t_u64 =
  t_u64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  t_u64

let unchecked_div_u8 (x y: t_u8) : t_u8 =
  t_u8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U8
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U8)
  <:
  t_u8

let unchecked_div_usize (x y: t_usize) : t_usize =
  t_usize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Pos.haxint_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_U64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    }
    <:
    Core.Base_interface.Int.t_U64)
  <:
  t_usize

let wrapping_add_i128 (a b: t_i128) : t_i128 = t_i128 (a._0 +! b._0) <: t_i128

let wrapping_add_i16 (a b: t_i16) : t_i16 = t_i16 (a._0 +! b._0) <: t_i16

let wrapping_add_i32 (a b: t_i32) : t_i32 = t_i32 (a._0 +! b._0) <: t_i32

let wrapping_add_i64 (a b: t_i64) : t_i64 = t_i64 (a._0 +! b._0) <: t_i64

let wrapping_add_i8 (a b: t_i8) : t_i8 = t_i8 (a._0 +! b._0) <: t_i8

let wrapping_add_isize (a b: t_isize) : t_isize = t_isize (a._0 +! b._0) <: t_isize

let wrapping_sub_i128 (a b: t_i128) : t_i128 = t_i128 (a._0 -! b._0) <: t_i128

let wrapping_sub_i16 (a b: t_i16) : t_i16 = t_i16 (a._0 -! b._0) <: t_i16

let wrapping_sub_i32 (a b: t_i32) : t_i32 = t_i32 (a._0 -! b._0) <: t_i32

let wrapping_sub_i64 (a b: t_i64) : t_i64 = t_i64 (a._0 -! b._0) <: t_i64

let wrapping_sub_i8 (a b: t_i8) : t_i8 = t_i8 (a._0 -! b._0) <: t_i8

let wrapping_sub_isize (a b: t_isize) : t_isize = t_isize (a._0 -! b._0) <: t_isize

let wrapping_add634491935 (self rhs: t_i8) : t_i8 = wrapping_add_i8 self rhs

let wrapping_sub973428293 (self rhs: t_i8) : t_i8 = wrapping_sub_i8 self rhs

let wrapping_neg400701205 (self: t_i8) : t_i8 =
  wrapping_sub973428293 (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)
    self

let wrapping_abs400396545 (self: t_i8) : t_i8 =
  if is_negative350273175 (Core.Clone.f_clone #t_i8 #FStar.Tactics.Typeclasses.solve self <: t_i8)
  then wrapping_neg400701205 self
  else self

let wrapping_add868559108 (self rhs: t_i16) : t_i16 = wrapping_add_i16 self rhs

let wrapping_sub189469152 (self rhs: t_i16) : t_i16 = wrapping_sub_i16 self rhs

let wrapping_neg860505723 (self: t_i16) : t_i16 =
  wrapping_sub189469152 (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s
      <:
      t_i16)
    self

let wrapping_abs229076826 (self: t_i16) : t_i16 =
  if is_negative477067241 (Core.Clone.f_clone #t_i16 #FStar.Tactics.Typeclasses.solve self <: t_i16)
  then wrapping_neg860505723 self
  else self

let wrapping_add475006616 (self rhs: t_i32) : t_i32 = wrapping_add_i32 self rhs

let wrapping_sub298337071 (self rhs: t_i32) : t_i32 = wrapping_sub_i32 self rhs

let wrapping_neg636433078 (self: t_i32) : t_i32 =
  wrapping_sub298337071 (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l
      <:
      t_i32)
    self

let wrapping_abs729536875 (self: t_i32) : t_i32 =
  if
    is_negative1035644813 (Core.Clone.f_clone #t_i32 #FStar.Tactics.Typeclasses.solve self <: t_i32)
  then wrapping_neg636433078 self
  else self

let wrapping_add590074241 (self rhs: t_i64) : t_i64 = wrapping_add_i64 self rhs

let wrapping_sub334584751 (self rhs: t_i64) : t_i64 = wrapping_sub_i64 self rhs

let wrapping_neg868282938 (self: t_i64) : t_i64 =
  wrapping_sub334584751 (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L
      <:
      t_i64)
    self

let wrapping_abs285829312 (self: t_i64) : t_i64 =
  if
    is_negative1066124578 (Core.Clone.f_clone #t_i64 #FStar.Tactics.Typeclasses.solve self <: t_i64)
  then wrapping_neg868282938 self
  else self

let wrapping_add251385439 (self rhs: t_i128) : t_i128 = wrapping_add_i128 self rhs

let wrapping_sub681598071 (self rhs: t_i128) : t_i128 = wrapping_sub_i128 self rhs

let wrapping_neg446546984 (self: t_i128) : t_i128 =
  wrapping_sub681598071 (Core.Convert.f_into #i128
        #t_i128
        #FStar.Tactics.Typeclasses.solve
        (pub_i128 0)
      <:
      t_i128)
    self

let wrapping_abs281925696 (self: t_i128) : t_i128 =
  if
    is_negative221698470 (Core.Clone.f_clone #t_i128 #FStar.Tactics.Typeclasses.solve self <: t_i128
      )
  then wrapping_neg446546984 self
  else self

let wrapping_add226040243 (self rhs: t_isize) : t_isize = wrapping_add_isize self rhs

let wrapping_sub698035192 (self rhs: t_isize) : t_isize = wrapping_sub_isize self rhs

let wrapping_neg912291768 (self: t_isize) : t_isize =
  wrapping_sub698035192 (Core.Convert.f_into #isize
        #t_isize
        #FStar.Tactics.Typeclasses.solve
        (isz 0)
      <:
      t_isize)
    self

let wrapping_abs347300819 (self: t_isize) : t_isize =
  if
    is_negative693446369 (Core.Clone.f_clone #t_isize #FStar.Tactics.Typeclasses.solve self
        <:
        t_isize)
  then wrapping_neg912291768 self
  else self

let checked_div508301931 (self rhs: t_u8) : Core.Option.t_Option t_u8 =
  if rhs =. (Core.Convert.f_into #u8 #t_u8 #FStar.Tactics.Typeclasses.solve 0uy <: t_u8)
  then Core.Option.Option_None <: Core.Option.t_Option t_u8
  else Core.Option.Option_Some (unchecked_div_u8 self rhs) <: Core.Option.t_Option t_u8

let overflowing_add708890057 (self rhs: t_u8) : (t_u8 & bool) = add_with_overflow_u8 self rhs

let checked_div614920780 (self rhs: t_u16) : Core.Option.t_Option t_u16 =
  if rhs =. (Core.Convert.f_into #u16 #t_u16 #FStar.Tactics.Typeclasses.solve 0us <: t_u16)
  then Core.Option.Option_None <: Core.Option.t_Option t_u16
  else Core.Option.Option_Some (unchecked_div_u16 self rhs) <: Core.Option.t_Option t_u16

let overflowing_add1023344178 (self rhs: t_u16) : (t_u16 & bool) = add_with_overflow_u16 self rhs

let checked_div979383477 (self rhs: t_u32) : Core.Option.t_Option t_u32 =
  if rhs =. (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul <: t_u32)
  then Core.Option.Option_None <: Core.Option.t_Option t_u32
  else Core.Option.Option_Some (unchecked_div_u32 self rhs) <: Core.Option.t_Option t_u32

let overflowing_add905744292 (self rhs: t_u32) : (t_u32 & bool) = add_with_overflow_u32 self rhs

let checked_div988689127 (self rhs: t_u64) : Core.Option.t_Option t_u64 =
  if rhs =. (Core.Convert.f_into #u64 #t_u64 #FStar.Tactics.Typeclasses.solve 0uL <: t_u64)
  then Core.Option.Option_None <: Core.Option.t_Option t_u64
  else Core.Option.Option_Some (unchecked_div_u64 self rhs) <: Core.Option.t_Option t_u64

let overflowing_add581983607 (self rhs: t_u64) : (t_u64 & bool) = add_with_overflow_u64 self rhs

let checked_div344106746 (self rhs: t_u128) : Core.Option.t_Option t_u128 =
  if
    rhs =.
    (Core.Convert.f_into #u128 #t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0) <: t_u128)
  then Core.Option.Option_None <: Core.Option.t_Option t_u128
  else Core.Option.Option_Some (unchecked_div_u128 self rhs) <: Core.Option.t_Option t_u128

let overflowing_add458293681 (self rhs: t_u128) : (t_u128 & bool) = add_with_overflow_u128 self rhs

let checked_div80223906 (self rhs: t_usize) : Core.Option.t_Option t_usize =
  if rhs =. (Core.Convert.f_into #usize #t_usize #FStar.Tactics.Typeclasses.solve (sz 0) <: t_usize)
  then Core.Option.Option_None <: Core.Option.t_Option t_usize
  else Core.Option.Option_Some (unchecked_div_usize self rhs) <: Core.Option.t_Option t_usize

let overflowing_add682280407 (self rhs: t_usize) : (t_usize & bool) =
  add_with_overflow_usize self rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Arith.t_Neg t_i8 =
  {
    f_Output = t_i8;
    f_neg_pre = (fun (self: t_i8) -> true);
    f_neg_post = (fun (self: t_i8) (out: t_i8) -> true);
    f_neg
    =
    fun (self: t_i8) ->
      t_i8
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I8 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i8
  }

let abs945505614 (self: t_i8) : t_i8 =
  if is_negative350273175 (Core.Clone.f_clone #t_i8 #FStar.Tactics.Typeclasses.solve self <: t_i8)
  then Core.Ops.Arith.f_neg #t_i8 #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Arith.t_Neg t_i16 =
  {
    f_Output = t_i16;
    f_neg_pre = (fun (self: t_i16) -> true);
    f_neg_post = (fun (self: t_i16) (out: t_i16) -> true);
    f_neg
    =
    fun (self: t_i16) ->
      t_i16
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I16 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i16
  }

let abs581170970 (self: t_i16) : t_i16 =
  if is_negative477067241 (Core.Clone.f_clone #t_i16 #FStar.Tactics.Typeclasses.solve self <: t_i16)
  then Core.Ops.Arith.f_neg #t_i16 #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Arith.t_Neg t_i32 =
  {
    f_Output = t_i32;
    f_neg_pre = (fun (self: t_i32) -> true);
    f_neg_post = (fun (self: t_i32) (out: t_i32) -> true);
    f_neg
    =
    fun (self: t_i32) ->
      t_i32
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I32 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i32
  }

let abs590464694 (self: t_i32) : t_i32 =
  if
    is_negative1035644813 (Core.Clone.f_clone #t_i32 #FStar.Tactics.Typeclasses.solve self <: t_i32)
  then Core.Ops.Arith.f_neg #t_i32 #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Arith.t_Neg t_i64 =
  {
    f_Output = t_i64;
    f_neg_pre = (fun (self: t_i64) -> true);
    f_neg_post = (fun (self: t_i64) (out: t_i64) -> true);
    f_neg
    =
    fun (self: t_i64) ->
      t_i64
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_i64
  }

let abs654781043 (self: t_i64) : t_i64 =
  if
    is_negative1066124578 (Core.Clone.f_clone #t_i64 #FStar.Tactics.Typeclasses.solve self <: t_i64)
  then Core.Ops.Arith.f_neg #t_i64 #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Arith.t_Neg t_i128 =
  {
    f_Output = t_i128;
    f_neg_pre = (fun (self: t_i128) -> true);
    f_neg_post = (fun (self: t_i128) (out: t_i128) -> true);
    f_neg
    =
    fun (self: t_i128) ->
      t_i128
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I128 #FStar.Tactics.Typeclasses.solve self._0
      )
      <:
      t_i128
  }

let abs204417539 (self: t_i128) : t_i128 =
  if
    is_negative221698470 (Core.Clone.f_clone #t_i128 #FStar.Tactics.Typeclasses.solve self <: t_i128
      )
  then Core.Ops.Arith.f_neg #t_i128 #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Ops.Arith.t_Neg t_isize =
  {
    f_Output = t_isize;
    f_neg_pre = (fun (self: t_isize) -> true);
    f_neg_post = (fun (self: t_isize) (out: t_isize) -> true);
    f_neg
    =
    fun (self: t_isize) ->
      t_isize
      (Core.Ops.Arith.f_neg #Core.Base_interface.Int.t_I64 #FStar.Tactics.Typeclasses.solve self._0)
      <:
      t_isize
  }

let abs220926056 (self: t_isize) : t_isize =
  if
    is_negative693446369 (Core.Clone.f_clone #t_isize #FStar.Tactics.Typeclasses.solve self
        <:
        t_isize)
  then Core.Ops.Arith.f_neg #t_isize #FStar.Tactics.Typeclasses.solve self
  else self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_84: Core.Ops.Bit.t_BitOr t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_bitor_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_bitor_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_bitor = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 |. other._0) <: t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_85: Core.Ops.Bit.t_BitOr t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_bitor_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_bitor_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_bitor = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 |. other._0) <: t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_86: Core.Ops.Bit.t_BitOr t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_bitor_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_bitor_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_bitor = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 |. other._0) <: t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_87: Core.Ops.Bit.t_BitOr t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_bitor_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_bitor_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_bitor = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 |. other._0) <: t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_88: Core.Ops.Bit.t_BitOr t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_bitor_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_bitor_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_bitor = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 |. other._0) <: t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_89: Core.Ops.Bit.t_BitOr t_isize t_isize =
  {
    f_Output = t_isize;
    f_bitor_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_bitor_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_bitor = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 |. other._0) <: t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Convert.t_From t_u16 t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: t_u16) -> true);
    f_from
    =
    fun (x: t_u8) ->
      t_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Convert.t_From t_u32 t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: t_u32) -> true);
    f_from
    =
    fun (x: t_u8) ->
      t_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Convert.t_From t_u64 t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: t_u64) -> true);
    f_from
    =
    fun (x: t_u8) ->
      t_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Convert.t_From t_u128 t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: t_u128) -> true);
    f_from
    =
    fun (x: t_u8) ->
      t_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Convert.t_From t_usize t_u8 =
  {
    f_from_pre = (fun (x: t_u8) -> true);
    f_from_post = (fun (x: t_u8) (out: t_usize) -> true);
    f_from
    =
    fun (x: t_u8) ->
      t_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U8
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Convert.t_From t_u8 t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: t_u8) -> true);
    f_from
    =
    fun (x: t_u16) ->
      t_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Convert.t_From t_u32 t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: t_u32) -> true);
    f_from
    =
    fun (x: t_u16) ->
      t_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Convert.t_From t_u64 t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: t_u64) -> true);
    f_from
    =
    fun (x: t_u16) ->
      t_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Convert.t_From t_u128 t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: t_u128) -> true);
    f_from
    =
    fun (x: t_u16) ->
      t_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Convert.t_From t_usize t_u16 =
  {
    f_from_pre = (fun (x: t_u16) -> true);
    f_from_post = (fun (x: t_u16) (out: t_usize) -> true);
    f_from
    =
    fun (x: t_u16) ->
      t_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U16
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Convert.t_From t_u8 t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: t_u8) -> true);
    f_from
    =
    fun (x: t_u32) ->
      t_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Convert.t_From t_u16 t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: t_u16) -> true);
    f_from
    =
    fun (x: t_u32) ->
      t_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Convert.t_From t_u64 t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: t_u64) -> true);
    f_from
    =
    fun (x: t_u32) ->
      t_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Convert.t_From t_u128 t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: t_u128) -> true);
    f_from
    =
    fun (x: t_u32) ->
      t_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Convert.t_From t_usize t_u32 =
  {
    f_from_pre = (fun (x: t_u32) -> true);
    f_from_post = (fun (x: t_u32) (out: t_usize) -> true);
    f_from
    =
    fun (x: t_u32) ->
      t_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U32
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Convert.t_From t_u8 t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: t_u8) -> true);
    f_from
    =
    fun (x: t_u64) ->
      t_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Convert.t_From t_u16 t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: t_u16) -> true);
    f_from
    =
    fun (x: t_u64) ->
      t_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Convert.t_From t_u32 t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: t_u32) -> true);
    f_from
    =
    fun (x: t_u64) ->
      t_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Convert.t_From t_u128 t_u64 =
  {
    f_from_pre = (fun (x: t_u64) -> true);
    f_from_post = (fun (x: t_u64) (out: t_u128) -> true);
    f_from
    =
    fun (x: t_u64) ->
      t_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Convert.t_From t_u8 t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: t_u8) -> true);
    f_from
    =
    fun (x: t_u128) ->
      t_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Convert.t_From t_u16 t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: t_u16) -> true);
    f_from
    =
    fun (x: t_u128) ->
      t_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Convert.t_From t_u32 t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: t_u32) -> true);
    f_from
    =
    fun (x: t_u128) ->
      t_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Convert.t_From t_u64 t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: t_u64) -> true);
    f_from
    =
    fun (x: t_u128) ->
      t_u64
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Convert.t_From t_usize t_u128 =
  {
    f_from_pre = (fun (x: t_u128) -> true);
    f_from_post = (fun (x: t_u128) (out: t_usize) -> true);
    f_from
    =
    fun (x: t_u128) ->
      t_usize
      (Core.Convert.f_into #Core.Base_interface.Int.t_U128
          #Core.Base_interface.Int.t_U64
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Convert.t_From t_u8 t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: t_u8) -> true);
    f_from
    =
    fun (x: t_usize) ->
      t_u8
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U8
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Convert.t_From t_u16 t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: t_u16) -> true);
    f_from
    =
    fun (x: t_usize) ->
      t_u16
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U16
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Convert.t_From t_u32 t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: t_u32) -> true);
    f_from
    =
    fun (x: t_usize) ->
      t_u32
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U32
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Convert.t_From t_u128 t_usize =
  {
    f_from_pre = (fun (x: t_usize) -> true);
    f_from_post = (fun (x: t_usize) (out: t_u128) -> true);
    f_from
    =
    fun (x: t_usize) ->
      t_u128
      (Core.Convert.f_into #Core.Base_interface.Int.t_U64
          #Core.Base_interface.Int.t_U128
          #FStar.Tactics.Typeclasses.solve
          x._0)
      <:
      t_u128
  }

let unchecked_div_i128 (x y: t_i128) : t_i128 =
  t_i128
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I128
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I128)
  <:
  t_i128

let unchecked_div_i16 (x y: t_i16) : t_i16 =
  t_i16
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I16
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I16)
  <:
  t_i16

let unchecked_div_i32 (x y: t_i32) : t_i32 =
  t_i32
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I32
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I32)
  <:
  t_i32

let unchecked_div_i64 (x y: t_i64) : t_i64 =
  t_i64
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  t_i64

let unchecked_div_i8 (x y: t_i8) : t_i8 =
  t_i8
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I8
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I8)
  <:
  t_i8

let unchecked_div_isize (x y: t_isize) : t_isize =
  t_isize
  ({
      Core.Base_interface.Int.f_v
      =
      Core.Base.Z.z_div (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            x._0
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Base_interface.Coerce.f_lift #Core.Base_interface.Int.t_I64
            #FStar.Tactics.Typeclasses.solve
            y._0
          <:
          Core.Base.Spec.Z.t_Z)
    }
    <:
    Core.Base_interface.Int.t_I64)
  <:
  t_isize

let wrapping_add_u128 (a b: t_u128) : t_u128 = t_u128 (a._0 +! b._0) <: t_u128

let wrapping_add_u16 (a b: t_u16) : t_u16 = t_u16 (a._0 +! b._0) <: t_u16

let wrapping_add_u32 (a b: t_u32) : t_u32 = t_u32 (a._0 +! b._0) <: t_u32

let wrapping_add_u64 (a b: t_u64) : t_u64 = t_u64 (a._0 +! b._0) <: t_u64

let wrapping_add_u8 (a b: t_u8) : t_u8 = t_u8 (a._0 +! b._0) <: t_u8

let wrapping_add_usize (a b: t_usize) : t_usize = t_usize (a._0 +! b._0) <: t_usize

let wrapping_mul_i128 (a b: t_i128) : t_i128 = t_i128 (a._0 *! b._0) <: t_i128

let wrapping_mul_i16 (a b: t_i16) : t_i16 = t_i16 (a._0 *! b._0) <: t_i16

let wrapping_mul_i32 (a b: t_i32) : t_i32 = t_i32 (a._0 *! b._0) <: t_i32

let wrapping_mul_i64 (a b: t_i64) : t_i64 = t_i64 (a._0 *! b._0) <: t_i64

let wrapping_mul_i8 (a b: t_i8) : t_i8 = t_i8 (a._0 *! b._0) <: t_i8

let wrapping_mul_isize (a b: t_isize) : t_isize = t_isize (a._0 *! b._0) <: t_isize

let wrapping_mul_u128 (a b: t_u128) : t_u128 = t_u128 (a._0 *! b._0) <: t_u128

let wrapping_mul_u16 (a b: t_u16) : t_u16 = t_u16 (a._0 *! b._0) <: t_u16

let wrapping_mul_u32 (a b: t_u32) : t_u32 = t_u32 (a._0 *! b._0) <: t_u32

let wrapping_mul_u64 (a b: t_u64) : t_u64 = t_u64 (a._0 *! b._0) <: t_u64

let wrapping_mul_u8 (a b: t_u8) : t_u8 = t_u8 (a._0 *! b._0) <: t_u8

let wrapping_mul_usize (a b: t_usize) : t_usize = t_usize (a._0 *! b._0) <: t_usize

let wrapping_add480603777 (self rhs: t_u8) : t_u8 = wrapping_add_u8 self rhs

let wrapping_mul885216284 (self rhs: t_u8) : t_u8 = wrapping_mul_u8 self rhs

let wrapping_add124432709 (self rhs: t_u16) : t_u16 = wrapping_add_u16 self rhs

let wrapping_mul14465189 (self rhs: t_u16) : t_u16 = wrapping_mul_u16 self rhs

let wrapping_add1049665857 (self rhs: t_u32) : t_u32 = wrapping_add_u32 self rhs

let wrapping_mul203346768 (self rhs: t_u32) : t_u32 = wrapping_mul_u32 self rhs

let wrapping_add865565639 (self rhs: t_u64) : t_u64 = wrapping_add_u64 self rhs

let wrapping_mul742978873 (self rhs: t_u64) : t_u64 = wrapping_mul_u64 self rhs

let wrapping_add40844100 (self rhs: t_u128) : t_u128 = wrapping_add_u128 self rhs

let wrapping_mul294115024 (self rhs: t_u128) : t_u128 = wrapping_mul_u128 self rhs

let wrapping_add427637036 (self rhs: t_usize) : t_usize = wrapping_add_usize self rhs

let wrapping_mul680896953 (self rhs: t_usize) : t_usize = wrapping_mul_usize self rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Ops.Arith.t_Add t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_add_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_add_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_add = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 +! other._0) <: t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Ops.Arith.t_Add t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_add_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_add_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_add = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 +! other._0) <: t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Ops.Arith.t_Add t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_add_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_add_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_add = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 +! other._0) <: t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Ops.Arith.t_Add t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_add_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_add_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_add = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 +! other._0) <: t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Arith.t_Add t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_add_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_add_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_add = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 +! other._0) <: t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Arith.t_Add t_isize t_isize =
  {
    f_Output = t_isize;
    f_add_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_add_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_add = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 +! other._0) <: t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Ops.Arith.t_Sub t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_sub_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_sub_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_sub = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 -! other._0) <: t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Ops.Arith.t_Sub t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_sub_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_sub_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_sub = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 -! other._0) <: t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Arith.t_Sub t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_sub_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_sub_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_sub = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 -! other._0) <: t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Ops.Arith.t_Sub t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_sub_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_sub_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_sub = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 -! other._0) <: t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Ops.Arith.t_Sub t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_sub_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_sub_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_sub = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 -! other._0) <: t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Ops.Arith.t_Sub t_isize t_isize =
  {
    f_Output = t_isize;
    f_sub_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_sub_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_sub = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 -! other._0) <: t_isize
  }

let wrapping_sub_u128 (a b: t_u128) : t_u128 = t_u128 (a._0 -! b._0) <: t_u128

let wrapping_sub_u16 (a b: t_u16) : t_u16 = t_u16 (a._0 -! b._0) <: t_u16

let wrapping_sub_u32 (a b: t_u32) : t_u32 = t_u32 (a._0 -! b._0) <: t_u32

let wrapping_sub_u64 (a b: t_u64) : t_u64 = t_u64 (a._0 -! b._0) <: t_u64

let wrapping_sub_u8 (a b: t_u8) : t_u8 = t_u8 (a._0 -! b._0) <: t_u8

let wrapping_sub_usize (a b: t_usize) : t_usize = t_usize (a._0 -! b._0) <: t_usize

let wrapping_sub403906422 (self rhs: t_u8) : t_u8 = wrapping_sub_u8 self rhs

let wrapping_neg123212788 (self: t_u8) : t_u8 =
  wrapping_sub403906422 (t_u8
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U8)
      <:
      t_u8)
    self

let wrapping_sub811251034 (self rhs: t_u16) : t_u16 = wrapping_sub_u16 self rhs

let wrapping_neg128555595 (self: t_u16) : t_u16 =
  wrapping_sub811251034 (t_u16
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U16)
      <:
      t_u16)
    self

let wrapping_sub708953500 (self rhs: t_u32) : t_u32 = wrapping_sub_u32 self rhs

let wrapping_neg328220773 (self: t_u32) : t_u32 =
  wrapping_sub708953500 (t_u32
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U32)
      <:
      t_u32)
    self

let wrapping_sub762520851 (self rhs: t_u64) : t_u64 = wrapping_sub_u64 self rhs

let wrapping_neg617136337 (self: t_u64) : t_u64 =
  wrapping_sub762520851 (t_u64
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U64)
      <:
      t_u64)
    self

let wrapping_sub409310259 (self rhs: t_u128) : t_u128 = wrapping_sub_u128 self rhs

let wrapping_neg729451428 (self: t_u128) : t_u128 =
  wrapping_sub409310259 (t_u128
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U128)
      <:
      t_u128)
    self

let wrapping_sub813101882 (self rhs: t_usize) : t_usize = wrapping_sub_usize self rhs

let wrapping_neg342773446 (self: t_usize) : t_usize =
  wrapping_sub813101882 (t_usize
      (Core.Base_interface.Int.f_ZERO #FStar.Tactics.Typeclasses.solve
        <:
        Core.Base_interface.Int.t_U64)
      <:
      t_usize)
    self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Arith.t_Add t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_add_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_add_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_add = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 +! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Ops.Arith.t_Add t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_add_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_add_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_add = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 +! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Arith.t_Add t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_add_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_add_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_add = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 +! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Arith.t_Add t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_add_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_add_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_add = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 +! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Ops.Arith.t_Add t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_add_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_add_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_add = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 +! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Ops.Arith.t_Add t_usize t_usize =
  {
    f_Output = t_usize;
    f_add_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_add_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_add = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 +! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Ops.Arith.t_Mul t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_mul_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_mul_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_mul = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 *! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Ops.Arith.t_Mul t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_mul_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_mul_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_mul = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 *! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Arith.t_Mul t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_mul_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_mul_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_mul = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 *! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Arith.t_Mul t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_mul_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_mul_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_mul = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 *! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Arith.t_Mul t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_mul_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_mul_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_mul = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 *! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Arith.t_Mul t_usize t_usize =
  {
    f_Output = t_usize;
    f_mul_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_mul_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_mul = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 *! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Ops.Arith.t_Mul t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_mul_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_mul_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_mul = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 *! other._0) <: t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Ops.Arith.t_Mul t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_mul_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_mul_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_mul = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 *! other._0) <: t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Arith.t_Mul t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_mul_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_mul_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_mul = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 *! other._0) <: t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Arith.t_Mul t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_mul_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_mul_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_mul = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 *! other._0) <: t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Arith.t_Mul t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_mul_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_mul_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_mul = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 *! other._0) <: t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Arith.t_Mul t_isize t_isize =
  {
    f_Output = t_isize;
    f_mul_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_mul_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_mul = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 *! other._0) <: t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Ops.Arith.t_Div t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_div_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_div_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_div = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 /! other._0) <: t_u8
  }

let wrapping_div660080892 (self rhs: t_u8) : t_u8 = self /! rhs

let wrapping_div_euclid481233436 (self rhs: t_u8) : t_u8 = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Ops.Arith.t_Div t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_div_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_div_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_div = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 /! other._0) <: t_u16
  }

let wrapping_div366977334 (self rhs: t_u16) : t_u16 = self /! rhs

let wrapping_div_euclid22267888 (self rhs: t_u16) : t_u16 = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Arith.t_Div t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_div_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_div_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_div = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 /! other._0) <: t_u32
  }

let wrapping_div931150450 (self rhs: t_u32) : t_u32 = self /! rhs

let wrapping_div_euclid606291997 (self rhs: t_u32) : t_u32 = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Arith.t_Div t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_div_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_div_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_div = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 /! other._0) <: t_u64
  }

let wrapping_div168427046 (self rhs: t_u64) : t_u64 = self /! rhs

let wrapping_div_euclid321252086 (self rhs: t_u64) : t_u64 = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Arith.t_Div t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_div_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_div_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_div = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 /! other._0) <: t_u128
  }

let wrapping_div692427683 (self rhs: t_u128) : t_u128 = self /! rhs

let wrapping_div_euclid926334515 (self rhs: t_u128) : t_u128 = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Ops.Arith.t_Div t_usize t_usize =
  {
    f_Output = t_usize;
    f_div_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_div_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_div = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 /! other._0) <: t_usize
  }

let wrapping_div905768546 (self rhs: t_usize) : t_usize = self /! rhs

let wrapping_div_euclid90317722 (self rhs: t_usize) : t_usize = self /! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Ops.Arith.t_Rem t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_rem_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_rem_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_rem = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 %! other._0) <: t_u8
  }

let wrapping_rem984569721 (self rhs: t_u8) : t_u8 = self %! rhs

let wrapping_rem_euclid946579345 (self rhs: t_u8) : t_u8 = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Ops.Arith.t_Rem t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_rem_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_rem_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_rem = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 %! other._0) <: t_u16
  }

let wrapping_rem378598035 (self rhs: t_u16) : t_u16 = self %! rhs

let wrapping_rem_euclid602402638 (self rhs: t_u16) : t_u16 = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Ops.Arith.t_Rem t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_rem_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_rem_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_rem = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 %! other._0) <: t_u32
  }

let wrapping_rem292009099 (self rhs: t_u32) : t_u32 = self %! rhs

let wrapping_rem_euclid1020271291 (self rhs: t_u32) : t_u32 = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Arith.t_Rem t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_rem_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_rem_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_rem = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 %! other._0) <: t_u64
  }

let wrapping_rem390602260 (self rhs: t_u64) : t_u64 = self %! rhs

let wrapping_rem_euclid839264546 (self rhs: t_u64) : t_u64 = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Arith.t_Rem t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_rem_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_rem_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_rem = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 %! other._0) <: t_u128
  }

let wrapping_rem332379920 (self rhs: t_u128) : t_u128 = self %! rhs

let wrapping_rem_euclid646122423 (self rhs: t_u128) : t_u128 = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Arith.t_Rem t_usize t_usize =
  {
    f_Output = t_usize;
    f_rem_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_rem_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_rem = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 %! other._0) <: t_usize
  }

let wrapping_rem333089373 (self rhs: t_usize) : t_usize = self %! rhs

let wrapping_rem_euclid769656504 (self rhs: t_usize) : t_usize = self %! rhs

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: Core.Ops.Bit.t_Shr t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: Core.Ops.Bit.t_Shr t_u8 t_u16 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_u16) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_u16) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: Core.Ops.Bit.t_Shr t_u8 t_u32 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_u32) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_u32) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_9: Core.Ops.Bit.t_Shr t_u8 t_u64 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_u64) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_u64) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_10: Core.Ops.Bit.t_Shr t_u8 t_u128 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_u128) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_u128) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_11: Core.Ops.Bit.t_Shr t_u8 t_usize =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_u8) (other: t_usize) (out: t_u8) -> true);
    f_shr = fun (self: t_u8) (other: t_usize) -> t_u8 (self._0 >>! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_12: Core.Ops.Bit.t_Shr t_u16 t_u8 =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_u8) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_u8) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_13: Core.Ops.Bit.t_Shr t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_14: Core.Ops.Bit.t_Shr t_u16 t_u32 =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_u32) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_u32) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_15: Core.Ops.Bit.t_Shr t_u16 t_u64 =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_u64) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_u64) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_16: Core.Ops.Bit.t_Shr t_u16 t_u128 =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_u128) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_u128) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Ops.Bit.t_Shr t_u16 t_usize =
  {
    f_Output = t_u16;
    f_shr_pre = (fun (self: t_u16) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_u16) (other: t_usize) (out: t_u16) -> true);
    f_shr = fun (self: t_u16) (other: t_usize) -> t_u16 (self._0 >>! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Ops.Bit.t_Shr t_u32 t_u8 =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_u8) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_u8) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Ops.Bit.t_Shr t_u32 t_u16 =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_u16) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_u16) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Ops.Bit.t_Shr t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Bit.t_Shr t_u32 t_u64 =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_u64) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_u64) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Bit.t_Shr t_u32 t_u128 =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_u128) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_u128) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Ops.Bit.t_Shr t_u32 t_usize =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_u32) (other: t_usize) (out: t_u32) -> true);
    f_shr = fun (self: t_u32) (other: t_usize) -> t_u32 (self._0 >>! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_24: Core.Ops.Bit.t_Shr t_u64 t_u8 =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_u8) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_u8) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_25: Core.Ops.Bit.t_Shr t_u64 t_u16 =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_u16) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_u16) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_26: Core.Ops.Bit.t_Shr t_u64 t_u32 =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_u32) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_u32) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_27: Core.Ops.Bit.t_Shr t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_28: Core.Ops.Bit.t_Shr t_u64 t_u128 =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_u128) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_u128) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_29: Core.Ops.Bit.t_Shr t_u64 t_usize =
  {
    f_Output = t_u64;
    f_shr_pre = (fun (self: t_u64) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_u64) (other: t_usize) (out: t_u64) -> true);
    f_shr = fun (self: t_u64) (other: t_usize) -> t_u64 (self._0 >>! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_30: Core.Ops.Bit.t_Shr t_u128 t_u8 =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_u8) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_u8) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_31: Core.Ops.Bit.t_Shr t_u128 t_u16 =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_u16) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_u16) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_32: Core.Ops.Bit.t_Shr t_u128 t_u32 =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_u32) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_u32) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_33: Core.Ops.Bit.t_Shr t_u128 t_u64 =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_u64) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_u64) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_34: Core.Ops.Bit.t_Shr t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_35: Core.Ops.Bit.t_Shr t_u128 t_usize =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_u128) (other: t_usize) (out: t_u128) -> true);
    f_shr = fun (self: t_u128) (other: t_usize) -> t_u128 (self._0 >>! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_36: Core.Ops.Bit.t_Shr t_usize t_u8 =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_u8) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_u8) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_u8) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_37: Core.Ops.Bit.t_Shr t_usize t_u16 =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_u16) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_u16) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_u16) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_38: Core.Ops.Bit.t_Shr t_usize t_u32 =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_u32) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_u32) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_u32) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_39: Core.Ops.Bit.t_Shr t_usize t_u64 =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_u64) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_u64) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_u64) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_40: Core.Ops.Bit.t_Shr t_usize t_u128 =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_u128) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_u128) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_u128) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_41: Core.Ops.Bit.t_Shr t_usize t_usize =
  {
    f_Output = t_usize;
    f_shr_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_shr_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_shr = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 >>! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_42: Core.Ops.Bit.t_Shl t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_43: Core.Ops.Bit.t_Shl t_u8 t_u16 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_u16) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_u16) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_44: Core.Ops.Bit.t_Shl t_u8 t_u32 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_u32) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_u32) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_45: Core.Ops.Bit.t_Shl t_u8 t_u64 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_u64) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_u64) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_46: Core.Ops.Bit.t_Shl t_u8 t_u128 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_u128) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_u128) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_47: Core.Ops.Bit.t_Shl t_u8 t_usize =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_u8) (other: t_usize) (out: t_u8) -> true);
    f_shl = fun (self: t_u8) (other: t_usize) -> t_u8 (self._0 <<! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Ops.Bit.t_Shl t_u16 t_u8 =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_u8) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_u8) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Ops.Bit.t_Shl t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Ops.Bit.t_Shl t_u16 t_u32 =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_u32) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_u32) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Bit.t_Shl t_u16 t_u64 =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_u64) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_u64) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Bit.t_Shl t_u16 t_u128 =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_u128) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_u128) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Bit.t_Shl t_u16 t_usize =
  {
    f_Output = t_u16;
    f_shl_pre = (fun (self: t_u16) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_u16) (other: t_usize) (out: t_u16) -> true);
    f_shl = fun (self: t_u16) (other: t_usize) -> t_u16 (self._0 <<! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_54: Core.Ops.Bit.t_Shl t_u32 t_u8 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_u8) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_u8) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_55: Core.Ops.Bit.t_Shl t_u32 t_u16 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_u16) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_u16) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_56: Core.Ops.Bit.t_Shl t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_57: Core.Ops.Bit.t_Shl t_u32 t_u64 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_u64) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_u64) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_58: Core.Ops.Bit.t_Shl t_u32 t_u128 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_u128) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_u128) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_59: Core.Ops.Bit.t_Shl t_u32 t_usize =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_u32) (other: t_usize) (out: t_u32) -> true);
    f_shl = fun (self: t_u32) (other: t_usize) -> t_u32 (self._0 <<! other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Bit.t_Shl t_u64 t_u8 =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_u8) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_u8) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Bit.t_Shl t_u64 t_u16 =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_u16) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_u16) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Bit.t_Shl t_u64 t_u32 =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_u32) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_u32) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Bit.t_Shl t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Ops.Bit.t_Shl t_u64 t_u128 =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_u128) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_u128) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Ops.Bit.t_Shl t_u64 t_usize =
  {
    f_Output = t_u64;
    f_shl_pre = (fun (self: t_u64) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_u64) (other: t_usize) (out: t_u64) -> true);
    f_shl = fun (self: t_u64) (other: t_usize) -> t_u64 (self._0 <<! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_66: Core.Ops.Bit.t_Shl t_u128 t_u8 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_u8) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_u8) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_67: Core.Ops.Bit.t_Shl t_u128 t_u16 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_u16) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_u16) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_68: Core.Ops.Bit.t_Shl t_u128 t_u32 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_u32) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_u32) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_69: Core.Ops.Bit.t_Shl t_u128 t_u64 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_u64) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_u64) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_70: Core.Ops.Bit.t_Shl t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_71: Core.Ops.Bit.t_Shl t_u128 t_usize =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_u128) (other: t_usize) (out: t_u128) -> true);
    f_shl = fun (self: t_u128) (other: t_usize) -> t_u128 (self._0 <<! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_72: Core.Ops.Bit.t_Shl t_usize t_u8 =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_u8) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_u8) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_u8) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_73: Core.Ops.Bit.t_Shl t_usize t_u16 =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_u16) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_u16) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_u16) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_74: Core.Ops.Bit.t_Shl t_usize t_u32 =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_u32) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_u32) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_u32) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_75: Core.Ops.Bit.t_Shl t_usize t_u64 =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_u64) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_u64) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_u64) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_76: Core.Ops.Bit.t_Shl t_usize t_u128 =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_u128) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_u128) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_u128) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_77: Core.Ops.Bit.t_Shl t_usize t_usize =
  {
    f_Output = t_usize;
    f_shl_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_shl_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_shl = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 <<! other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_78: Core.Ops.Bit.t_BitOr t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_bitor_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_bitor_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_bitor = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 |. other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_79: Core.Ops.Bit.t_BitOr t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_bitor_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_bitor_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_bitor = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 |. other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_80: Core.Ops.Bit.t_BitOr t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_bitor_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_bitor_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_bitor = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 |. other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_81: Core.Ops.Bit.t_BitOr t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_bitor_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_bitor_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_bitor = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 |. other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_82: Core.Ops.Bit.t_BitOr t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_bitor_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_bitor_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_bitor = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 |. other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_83: Core.Ops.Bit.t_BitOr t_usize t_usize =
  {
    f_Output = t_usize;
    f_bitor_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_bitor_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_bitor = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 |. other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_90: Core.Ops.Bit.t_BitXor t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_bitxor_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_bitxor_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_bitxor = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 ^. other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_91: Core.Ops.Bit.t_BitXor t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_bitxor_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_bitxor_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_bitxor = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 ^. other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_92: Core.Ops.Bit.t_BitXor t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_bitxor_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_bitxor_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_bitxor = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 ^. other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_93: Core.Ops.Bit.t_BitXor t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_bitxor_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_bitxor_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_bitxor = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 ^. other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_94: Core.Ops.Bit.t_BitXor t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_bitxor_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_bitxor_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_bitxor = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 ^. other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_95: Core.Ops.Bit.t_BitXor t_usize t_usize =
  {
    f_Output = t_usize;
    f_bitxor_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_bitxor_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_bitxor = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 ^. other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_96: Core.Ops.Bit.t_BitAnd t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_bitand_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_bitand_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_bitand = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 &. other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_97: Core.Ops.Bit.t_BitAnd t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_bitand_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_bitand_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_bitand = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 &. other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_98: Core.Ops.Bit.t_BitAnd t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_bitand_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_bitand_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_bitand = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 &. other._0) <: t_u32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_99: Core.Ops.Bit.t_BitAnd t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_bitand_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_bitand_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_bitand = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 &. other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_100: Core.Ops.Bit.t_BitAnd t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_bitand_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_bitand_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_bitand = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 &. other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_101: Core.Ops.Bit.t_BitAnd t_usize t_usize =
  {
    f_Output = t_usize;
    f_bitand_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_bitand_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_bitand = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 &. other._0) <: t_usize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Ops.Arith.t_Sub t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_sub_pre = (fun (self: t_u8) (other: t_u8) -> true);
    f_sub_post = (fun (self: t_u8) (other: t_u8) (out: t_u8) -> true);
    f_sub = fun (self: t_u8) (other: t_u8) -> t_u8 (self._0 -! other._0) <: t_u8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_19: Core.Ops.Arith.t_Sub t_u16 t_u16 =
  {
    f_Output = t_u16;
    f_sub_pre = (fun (self: t_u16) (other: t_u16) -> true);
    f_sub_post = (fun (self: t_u16) (other: t_u16) (out: t_u16) -> true);
    f_sub = fun (self: t_u16) (other: t_u16) -> t_u16 (self._0 -! other._0) <: t_u16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_20: Core.Ops.Arith.t_Sub t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_sub_pre = (fun (self: t_u32) (other: t_u32) -> true);
    f_sub_post = (fun (self: t_u32) (other: t_u32) (out: t_u32) -> true);
    f_sub = fun (self: t_u32) (other: t_u32) -> t_u32 (self._0 -! other._0) <: t_u32
  }

let rotate_left_u128 (x: t_u128) (shift: t_u32) : t_u128 =
  let (shift: t_u32):t_u32 = shift %! v_BITS136999051 in
  let (left: t_u128):t_u128 =
    (Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u128):t_u128 =
    (Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) >>!
    (v_BITS136999051 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left_u16 (x: t_u16) (shift: t_u32) : t_u16 =
  let (shift: t_u32):t_u32 = shift %! v_BITS277333551 in
  let (left: t_u16):t_u16 =
    (Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u16):t_u16 =
    (Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) >>!
    (v_BITS277333551 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left_u32 (x shift: t_u32) : t_u32 =
  let (shift: t_u32):t_u32 = shift %! v_BITS473478051 in
  let (left: t_u32):t_u32 =
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u32):t_u32 =
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) >>!
    (v_BITS473478051 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left_u64 (x: t_u64) (shift: t_u32) : t_u64 =
  let (shift: t_u32):t_u32 = shift %! v_BITS177666292 in
  let (left: t_u64):t_u64 =
    (Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u64):t_u64 =
    (Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) >>!
    (v_BITS177666292 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left_u8 (x: t_u8) (shift: t_u32) : t_u8 =
  let (shift: t_u32):t_u32 = shift %! v_BITS690311813 in
  let (left: t_u8):t_u8 =
    (Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u8):t_u8 =
    (Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) >>!
    (v_BITS690311813 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left_usize (x: t_usize) (shift: t_u32) : t_usize =
  let (shift: t_u32):t_u32 = shift %! v_BITS229952196 in
  let (left: t_usize):t_usize =
    (Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) <<!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_usize):t_usize =
    (Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) >>!
    (v_BITS229952196 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_u128 (x: t_u128) (shift: t_u32) : t_u128 =
  let (shift: t_u32):t_u32 = shift %! v_BITS136999051 in
  let (left: t_u128):t_u128 =
    (Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u128):t_u128 =
    (Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) <<!
    (v_BITS136999051 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_u16 (x: t_u16) (shift: t_u32) : t_u16 =
  let (shift: t_u32):t_u32 = shift %! v_BITS277333551 in
  let (left: t_u16):t_u16 =
    (Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u16):t_u16 =
    (Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) <<!
    (v_BITS277333551 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_u32 (x shift: t_u32) : t_u32 =
  let (shift: t_u32):t_u32 = shift %! v_BITS473478051 in
  let (left: t_u32):t_u32 =
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u32):t_u32 =
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) <<!
    (v_BITS473478051 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_u64 (x: t_u64) (shift: t_u32) : t_u64 =
  let (shift: t_u32):t_u32 = shift %! v_BITS177666292 in
  let (left: t_u64):t_u64 =
    (Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u64):t_u64 =
    (Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) <<!
    (v_BITS177666292 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_u8 (x: t_u8) (shift: t_u32) : t_u8 =
  let (shift: t_u32):t_u32 = shift %! v_BITS690311813 in
  let (left: t_u8):t_u8 =
    (Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_u8):t_u8 =
    (Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) <<!
    (v_BITS690311813 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_right_usize (x: t_usize) (shift: t_u32) : t_usize =
  let (shift: t_u32):t_u32 = shift %! v_BITS229952196 in
  let (left: t_usize):t_usize =
    (Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) >>!
    (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
  in
  let (right: t_usize):t_usize =
    (Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) <<!
    (v_BITS229952196 -! (Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve shift <: t_u32)
      <:
      t_u32)
  in
  left |. right

let rotate_left792925914 (self: t_u8) (n: t_u32) : t_u8 = rotate_left_u8 self n

let rotate_right166090082 (self: t_u8) (n: t_u32) : t_u8 = rotate_right_u8 self n

let rotate_left297034175 (self: t_u16) (n: t_u32) : t_u16 = rotate_left_u16 self n

let rotate_right138522246 (self: t_u16) (n: t_u32) : t_u16 = rotate_right_u16 self n

let rotate_left823573251 (self n: t_u32) : t_u32 = rotate_left_u32 self n

let rotate_right869195717 (self n: t_u32) : t_u32 = rotate_right_u32 self n

let rotate_left618936072 (self: t_u64) (n: t_u32) : t_u64 = rotate_left_u64 self n

let rotate_right1041614027 (self: t_u64) (n: t_u32) : t_u64 = rotate_right_u64 self n

let rotate_left1065866885 (self: t_u128) (n: t_u32) : t_u128 = rotate_left_u128 self n

let rotate_right591112338 (self: t_u128) (n: t_u32) : t_u128 = rotate_right_u128 self n

let rotate_left996672710 (self: t_usize) (n: t_u32) : t_usize = rotate_left_usize self n

let rotate_right442734174 (self: t_usize) (n: t_u32) : t_usize = rotate_right_usize self n

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_21: Core.Ops.Arith.t_Sub t_u64 t_u64 =
  {
    f_Output = t_u64;
    f_sub_pre = (fun (self: t_u64) (other: t_u64) -> true);
    f_sub_post = (fun (self: t_u64) (other: t_u64) (out: t_u64) -> true);
    f_sub = fun (self: t_u64) (other: t_u64) -> t_u64 (self._0 -! other._0) <: t_u64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_22: Core.Ops.Arith.t_Sub t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_sub_pre = (fun (self: t_u128) (other: t_u128) -> true);
    f_sub_post = (fun (self: t_u128) (other: t_u128) (out: t_u128) -> true);
    f_sub = fun (self: t_u128) (other: t_u128) -> t_u128 (self._0 -! other._0) <: t_u128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_23: Core.Ops.Arith.t_Sub t_usize t_usize =
  {
    f_Output = t_usize;
    f_sub_pre = (fun (self: t_usize) (other: t_usize) -> true);
    f_sub_post = (fun (self: t_usize) (other: t_usize) (out: t_usize) -> true);
    f_sub = fun (self: t_usize) (other: t_usize) -> t_usize (self._0 -! other._0) <: t_usize
  }

let bswap_u128 (x: t_u128) : t_u128 =
  let (count: t_u128):t_u128 =
    Core.Convert.f_into #u128 #t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 0)
  in
  let count:t_u128 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS136999051 <: u32)
      (fun count temp_1_ ->
          let count:t_u128 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u128 = count in
          let i:u32 = i in
          let (low_bit: t_u128):t_u128 =
            Core.Convert.f_into #t_u128
              #t_u128
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u128) &.
                (Core.Convert.f_into #u128 #t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 1)
                  <:
                  t_u128)
                <:
                t_u128)
          in
          let count:t_u128 =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_u128) +!
            low_bit
          in
          count)
  in
  count

let bswap_u16 (x: t_u16) : t_u16 =
  let (count: t_u16):t_u16 = Core.Convert.f_into #u16 #t_u16 #FStar.Tactics.Typeclasses.solve 0us in
  let count:t_u16 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS277333551 <: u32)
      (fun count temp_1_ ->
          let count:t_u16 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u16 = count in
          let i:u32 = i in
          let (low_bit: t_u16):t_u16 =
            Core.Convert.f_into #t_u16
              #t_u16
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u16) &.
                (Core.Convert.f_into #u16 #t_u16 #FStar.Tactics.Typeclasses.solve 1us <: t_u16)
                <:
                t_u16)
          in
          let count:t_u16 =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_u16) +!
            low_bit
          in
          count)
  in
  count

let bswap_u32 (x: t_u32) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS473478051 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u32
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u32) &.
                (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
                <:
                t_u32)
          in
          let count:t_u32 =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_u32) +!
            low_bit
          in
          count)
  in
  count

let bswap_u64 (x: t_u64) : t_u64 =
  let (count: t_u64):t_u64 = Core.Convert.f_into #u64 #t_u64 #FStar.Tactics.Typeclasses.solve 0uL in
  let count:t_u64 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS177666292 <: u32)
      (fun count temp_1_ ->
          let count:t_u64 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u64 = count in
          let i:u32 = i in
          let (low_bit: t_u64):t_u64 =
            Core.Convert.f_into #t_u64
              #t_u64
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u64) &.
                (Core.Convert.f_into #u64 #t_u64 #FStar.Tactics.Typeclasses.solve 1uL <: t_u64)
                <:
                t_u64)
          in
          let count:t_u64 =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_u64) +!
            low_bit
          in
          count)
  in
  count

let bswap_u8 (x: t_u8) : t_u8 =
  let (count: t_u8):t_u8 = Core.Convert.f_into #u8 #t_u8 #FStar.Tactics.Typeclasses.solve 0uy in
  let count:t_u8 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS690311813 <: u32)
      (fun count temp_1_ ->
          let count:t_u8 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u8 = count in
          let i:u32 = i in
          let (low_bit: t_u8):t_u8 =
            Core.Convert.f_into #t_u8
              #t_u8
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u8) &.
                (Core.Convert.f_into #u8 #t_u8 #FStar.Tactics.Typeclasses.solve 1uy <: t_u8)
                <:
                t_u8)
          in
          let count:t_u8 =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_u8) +!
            low_bit
          in
          count)
  in
  count

let bswap_usize (x: t_usize) : t_usize =
  let (count: t_usize):t_usize =
    Core.Convert.f_into #usize #t_usize #FStar.Tactics.Typeclasses.solve (sz 0)
  in
  let count:t_usize =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS229952196 <: u32)
      (fun count temp_1_ ->
          let count:t_usize = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_usize = count in
          let i:u32 = i in
          let (low_bit: t_usize):t_usize =
            Core.Convert.f_into #t_usize
              #t_usize
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_usize) &.
                (Core.Convert.f_into #usize #t_usize #FStar.Tactics.Typeclasses.solve (sz 1)
                  <:
                  t_usize)
                <:
                t_usize)
          in
          let count:t_usize =
            (count <<!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
              <:
              t_usize) +!
            low_bit
          in
          count)
  in
  count

let ctlz_u128 (x: t_u128) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS136999051 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u128
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u128) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS136999051 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_u128)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctlz_u16 (x: t_u16) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS277333551 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u16
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u16) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS277333551 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_u16)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctlz_u32 (x: t_u32) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS473478051 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u32
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u32) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS473478051 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_u32)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctlz_u64 (x: t_u64) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS177666292 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u64
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u64) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS177666292 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_u64)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctlz_u8 (x: t_u8) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS690311813 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u8
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u8) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS690311813 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_u8)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctlz_usize (x: t_usize) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS229952196 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (high_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_usize
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) <<!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_usize) >>!
                (Core.Convert.f_into #t_u32
                    #t_u32
                    #FStar.Tactics.Typeclasses.solve
                    (v_BITS229952196 -!
                      (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32
                      )
                      <:
                      t_u32)
                  <:
                  t_u32)
                <:
                t_usize)
          in
          if
            high_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let ctpop_u128 (x: t_u128) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS136999051 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_u128
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u128) &.
                (Core.Convert.f_into #u128 #t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 1)
                  <:
                  t_u128)
                <:
                t_u128)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let ctpop_u16 (x: t_u16) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS277333551 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_u16
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u16) &.
                (Core.Convert.f_into #u16 #t_u16 #FStar.Tactics.Typeclasses.solve 1us <: t_u16)
                <:
                t_u16)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let ctpop_u32 (x: t_u32) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS473478051 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_u32
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u32) &.
                (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
                <:
                t_u32)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let ctpop_u64 (x: t_u64) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS177666292 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_u64
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u64) &.
                (Core.Convert.f_into #u64 #t_u64 #FStar.Tactics.Typeclasses.solve 1uL <: t_u64)
                <:
                t_u64)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let ctpop_u8 (x: t_u8) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS690311813 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_u8
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u8) &.
                (Core.Convert.f_into #u8 #t_u8 #FStar.Tactics.Typeclasses.solve 1uy <: t_u8)
                <:
                t_u8)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let ctpop_usize (x: t_usize) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let count:t_u32 =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS229952196 <: u32)
      (fun count temp_1_ ->
          let count:t_u32 = count in
          let _:u32 = temp_1_ in
          true)
      count
      (fun count i ->
          let count:t_u32 = count in
          let i:u32 = i in
          count +!
          (Core.Convert.f_into #t_usize
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_usize) &.
                (Core.Convert.f_into #usize #t_usize #FStar.Tactics.Typeclasses.solve (sz 1)
                  <:
                  t_usize)
                <:
                t_usize)
            <:
            t_u32)
          <:
          t_u32)
  in
  count

let cttz_u128 (x: t_u128) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS136999051 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u128
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u128 #FStar.Tactics.Typeclasses.solve x <: t_u128) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u128) &.
                (Core.Convert.f_into #u128 #t_u128 #FStar.Tactics.Typeclasses.solve (pub_u128 1)
                  <:
                  t_u128)
                <:
                t_u128)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let cttz_u16 (x: t_u16) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS277333551 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u16
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u16 #FStar.Tactics.Typeclasses.solve x <: t_u16) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u16) &.
                (Core.Convert.f_into #u16 #t_u16 #FStar.Tactics.Typeclasses.solve 1us <: t_u16)
                <:
                t_u16)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let cttz_u32 (x: t_u32) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS473478051 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u32
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u32 #FStar.Tactics.Typeclasses.solve x <: t_u32) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u32) &.
                (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
                <:
                t_u32)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let cttz_u64 (x: t_u64) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS177666292 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u64
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u64 #FStar.Tactics.Typeclasses.solve x <: t_u64) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u64) &.
                (Core.Convert.f_into #u64 #t_u64 #FStar.Tactics.Typeclasses.solve 1uL <: t_u64)
                <:
                t_u64)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let cttz_u8 (x: t_u8) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS690311813 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_u8
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_u8 #FStar.Tactics.Typeclasses.solve x <: t_u8) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_u8) &.
                (Core.Convert.f_into #u8 #t_u8 #FStar.Tactics.Typeclasses.solve 1uy <: t_u8)
                <:
                t_u8)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let cttz_usize (x: t_usize) : t_u32 =
  let (count: t_u32):t_u32 = Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 0ul in
  let done:bool = false in
  let count, done:(t_u32 & bool) =
    Rust_primitives.Hax.Folds.fold_range 0ul
      (Core.Convert.f_into #t_u32 #u32 #FStar.Tactics.Typeclasses.solve v_BITS229952196 <: u32)
      (fun temp_0_ temp_1_ ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let _:u32 = temp_1_ in
          true)
      (count, done <: (t_u32 & bool))
      (fun temp_0_ i ->
          let count, done:(t_u32 & bool) = temp_0_ in
          let i:u32 = i in
          let (low_bit: t_u32):t_u32 =
            Core.Convert.f_into #t_usize
              #t_u32
              #FStar.Tactics.Typeclasses.solve
              (((Core.Clone.f_clone #t_usize #FStar.Tactics.Typeclasses.solve x <: t_usize) >>!
                  (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve i <: t_u32)
                  <:
                  t_usize) &.
                (Core.Convert.f_into #usize #t_usize #FStar.Tactics.Typeclasses.solve (sz 1)
                  <:
                  t_usize)
                <:
                t_usize)
          in
          if
            low_bit =.
            (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32) ||
            done
          then
            let done:bool = true in
            count, done <: (t_u32 & bool)
          else
            let count:t_u32 =
              count +!
              (Core.Convert.f_into #u32 #t_u32 #FStar.Tactics.Typeclasses.solve 1ul <: t_u32)
            in
            count, done <: (t_u32 & bool))
  in
  count

let count_ones202509899 (self: t_u8) : t_u32 = ctpop_u8 self

let leading_zeros75047366 (self: t_u8) : t_u32 = ctlz_u8 self

let swap_bytes657156997 (self: t_u8) : t_u8 =
  Core.Convert.f_into #t_u8 #t_u8 #FStar.Tactics.Typeclasses.solve (bswap_u8 self <: t_u8)

let from_be746282521 (x: t_u8) : t_u8 = swap_bytes657156997 x

let to_be972448780 (self: t_u8) : t_u8 = swap_bytes657156997 self

let trailing_zeros572929871 (self: t_u8) : t_u32 = cttz_u8 self

let count_ones91875752 (self: t_u16) : t_u32 = ctpop_u16 self

let leading_zeros462412478 (self: t_u16) : t_u32 = ctlz_u16 self

let swap_bytes926722059 (self: t_u16) : t_u16 =
  Core.Convert.f_into #t_u16 #t_u16 #FStar.Tactics.Typeclasses.solve (bswap_u16 self <: t_u16)

let from_be510959665 (x: t_u16) : t_u16 = swap_bytes926722059 x

let to_be551590602 (self: t_u16) : t_u16 = swap_bytes926722059 self

let trailing_zeros421474733 (self: t_u16) : t_u32 = cttz_u16 self

let count_ones776185738 (self: t_u32) : t_u32 = ctpop_u32 self

let leading_zeros698221972 (self: t_u32) : t_u32 = ctlz_u32 self

let swap_bytes320480126 (self: t_u32) : t_u32 =
  Core.Convert.f_into #t_u32 #t_u32 #FStar.Tactics.Typeclasses.solve (bswap_u32 self <: t_u32)

let from_be664756649 (x: t_u32) : t_u32 = swap_bytes320480126 x

let to_be82825962 (self: t_u32) : t_u32 = swap_bytes320480126 self

let trailing_zeros1061560720 (self: t_u32) : t_u32 = cttz_u32 self

let count_ones235885653 (self: t_u64) : t_u32 = ctpop_u64 self

let leading_zeros338302110 (self: t_u64) : t_u32 = ctlz_u64 self

let swap_bytes722254271 (self: t_u64) : t_u64 =
  Core.Convert.f_into #t_u64 #t_u64 #FStar.Tactics.Typeclasses.solve (bswap_u64 self <: t_u64)

let from_be16013635 (x: t_u64) : t_u64 = swap_bytes722254271 x

let to_be376714729 (self: t_u64) : t_u64 = swap_bytes722254271 self

let trailing_zeros188346231 (self: t_u64) : t_u32 = cttz_u64 self

let count_ones926736261 (self: t_u128) : t_u32 = ctpop_u128 self

let leading_zeros19644612 (self: t_u128) : t_u32 = ctlz_u128 self

let swap_bytes420879368 (self: t_u128) : t_u128 =
  Core.Convert.f_into #t_u128 #t_u128 #FStar.Tactics.Typeclasses.solve (bswap_u128 self <: t_u128)

let from_be191085771 (x: t_u128) : t_u128 = swap_bytes420879368 x

let to_be555075987 (self: t_u128) : t_u128 = swap_bytes420879368 self

let trailing_zeros821715250 (self: t_u128) : t_u32 = cttz_u128 self

let count_ones441645762 (self: t_usize) : t_u32 = ctpop_usize self

let leading_zeros905233489 (self: t_usize) : t_u32 = ctlz_usize self

let swap_bytes268673424 (self: t_usize) : t_usize =
  Core.Convert.f_into #t_usize
    #t_usize
    #FStar.Tactics.Typeclasses.solve
    (bswap_usize self <: t_usize)

let from_be607978059 (x: t_usize) : t_usize = swap_bytes268673424 x

let to_be561847134 (self: t_usize) : t_usize = swap_bytes268673424 self

let trailing_zeros42066260 (self: t_usize) : t_u32 = cttz_usize self

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_48: Core.Ops.Arith.t_Div t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_div_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_div_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_div = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 /! other._0) <: t_i8
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_49: Core.Ops.Arith.t_Div t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_div_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_div_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_div = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 /! other._0) <: t_i16
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_50: Core.Ops.Arith.t_Div t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_div_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_div_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_div = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 /! other._0) <: t_i32
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_51: Core.Ops.Arith.t_Div t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_div_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_div_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_div = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 /! other._0) <: t_i64
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_52: Core.Ops.Arith.t_Div t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_div_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_div_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_div = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 /! other._0) <: t_i128
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_53: Core.Ops.Arith.t_Div t_isize t_isize =
  {
    f_Output = t_isize;
    f_div_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_div_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_div = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 /! other._0) <: t_isize
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_60: Core.Ops.Arith.t_Rem t_i8 t_i8 =
  {
    f_Output = t_i8;
    f_rem_pre = (fun (self: t_i8) (other: t_i8) -> true);
    f_rem_post = (fun (self: t_i8) (other: t_i8) (out: t_i8) -> true);
    f_rem = fun (self: t_i8) (other: t_i8) -> t_i8 (self._0 %! other._0) <: t_i8
  }

let rem_euclid622298453 (self rhs: t_i8) : t_i8 =
  let r:t_i8 = self %! (Core.Clone.f_clone #t_i8 #FStar.Tactics.Typeclasses.solve rhs <: t_i8) in
  if r <. (Core.Convert.f_into #i8 #t_i8 #FStar.Tactics.Typeclasses.solve 0y <: t_i8)
  then wrapping_add634491935 r (wrapping_abs400396545 rhs <: t_i8)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_61: Core.Ops.Arith.t_Rem t_i16 t_i16 =
  {
    f_Output = t_i16;
    f_rem_pre = (fun (self: t_i16) (other: t_i16) -> true);
    f_rem_post = (fun (self: t_i16) (other: t_i16) (out: t_i16) -> true);
    f_rem = fun (self: t_i16) (other: t_i16) -> t_i16 (self._0 %! other._0) <: t_i16
  }

let rem_euclid158017644 (self rhs: t_i16) : t_i16 =
  let r:t_i16 = self %! (Core.Clone.f_clone #t_i16 #FStar.Tactics.Typeclasses.solve rhs <: t_i16) in
  if r <. (Core.Convert.f_into #i16 #t_i16 #FStar.Tactics.Typeclasses.solve 0s <: t_i16)
  then wrapping_add868559108 r (wrapping_abs229076826 rhs <: t_i16)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_62: Core.Ops.Arith.t_Rem t_i32 t_i32 =
  {
    f_Output = t_i32;
    f_rem_pre = (fun (self: t_i32) (other: t_i32) -> true);
    f_rem_post = (fun (self: t_i32) (other: t_i32) (out: t_i32) -> true);
    f_rem = fun (self: t_i32) (other: t_i32) -> t_i32 (self._0 %! other._0) <: t_i32
  }

let rem_euclid881249982 (self rhs: t_i32) : t_i32 =
  let r:t_i32 = self %! (Core.Clone.f_clone #t_i32 #FStar.Tactics.Typeclasses.solve rhs <: t_i32) in
  if r <. (Core.Convert.f_into #i32 #t_i32 #FStar.Tactics.Typeclasses.solve 0l <: t_i32)
  then wrapping_add475006616 r (wrapping_abs729536875 rhs <: t_i32)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_63: Core.Ops.Arith.t_Rem t_i64 t_i64 =
  {
    f_Output = t_i64;
    f_rem_pre = (fun (self: t_i64) (other: t_i64) -> true);
    f_rem_post = (fun (self: t_i64) (other: t_i64) (out: t_i64) -> true);
    f_rem = fun (self: t_i64) (other: t_i64) -> t_i64 (self._0 %! other._0) <: t_i64
  }

let rem_euclid1057082210 (self rhs: t_i64) : t_i64 =
  let r:t_i64 = self %! (Core.Clone.f_clone #t_i64 #FStar.Tactics.Typeclasses.solve rhs <: t_i64) in
  if r <. (Core.Convert.f_into #i64 #t_i64 #FStar.Tactics.Typeclasses.solve 0L <: t_i64)
  then wrapping_add590074241 r (wrapping_abs285829312 rhs <: t_i64)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_64: Core.Ops.Arith.t_Rem t_i128 t_i128 =
  {
    f_Output = t_i128;
    f_rem_pre = (fun (self: t_i128) (other: t_i128) -> true);
    f_rem_post = (fun (self: t_i128) (other: t_i128) (out: t_i128) -> true);
    f_rem = fun (self: t_i128) (other: t_i128) -> t_i128 (self._0 %! other._0) <: t_i128
  }

let rem_euclid254910751 (self rhs: t_i128) : t_i128 =
  let r:t_i128 =
    self %! (Core.Clone.f_clone #t_i128 #FStar.Tactics.Typeclasses.solve rhs <: t_i128)
  in
  if
    r <. (Core.Convert.f_into #i128 #t_i128 #FStar.Tactics.Typeclasses.solve (pub_i128 0) <: t_i128)
  then wrapping_add251385439 r (wrapping_abs281925696 rhs <: t_i128)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_65: Core.Ops.Arith.t_Rem t_isize t_isize =
  {
    f_Output = t_isize;
    f_rem_pre = (fun (self: t_isize) (other: t_isize) -> true);
    f_rem_post = (fun (self: t_isize) (other: t_isize) (out: t_isize) -> true);
    f_rem = fun (self: t_isize) (other: t_isize) -> t_isize (self._0 %! other._0) <: t_isize
  }

let rem_euclid828379367 (self rhs: t_isize) : t_isize =
  let r:t_isize =
    self %! (Core.Clone.f_clone #t_isize #FStar.Tactics.Typeclasses.solve rhs <: t_isize)
  in
  if r <. (Core.Convert.f_into #isize #t_isize #FStar.Tactics.Typeclasses.solve (isz 0) <: t_isize)
  then wrapping_add226040243 r (wrapping_abs347300819 rhs <: t_isize)
  else r

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Ops.Bit.t_Not t_u8 =
  {
    f_Output = t_u8;
    f_not_pre = (fun (self: t_u8) -> true);
    f_not_post = (fun (self: t_u8) (out: t_u8) -> true);
    f_not = fun (self: t_u8) -> t_u8 ~.self._0 <: t_u8
  }

let count_zeros558337492 (self: t_u8) : t_u32 = count_ones202509899 (~.self <: t_u8)

let leading_ones55148479 (self: t_u8) : t_u32 = leading_zeros75047366 (~.self <: t_u8)

let trailing_ones359778731 (self: t_u8) : t_u32 = trailing_zeros572929871 (~.self <: t_u8)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Ops.Bit.t_Not t_u16 =
  {
    f_Output = t_u16;
    f_not_pre = (fun (self: t_u16) -> true);
    f_not_post = (fun (self: t_u16) (out: t_u16) -> true);
    f_not = fun (self: t_u16) -> t_u16 ~.self._0 <: t_u16
  }

let count_zeros199825317 (self: t_u16) : t_u32 = count_ones91875752 (~.self <: t_u16)

let leading_ones164277656 (self: t_u16) : t_u32 = leading_zeros462412478 (~.self <: t_u16)

let trailing_ones903944727 (self: t_u16) : t_u32 = trailing_zeros421474733 (~.self <: t_u16)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: Core.Ops.Bit.t_Not t_u32 =
  {
    f_Output = t_u32;
    f_not_pre = (fun (self: t_u32) -> true);
    f_not_post = (fun (self: t_u32) (out: t_u32) -> true);
    f_not = fun (self: t_u32) -> t_u32 ~.self._0 <: t_u32
  }

let count_zeros942566041 (self: t_u32) : t_u32 = count_ones776185738 (~.self <: t_u32)

let leading_ones766486760 (self: t_u32) : t_u32 = leading_zeros698221972 (~.self <: t_u32)

let trailing_ones223371510 (self: t_u32) : t_u32 = trailing_zeros1061560720 (~.self <: t_u32)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Ops.Bit.t_Not t_u64 =
  {
    f_Output = t_u64;
    f_not_pre = (fun (self: t_u64) -> true);
    f_not_post = (fun (self: t_u64) (out: t_u64) -> true);
    f_not = fun (self: t_u64) -> t_u64 ~.self._0 <: t_u64
  }

let count_zeros60346158 (self: t_u64) : t_u32 = count_ones235885653 (~.self <: t_u64)

let leading_ones404666910 (self: t_u64) : t_u32 = leading_zeros338302110 (~.self <: t_u64)

let trailing_ones601201120 (self: t_u64) : t_u32 = trailing_zeros188346231 (~.self <: t_u64)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: Core.Ops.Bit.t_Not t_u128 =
  {
    f_Output = t_u128;
    f_not_pre = (fun (self: t_u128) -> true);
    f_not_post = (fun (self: t_u128) (out: t_u128) -> true);
    f_not = fun (self: t_u128) -> t_u128 ~.self._0 <: t_u128
  }

let count_zeros824862815 (self: t_u128) : t_u32 = count_ones926736261 (~.self <: t_u128)

let leading_ones475503572 (self: t_u128) : t_u32 = leading_zeros19644612 (~.self <: t_u128)

let trailing_ones705845381 (self: t_u128) : t_u32 = trailing_zeros821715250 (~.self <: t_u128)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: Core.Ops.Bit.t_Not t_usize =
  {
    f_Output = t_usize;
    f_not_pre = (fun (self: t_usize) -> true);
    f_not_post = (fun (self: t_usize) (out: t_usize) -> true);
    f_not = fun (self: t_usize) -> t_usize ~.self._0 <: t_usize
  }

let count_zeros73479642 (self: t_usize) : t_u32 = count_ones441645762 (~.self <: t_usize)

let leading_ones667660708 (self: t_usize) : t_u32 = leading_zeros905233489 (~.self <: t_usize)

let trailing_ones979548463 (self: t_usize) : t_u32 = trailing_zeros42066260 (~.self <: t_usize)
