module Prelude
#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"

open Core.Array
open Core.Primitive
open Core.Base.Int.Number_conversion
open Core.Convert
open Core.Base.Int
open Core.Ops.Arith
open Core.Ops.Bit
// open Core.Num
open Core.Int

let array_of_list n l : t_Array u8 (sz n) =
  { f_v = l }

let v_RCON: t_Array u8 (sz 15) =
  let list =
    [(pub_u8 141); (pub_u8 1); (pub_u8 2); (pub_u8 4); (pub_u8 8); (pub_u8 16); (pub_u8 32); (pub_u8 64); (pub_u8 128); (pub_u8 27); (pub_u8 54); (pub_u8 108); (pub_u8 216); (pub_u8 171); (pub_u8 77)]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 15);
  array_of_list 15 list

let v_SBOX: t_Array u8 (sz 256) =
  let list =
    [
      (pub_u8 99); (pub_u8 124); (pub_u8 119); (pub_u8 123); (pub_u8 242); (pub_u8 107); (pub_u8 111); (pub_u8 197); (pub_u8 48); (pub_u8 1); (pub_u8 103); (pub_u8 43); (pub_u8 254); (pub_u8 215);
      (pub_u8 171); (pub_u8 118); (pub_u8 202); (pub_u8 130); (pub_u8 201); (pub_u8 125); (pub_u8 250); (pub_u8 89); (pub_u8 71); (pub_u8 240); (pub_u8 173); (pub_u8 212); (pub_u8 162); (pub_u8 175);
      (pub_u8 156); (pub_u8 164); (pub_u8 114); (pub_u8 192); (pub_u8 183); (pub_u8 253); (pub_u8 147); (pub_u8 38); (pub_u8 54); (pub_u8 63); (pub_u8 247); (pub_u8 204); (pub_u8 52); (pub_u8 165);
      (pub_u8 229); (pub_u8 241); (pub_u8 113); (pub_u8 216); (pub_u8 49); (pub_u8 21); (pub_u8 4); (pub_u8 199); (pub_u8 35); (pub_u8 195); (pub_u8 24); (pub_u8 150); (pub_u8 5); (pub_u8 154); (pub_u8 7);
      (pub_u8 18); (pub_u8 128); (pub_u8 226); (pub_u8 235); (pub_u8 39); (pub_u8 178); (pub_u8 117); (pub_u8 9); (pub_u8 131); (pub_u8 44); (pub_u8 26); (pub_u8 27); (pub_u8 110); (pub_u8 90);
      (pub_u8 160); (pub_u8 82); (pub_u8 59); (pub_u8 214); (pub_u8 179); (pub_u8 41); (pub_u8 227); (pub_u8 47); (pub_u8 132); (pub_u8 83); (pub_u8 209); (pub_u8 0); (pub_u8 237); (pub_u8 32);
      (pub_u8 252); (pub_u8 177); (pub_u8 91); (pub_u8 106); (pub_u8 203); (pub_u8 190); (pub_u8 57); (pub_u8 74); (pub_u8 76); (pub_u8 88); (pub_u8 207); (pub_u8 208); (pub_u8 239); (pub_u8 170);
      (pub_u8 251); (pub_u8 67); (pub_u8 77); (pub_u8 51); (pub_u8 133); (pub_u8 69); (pub_u8 249); (pub_u8 2); (pub_u8 127); (pub_u8 80); (pub_u8 60); (pub_u8 159); (pub_u8 168); (pub_u8 81); (pub_u8 163);
      (pub_u8 64); (pub_u8 143); (pub_u8 146); (pub_u8 157); (pub_u8 56); (pub_u8 245); (pub_u8 188); (pub_u8 182); (pub_u8 218); (pub_u8 33); (pub_u8 16); (pub_u8 255); (pub_u8 243); (pub_u8 210);
      (pub_u8 205); (pub_u8 12); (pub_u8 19); (pub_u8 236); (pub_u8 95); (pub_u8 151); (pub_u8 68); (pub_u8 23); (pub_u8 196); (pub_u8 167); (pub_u8 126); (pub_u8 61); (pub_u8 100); (pub_u8 93);
      (pub_u8 25); (pub_u8 115); (pub_u8 96); (pub_u8 129); (pub_u8 79); (pub_u8 220); (pub_u8 34); (pub_u8 42); (pub_u8 144); (pub_u8 136); (pub_u8 70); (pub_u8 238); (pub_u8 184); (pub_u8 20);
      (pub_u8 222); (pub_u8 94); (pub_u8 11); (pub_u8 219); (pub_u8 224); (pub_u8 50); (pub_u8 58); (pub_u8 10); (pub_u8 73); (pub_u8 6); (pub_u8 36); (pub_u8 92); (pub_u8 194); (pub_u8 211); (pub_u8 172);
      (pub_u8 98); (pub_u8 145); (pub_u8 149); (pub_u8 228); (pub_u8 121); (pub_u8 231); (pub_u8 200); (pub_u8 55); (pub_u8 109); (pub_u8 141); (pub_u8 213); (pub_u8 78); (pub_u8 169); (pub_u8 108);
      (pub_u8 86); (pub_u8 244); (pub_u8 234); (pub_u8 101); (pub_u8 122); (pub_u8 174); (pub_u8 8); (pub_u8 186); (pub_u8 120); (pub_u8 37); (pub_u8 46); (pub_u8 28); (pub_u8 166); (pub_u8 180);
      (pub_u8 198); (pub_u8 232); (pub_u8 221); (pub_u8 116); (pub_u8 31); (pub_u8 75); (pub_u8 189); (pub_u8 139); (pub_u8 138); (pub_u8 112); (pub_u8 62); (pub_u8 181); (pub_u8 102); (pub_u8 72);
      (pub_u8 3); (pub_u8 246); (pub_u8 14); (pub_u8 97); (pub_u8 53); (pub_u8 87); (pub_u8 185); (pub_u8 134); (pub_u8 193); (pub_u8 29); (pub_u8 158); (pub_u8 225); (pub_u8 248); (pub_u8 152);
      (pub_u8 17); (pub_u8 105); (pub_u8 217); (pub_u8 142); (pub_u8 148); (pub_u8 155); (pub_u8 30); (pub_u8 135); (pub_u8 233); (pub_u8 206); (pub_u8 85); (pub_u8 40); (pub_u8 223); (pub_u8 140);
      (pub_u8 161); (pub_u8 137); (pub_u8 13); (pub_u8 191); (pub_u8 230); (pub_u8 66); (pub_u8 104); (pub_u8 65); (pub_u8 153); (pub_u8 45); (pub_u8 15); (pub_u8 176); (pub_u8 84); (pub_u8 187);
      (pub_u8 22)
    ]
  in
  FStar.Pervasives.assert_norm (Prims.eq2 (List.Tot.length list) 256);
  array_of_list 256 list

(* Manually added *)
class t_Cast (v_Self: Type0) (v_T: Type0) = {
  cast_pre:v_T -> Type0;
  cast_post:v_T -> v_Self -> Type0;
  cast:x0: v_T -> Prims.Pure v_Self (cast_pre x0) (fun result -> cast_post x0 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_cast_u128_u32 : t_Cast u32 u128 =
  {
    cast_pre = (fun (self: t_u128) -> true);
    cast_post = (fun (self: t_u128) (out: t_u32) -> true);
    cast
    =
    fun (self: t_u128) -> C_u32 ({f_v = (match self with C_u128 v -> v.f_v % pow2 32)} <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_cast_u32_u128 : t_Cast u128 u32 =
  {
    cast_pre = (fun (self: t_u32) -> true);
    cast_post = (fun (self: t_u32) (out: t_u128) -> true);
    cast
    =
    fun (self: t_u32) -> C_u128 ({f_v = (match self with C_u32 v -> v.f_v)} <: t_U128)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_cast_u32_u8 : t_Cast u8 u32 =
  {
    cast_pre = (fun (self: t_u32) -> true);
    cast_post = (fun (self: t_u32) (out: t_u8) -> true);
    cast
    =
    fun (self: t_u32) -> C_u8 ({f_v = (match self with C_u32 v -> v.f_v % pow2 8)} <: t_U8)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_cast_u8_u32 : t_Cast u32 u8 =
  {
    cast_pre = (fun (self: t_u8) -> true);
    cast_post = (fun (self: t_u8) (out: t_u32) -> true);
    cast
    =
    fun (self: t_u8) -> C_u32 ({f_v = (match self with C_u8 v -> v.f_v)} <: t_U32)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_cast_u8_usize : t_Cast usize u8 =
  {
    cast_pre = (fun (self: t_u8) -> true);
    cast_post = (fun (self: t_u8) (out: t_usize) -> true);
    cast
    =
    fun (self: t_u8) -> C_usize ({f_v = (match self with C_u8 v -> v.f_v)} <: t_U64)
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_shr_u128: Core.Ops.Bit.t_Shr t_u128 t_usize =
  {
    f_Output = t_u128;
    f_shr_pre = (fun (self: t_u128) (rhs: t_usize) -> true);
    f_shr_post = (fun (self: t_u128) (rhs: t_usize) (out: t_u128) -> true);
    f_shr
    =
    fun (self: t_u128) (rhs: t_usize) -> C_u128 ((match self with C_u128 v -> v <: t_U128) >>! (match rhs with C_usize v -> v <: t_U64))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_shr_u32_usize: Core.Ops.Bit.t_Shr t_u32 t_usize =
  {
    f_Output = t_u32;
    f_shr_pre = (fun (self: t_u32) (rhs: t_usize) -> true);
    f_shr_post = (fun (self: t_u32) (rhs: t_usize) (out: t_u32) -> true);
    f_shr
    =
    fun (self: t_u32) (rhs: t_usize) -> C_u32 ((match self with C_u32 v -> v <: t_U32) >>! (match rhs with C_usize v -> v <: t_U64))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_shr_u8_usize: Core.Ops.Bit.t_Shr t_u8 t_usize =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (rhs: t_usize) -> true);
    f_shr_post = (fun (self: t_u8) (rhs: t_usize) (out: t_u8) -> true);
    f_shr
    =
    fun (self: t_u8) (rhs: t_usize) -> C_u8 ((match self with C_u8 v -> v <: t_U8) >>! (match rhs with C_usize v -> v <: t_U64))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_shr_u8_u128: Core.Ops.Bit.t_Shr t_u8 t_u128 =
  {
    f_Output = t_u8;
    f_shr_pre = (fun (self: t_u8) (rhs: t_u128) -> true);
    f_shr_post = (fun (self: t_u8) (rhs: t_u128) (out: t_u8) -> true);
    f_shr
    =
    fun (self: t_u8) (rhs: t_u128) -> C_u8 ((match self with C_u8 v -> v <: t_U8) >>! (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_u128_u128: Core.Ops.Bit.t_Shl t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_shl_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_shl_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_shl
    =
    fun (self: t_u128) (rhs: t_u128) -> C_u128 ((match self with C_u128 v -> v <: t_U128) <<! (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_u32_u128: Core.Ops.Bit.t_Shl t_u32 t_u128 =
  {
    f_Output = t_u32;
    f_shl_pre = (fun (self: t_u32) (rhs: t_u128) -> true);
    f_shl_post = (fun (self: t_u32) (rhs: t_u128) (out: t_u32) -> true);
    f_shl
    =
    fun (self: t_u32) (rhs: t_u128) -> C_u32 ((match self with C_u32 v -> v <: t_U32) <<! (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_u8_u128: Core.Ops.Bit.t_Shl t_u8 t_u128 =
  {
    f_Output = t_u8;
    f_shl_pre = (fun (self: t_u8) (rhs: t_u128) -> true);
    f_shl_post = (fun (self: t_u8) (rhs: t_u128) (out: t_u8) -> true);
    f_shl
    =
    fun (self: t_u8) (rhs: t_u128) -> C_u8 ((match self with C_u8 v -> v <: t_U8) <<! (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitor_u128: Core.Ops.Bit.t_BitOr t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_bitor_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_bitor_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_bitor
    =
    fun (self: t_u128) (rhs: t_u128) -> C_u128 ((match self with C_u128 v -> v <: t_U128) |. (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitor_u32: Core.Ops.Bit.t_BitOr t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_bitor_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_bitor_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_bitor
    =
    fun (self: t_u32) (rhs: t_u32) -> C_u32 ((match self with C_u32 v -> v <: t_U32) |. (match rhs with C_u32 v -> v <: t_U32))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitxor_u32: Core.Ops.Bit.t_BitXor t_u32 t_u32 =
  {
    f_Output = t_u32;
    f_bitxor_pre = (fun (self: t_u32) (rhs: t_u32) -> true);
    f_bitxor_post = (fun (self: t_u32) (rhs: t_u32) (out: t_u32) -> true);
    f_bitxor
    =
    fun (self: t_u32) (rhs: t_u32) -> C_u32 ((match self with C_u32 v -> v <: t_U32) ^. (match rhs with C_u32 v -> v <: t_U32))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitxor_u128: Core.Ops.Bit.t_BitXor t_u128 t_u128 =
  {
    f_Output = t_u128;
    f_bitxor_pre = (fun (self: t_u128) (rhs: t_u128) -> true);
    f_bitxor_post = (fun (self: t_u128) (rhs: t_u128) (out: t_u128) -> true);
    f_bitxor
    =
    fun (self: t_u128) (rhs: t_u128) -> C_u128 ((match self with C_u128 v -> v <: t_U128) ^. (match rhs with C_u128 v -> v <: t_U128))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitxor_u8: Core.Ops.Bit.t_BitXor t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_bitxor_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_bitxor_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_bitxor
    =
    fun (self: t_u8) (rhs: t_u8) -> C_u8 ((match self with C_u8 v -> v <: t_U8) ^. (match rhs with C_u8 v -> v <: t_U8))
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_bitand_u8: Core.Ops.Bit.t_BitAnd t_u8 t_u8 =
  {
    f_Output = t_u8;
    f_bitand_pre = (fun (self: t_u8) (rhs: t_u8) -> true);
    f_bitand_post = (fun (self: t_u8) (rhs: t_u8) (out: t_u8) -> true);
    f_bitand
    =
    fun (self: t_u8) (rhs: t_u8) -> C_u8 ((match self with C_u8 v -> v <: t_U8) &. (match rhs with C_u8 v -> v <: t_U8))
  }

(* / Manually added *)

let index_u32 (s: u128) (i: usize) : u32 =
  cast ((s >>! (i *! sz 32 <: usize) <: u128) %! (pub_u128 1 <<! (pub_u128 32) <: u128) <: u128) <: u32

let index_u8 (s: u32) (i: usize) : u8 =
  cast ((s >>! (i *! sz 8 <: usize) <: u32) %! ((pub_u32 1) <<! (pub_u128 8) <: u32) <: u32) <: u8

let matrix_index (s: u128) (i j: usize) : u8 = index_u8 (index_u32 s j <: u32) i

let rebuild_u128 (s0 s1 s2 s3: u32) : u128 =
  (cast (s0 <: u32) <: u128) |.
  (((cast (s1 <: u32) <: u128) <<! (pub_u128 32) <: u128) |.
    (((cast (s2 <: u32) <: u128) <<! (pub_u128 64) <: u128) |. ((cast (s3 <: u32) <: u128) <<! (pub_u128 96) <: u128)
      <:
      u128)
    <:
    u128)

let rebuild_u32 (s0 s1 s2 s3: u8) : u32 =
  (cast (s0 <: u8) <: u32) |.
  (((cast (s1 <: u8) <: u32) <<! (pub_u128 8) <: u32) |.
    (((cast (s2 <: u8) <: u32) <<! (pub_u128 16) <: u32) |. ((cast (s3 <: u8) <: u32) <<! (pub_u128 24) <: u32) <: u32)
    <:
    u32)

let rotword (v: u32) : u32 =
  rebuild_u32 (index_u8 v (sz 1) <: u8)
    (index_u8 v (sz 2) <: u8)
    (index_u8 v (sz 3) <: u8)
    (index_u8 v (sz 0) <: u8)

let shiftrows (s: u128) : u128 =
  rebuild_u128 (rebuild_u32 (matrix_index s (sz 0) (sz 0) <: u8)
        (matrix_index s (sz 1) (sz 1) <: u8)
        (matrix_index s (sz 2) (sz 2) <: u8)
        (matrix_index s (sz 3) (sz 3) <: u8)
      <:
      u32)
    (rebuild_u32 (matrix_index s (sz 0) (sz 1) <: u8)
        (matrix_index s (sz 1) (sz 2) <: u8)
        (matrix_index s (sz 2) (sz 3) <: u8)
        (matrix_index s (sz 3) (sz 0) <: u8)
      <:
      u32)
    (rebuild_u32 (matrix_index s (sz 0) (sz 2) <: u8)
        (matrix_index s (sz 1) (sz 3) <: u8)
        (matrix_index s (sz 2) (sz 0) <: u8)
        (matrix_index s (sz 3) (sz 1) <: u8)
      <:
      u32)
    (rebuild_u32 (matrix_index s (sz 0) (sz 3) <: u8)
        (matrix_index s (sz 1) (sz 0) <: u8)
        (matrix_index s (sz 2) (sz 1) <: u8)
        (matrix_index s (sz 3) (sz 2) <: u8)
      <:
      u32)

let (.[] ) (#v_T : eqtype) #v_N (#[FStar.Tactics.Typeclasses.tcresolve ()] i2: Core.Clone.t_Clone v_T) = (impl_2__index #v_T v_N #i2)

#set-options "--fuel 400 --ifuel 10 --z3rlimit 120"
// let sub0_guar250 (v: u8 {match v with | C_u8 v -> v.f_v < 256}) = impl_2__index #u8 (sz 256) (v_SBOX) (sz 255) <: u8

let sub0_not (v: u8) = (v_SBOX).[ (cast v <: usize) ] <: u8
let subi (v: u32) (n: Prims.nat {n < 4}) = sub0_not (index_u8 v (sz n) <: u8) // v_SBOX.[ cast (index_u8 v (sz 0) <: u8) <: usize ] <: u8

let subword (v: u32) : u32 =
  rebuild_u32 (subi v 0) (subi v 1) (subi v 2) (subi v 3)
  // rebuild_u32 (v_SBOX.[ cast (index_u8 v (sz 0) <: u8) <: usize ] <: u8)
  //   (v_SBOX.[ cast (index_u8 v (sz 1) <: u8) <: usize ] <: u8)
  //   (v_SBOX.[ cast (index_u8 v (sz 2) <: u8) <: usize ] <: u8)
  //   (v_SBOX.[ cast (index_u8 v (sz 3) <: u8) <: usize ] <: u8)

let aeskeygenassist (v1: u128) (v2: u8) : u128 =
  let x1:u32 = index_u32 v1 (sz 1) in
  let x3:u32 = index_u32 v1 (sz 3) in
  let y0:u32 = subword x1 in
  let y1:u32 = (rotword y0 <: u32) ^. (cast (v2 <: u8) <: u32) in
  let y2:u32 = subword x3 in
  let y3:u32 = (rotword y2 <: u32) ^. (cast (v2 <: u8) <: u32) in
  rebuild_u128 y0 y1 y2 y3

let subbytes (s: u128) : u128 =
  rebuild_u128 (subword (index_u32 s (sz 0) <: u32) <: u32)
    (subword (index_u32 s (sz 1) <: u32) <: u32)
    (subword (index_u32 s (sz 2) <: u32) <: u32)
    (subword (index_u32 s (sz 3) <: u32) <: u32)

let aesenclast (state rkey: u128) : u128 =
  let state:u128 = shiftrows state in
  let state:u128 = subbytes state in
  state ^. rkey

let vpshufd1 (s: u128) (o: u8) (i: usize) : u32 =
  index_u32 (s >>!
      (sz 32 *! (cast ((o >>! (sz 2 *! i <: usize) <: u8) %! (pub_u8 4) <: u8) <: usize) <: usize)
      <:
      u128)
    (sz 0)

let vpshufd (s: u128) (o: u8) : u128 =
  let (d1: u32):u32 = vpshufd1 s o (sz 0) in
  let (d2: u32):u32 = vpshufd1 s o (sz 1) in
  let (d3: u32):u32 = vpshufd1 s o (sz 2) in
  let (d4: u32):u32 = vpshufd1 s o (sz 3) in
  rebuild_u128 d1 d2 d3 d4

let vshufps (s1 s2: u128) (o: u8) : u128 =
  let (d1: u32):u32 = vpshufd1 s1 o (sz 0) in
  let (d2: u32):u32 = vpshufd1 s1 o (sz 1) in
  let (d3: u32):u32 = vpshufd1 s2 o (sz 2) in
  let (d4: u32):u32 = vpshufd1 s2 o (sz 3) in
  rebuild_u128 d1 d2 d3 d4

let key_combine (rkey temp1 temp2: u128) : (u128 & u128) =
  let temp1:u128 = vpshufd temp1 (pub_u8 255) in
  let temp2:u128 = vshufps temp2 rkey (pub_u8 16) in
  let rkey:u128 = rkey ^. temp2 in
  let temp2:u128 = vshufps temp2 rkey (pub_u8 140) in
  let rkey:u128 = rkey ^. temp2 in
  let rkey:u128 = rkey ^. temp1 in
  rkey, temp2 <: (u128 & u128)

let key_expand (rcon: u8) (rkey temp2: u128) : (u128 & u128) =
  let temp1:u128 = aeskeygenassist rkey rcon in
  key_combine rkey temp1 temp2

let xtime (x: u8) : u8 =
  let x1:u8 = x <<! (pub_u128 1) in
  let x7:u8 = x >>! (pub_u128 7) in
  let x71:u8 = x7 &. (pub_u8 1) in
  let x711b:u8 = x71 *! (pub_u8 27) in
  x1 ^. x711b

let mixcolumn (c: usize) (state: u128) : u32 =
  let s0:u8 = matrix_index state (sz 0) c in
  let s1:u8 = matrix_index state (sz 1) c in
  let s2:u8 = matrix_index state (sz 2) c in
  let s3:u8 = matrix_index state (sz 3) c in
  let tmp:u8 = ((s0 ^. s1 <: u8) ^. s2 <: u8) ^. s3 in
  let r0:u8 = (s0 ^. tmp <: u8) ^. (xtime (s0 ^. s1 <: u8) <: u8) in
  let r1:u8 = (s1 ^. tmp <: u8) ^. (xtime (s1 ^. s2 <: u8) <: u8) in
  let r2:u8 = (s2 ^. tmp <: u8) ^. (xtime (s2 ^. s3 <: u8) <: u8) in
  let r3:u8 = (s3 ^. tmp <: u8) ^. (xtime (s3 ^. s0 <: u8) <: u8) in
  rebuild_u32 r0 r1 r2 r3

let mixcolumns (state: u128) : u128 =
  let c0:u32 = mixcolumn (sz 0) state in
  let c1:u32 = mixcolumn (sz 1) state in
  let c2:u32 = mixcolumn (sz 2) state in
  let c3:u32 = mixcolumn (sz 3) state in
  rebuild_u128 c0 c1 c2 c3

let aesenc (state rkey: u128) : u128 =
  let state:u128 = shiftrows state in
  let state:u128 = subbytes state in
  let state:u128 = mixcolumns state in
  state ^. rkey

type sz_small = x:usize{match x with | C_usize v -> v.f_v < 12}

open Core.Cmp

let aes_helper (rkeys: t_Array u128 (sz 12)) (i : Prims.nat {i < 12}) : Lemma (requires (Core.Base.Seq.Base_impl.impl_2__len #u128 rkeys.f_v <: Core.Base.Int.t_HaxInt) = 12) (ensures ((Core.Convert.f_from #Core.Base.Int.t_HaxInt #usize #FStar.Tactics.Typeclasses.solve (sz i)) <. (Core.Base.Seq.Base_impl.impl_2__len #u128 rkeys.f_v <: Core.Base.Int.t_HaxInt))) = ()

#set-options "--fuel 100 --ifuel 1 --z3rlimit 15"
let aes_rounds (rkeys: t_Array u128 (sz 12) {(Core.Base.Seq.Base_impl.impl_2__len #u128 rkeys.f_v <: Core.Base.Int.t_HaxInt) = 12} ) (inp: u128) : u128 =
  let _ = aes_helper rkeys in
  let (state: u128):u128 = inp ^. (rkeys.[ sz 0 <: sz_small ] <: u128)
  in
  let state:u128 =
    (let state:u128 = state in
     let state:u128 = ( aes_helper rkeys 1 ; aesenc state (rkeys.[ sz 1 ] <: u128)) in
     let state:u128 = ( aes_helper rkeys 2 ; aesenc state (rkeys.[ sz 2 ] <: u128)) in
     let state:u128 = ( aes_helper rkeys 3 ; aesenc state (rkeys.[ sz 3 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 4 ; aesenc state (rkeys.[ sz 4 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 5 ; aesenc state (rkeys.[ sz 5 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 6 ; aesenc state (rkeys.[ sz 6 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 7 ; aesenc state (rkeys.[ sz 7 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 8 ; aesenc state (rkeys.[ sz 8 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 9 ; aesenc state (rkeys.[ sz 9 ] <: u128) ) in
     let state:u128 = ( aes_helper rkeys 10 ; aesenc state (rkeys.[ sz 10 ] <: u128) ) in
     state
       )

    // Rust_primitives.Hax.Folds.fold_range (sz 1)
    //   (sz 10)
    //   (fun state temp_1_ ->
    //       let state:u128 = state in
    //       let _:usize = temp_1_ in
    //       true)
    //   state
    //   (fun state round ->
    //       let state:u128 = state in
    //       let round:usize = round in
    //       aesenc state (rkeys.[ round ] <: u128) <: u128)
  in
  aesenclast state (rkeys.[ sz 10 ] <: u128)

type rkeys_typ = x:t_Array u128 (sz 12){Core.Base.Seq.Base_impl.impl_2__len #u128 x.f_v = 12}

#set-options "--fuel 1 --ifuel 1 --z3rlimit 15"
let rec new_is_sized_correct (n : Prims.nat{n < 20}) : Lemma (requires true) (ensures (Core.Base.Seq.Base_impl.impl_2__len #u128 (impl_2__new (sz n) (pub_u128 0)).f_v = n)) =
  match Core.Base.Seq.Base_spec.impl_1__match_list #u128 ((impl_2__new (sz n) (pub_u128 0)).f_v) with
  | Core.Base.Seq.LIST_NIL  -> ()
  | Core.Base.Seq.LIST_CONS _ tl ->
    (new_is_sized_correct (n-1))
    // Core.Base.Int.Base_spec.impl_9__succ (Core.Base.Seq.Base_impl.impl_2__len #u128 tl <: Core.Base.Int.t_HaxInt)

#set-options "--fuel 20 --ifuel 1 --z3rlimit 30"
let rec set_index_is_sized_correct (ms : Prims.nat{ms < 13}) (n : Prims.nat{n < ms}) (rkeys : t_Array u128 (sz ms)) key : Lemma (requires Core.Base.Seq.Base_impl.impl_2__len #u128 rkeys.f_v = ms) (ensures (Core.Base.Seq.Base_impl.impl_2__len #u128 (impl_2__set_index (sz ms) rkeys (sz n) key).f_v = ms)) =
  match Core.Base.Seq.Base_spec.impl_1__match_list #u128 (impl_2__set_index (sz ms) rkeys (sz n) key).f_v with
  | Core.Base.Seq.LIST_NIL  -> ()
  | Core.Base.Seq.LIST_CONS _ tl ->
    if n = 0
    then ()
    else
      (set_index_is_sized_correct (ms-1) (n-1) { f_v = tl } key)
    // Core.Base.Int.Base_spec.impl_9__succ (impl_2__len #v_T tl <: Core.Base.Int.t_HaxInt)

type usize_small = x:usize{match x with | C_usize v -> v.f_v < 12}

#set-options "--fuel 300 --ifuel 1 --z3rlimit 30 --split_queries always"
let sub_round_i (key, rkeys, temp2:(u128 & rkeys_typ & u128)) (i : Prims.nat{i<12}) : (u128 & rkeys_typ & u128) =
      let rkeys:rkeys_typ =
        (set_index_is_sized_correct 12 i rkeys key ; impl_2__set_index (sz 12) rkeys (sz i) key)
      in
      key, rkeys, temp2

let round_i (key, rkeys, temp2:(u128 & rkeys_typ & u128)) (i : Prims.nat{i<12}) : (u128 & rkeys_typ & u128) =
      let round:usize_small = sz i in
      let rcon:u8 = v_RCON.[ round ] in
      let key, temp2:(u128 & u128) = key_expand rcon key temp2 in
      sub_round_i (key, rkeys, temp2) i

let keys_expand (key: u128) : rkeys_typ =
  let (rkeys: rkeys_typ) =
    (new_is_sized_correct 12; impl_2__new (sz 12) (pub_u128 0))
  in
  let key:u128 = key in
  let rkeys:rkeys_typ =
    impl_2__set_index (sz 12) rkeys (sz 0) key
  in
  let (temp2: u128):u128 = pub_u128 0 in
  let key, rkeys, temp2:(u128 & rkeys_typ & u128) =
    (
      let temp0 = (key, rkeys, temp2 <: (u128 & rkeys_typ & u128)) in
      let temp0 = round_i temp0 1 in
      let temp0 = round_i temp0 2 in
      let temp0 = round_i temp0 3 in
      let temp0 = round_i temp0 4 in
      let temp0 = round_i temp0 5 in
      let temp0 = round_i temp0 6 in
      let temp0 = round_i temp0 7 in
      let temp0 = round_i temp0 8 in
      let temp0 = round_i temp0 9 in
      let temp0 = round_i temp0 10 in
      let temp0 = round_i temp0 11 in
      temp0
    )
    // Rust_primitives.Hax.Folds.fold_range (sz 1)
    //   (sz 11)
    //   (fun temp_0_ temp_1_ ->
    //       let key, rkeys, temp2:(u128 & t_Array u128 (sz 12) & u128) = temp_0_ in
    //       let _:usize = temp_1_ in
    //       true)
    //   (key, rkeys, temp2 <: (u128 & t_Array u128 (sz 12) & u128))
    //   (fun temp_0_ round ->
    //       let key, rkeys, temp2:(u128 & t_Array u128 (sz 12) & u128) = temp_0_ in
    //       let round:usize = round in
    //       let rcon:u8 = v_RCON.[ round ] in
    //       let key_temp, temp2_temp:(u128 & u128) = key_expand rcon key temp2 in
    //       let key:u128 = key_temp in
    //       let temp2:u128 = temp2_temp in
    //       let rkeys:t_Array u128 (sz 12) =
    //         Rust_primitives.Hax.Monomorphized_update_at.update_at_usize rkeys round key
    //       in
    //       key, rkeys, temp2 <: (u128 & t_Array u128 (sz 12) & u128))
  in
  rkeys

let aes (key inp: u128) : u128 =
  let rkeys:rkeys_typ = keys_expand key in
  aes_rounds rkeys inp

//A main program, which sorts a list and prints it before and after
let main () =
    let msg = "" in
    // let msg =
    //   let key = pub_u128 0x3c4fcf098815f7aba6d2ae2816157e2b in
    //   Printf.sprintf "%s vs %s"
    //     (string_of_int (match (aeskeygenassist key (v_RCON.[sz 1])) with | C_u128 v -> v.f_v))
    //     (string_of_int (match (pub_u128 0x01eb848beb848a013424b5e524b5e434) with | C_u128 v -> v.f_v))
    // in

    // let msg =
    //   let key = pub_u128 0x3c4fcf098815f7aba6d2ae2816157e2b in
    //   let (lhs, _) = key_combine key (aeskeygenassist key v_RCON.[sz 1]) (pub_u128 0) in

    //   let rhs = pub_u128 0x05766c2a3939a323b12c548817fefaa0 in

    //   Printf.sprintf "%s\n%s vs %s" msg
    //       (string_of_int (match lhs with | C_u128 v -> v.f_v))
    //       (string_of_int (match rhs with | C_u128 v -> v.f_v))
    // in

//     let msg =
//       let inp = pub_u128 0x627a6f6644b109c82b18330a81c3b3e5 in
//       let lhs = mixcolumns(inp) in
//       let rhs = pub_u128 0x7b5b54657374566563746f725d53475d in

//       Printf.sprintf "%s\nleft: %s\nright: %s\n" msg
// (string_of_int (match lhs with | C_u128 v -> v.f_v))
// (string_of_int (match rhs with | C_u128 v -> v.f_v))
//     in

    let msg =
      let rkey = pub_u128 0x48692853686179295b477565726f6e5d in
      let state = pub_u128 0x7b5b54657374566563746f725d53475d in
      let lhs = aesenc state rkey in
      let rhs = pub_u128  0xa8311c2f9fdba3c58b104b58ded7e595 in
      Printf.sprintf "%s\nleft: %s\nright: %s\n" msg
        (string_of_int (match lhs with | C_u128 v -> v.f_v))
        (string_of_int (match rhs with | C_u128 v -> v.f_v))
    in

    // let msg =
    //   let key = pub_u128 0x3c4fcf098815f7aba6d2ae2816157e2b in
    //   let inp = pub_u128 0x340737e0a29831318d305a88a8f64332 in
    //   let ctx = pub_u128 0x320b6a19978511dcfb09dc021d842539 in

    //   let enc_val = (aes key inp) in
    //   Printf.sprintf "%s\nAES(Key = %s, Msg = %s) = %s\n vs %s\n"
    //     msg
    //     (string_of_int (match key with | C_u128 v -> v.f_v))
    //     (string_of_int (match inp with | C_u128 v -> v.f_v))
    //     (string_of_int (match enc_val with | C_u128 v -> v.f_v <: nat))
    //     (string_of_int (match ctx with | C_u128 v -> v.f_v))
    // in

    FStar.IO.print_string msg

//Run ``main ()`` when the module loads
#push-options "--warn_error -272"
let _ = main ()
#pop-options

// TO extract: fstar.exe --extract "*" --odir out --codegen OCaml Prelude.fst
// and to run: AESenc: cd out && OCAMLPATH=$FSTAR_HOME/lib ocamlbuild -use-ocamlfind -pkg batteries -pkg fstar.lib Prelude.native && ./Prelude.native
