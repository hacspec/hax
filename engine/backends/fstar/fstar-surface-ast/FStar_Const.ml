open Prims
type signedness =
  | Unsigned 
  | Signed [@@deriving yojson,show]
type width =
  | Int8 
  | Int16 
  | Int32 
  | Int64 
  | Sizet [@@deriving yojson,show]
type sconst =
  | Const_effect 
  | Const_unit 
  | Const_bool of Prims.bool 
  | Const_int of (Prims.string * (signedness * width)
  FStar_Pervasives_Native.option) 
  | Const_char of FStar_BaseTypes.char 
  | Const_real of Prims.string 
  | Const_string of (Prims.string * FStar_Compiler_Range.range) 
  | Const_range_of 
  | Const_set_range_of 
  | Const_range of FStar_Compiler_Range.range 
  | Const_reify of FStar_Ident.lid FStar_Pervasives_Native.option 
  | Const_reflect of FStar_Ident.lid [@@deriving yojson,show]
let (eq_const : sconst -> sconst -> Prims.bool) =
  fun c1 ->
    fun c2 ->
      match (c1, c2) with
      | (Const_int (s1, o1), Const_int (s2, o2)) ->
          (let uu___ = FStar_Compiler_Util.ensure_decimal s1 in
           let uu___1 = FStar_Compiler_Util.ensure_decimal s2 in
           uu___ = uu___1) && (o1 = o2)
      | (Const_string (a, uu___), Const_string (b, uu___1)) -> a = b
      | (Const_reflect l1, Const_reflect l2) -> FStar_Ident.lid_equals l1 l2
      | (Const_reify uu___, Const_reify uu___1) -> true
      | uu___ -> c1 = c2
