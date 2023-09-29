module Core.Types

unfold type i8 = FStar.Int8.t
unfold type i16 = FStar.Int16.t
unfold type i32 = FStar.Int32.t
unfold type i64 = FStar.Int64.t
unfold type i128 = FStar.Int128.t

unfold type u8 = FStar.UInt8.t
unfold type u16 = FStar.UInt16.t
unfold type u32 = FStar.UInt32.t
unfold type u64 = FStar.UInt64.t
unfold type u128 = FStar.UInt128.t
unfold type usize = FStar.SizeT.t
unfold type slice t = s: FStar.Seq.seq t {SizeT.fits (FStar.Seq.length s)}
type t_Array t (l: usize) = 
  s: FStar.Seq.seq t {
       FStar.Seq.length s == FStar.SizeT.v l
    }
unfold type array = t_Array

class index self idx = {
  output: Type;
  in_range: self -> idx -> bool;
  (.[]): s:self -> i:idx {in_range s i} -> output;
}

class update_at self idx = {
  super_index: index self idx;
  (.[]<-): s: self -> i: idx {super_index.in_range s i} -> super_index.output -> self;
}


open Core.Types
open FStar.UInt128
let pub_u128 = uint_to_t
