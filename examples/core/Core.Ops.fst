module Core.Ops

open Core.Types

class add_tc self rhs = {
  output: Type;
  in_bounds: self -> rhs -> Type0;
  (+.): x:self -> y:rhs {in_bounds x y} -> output;
}

open FStar.Int8

instance _: add_tc i8 i8 = {
  output = i8;
  in_bounds = (fun a b -> FStar.Int.size (v a + v b) 8);
  (+.) = (fun x y -> x +^ y)
}

open FStar.Int16

instance _: add_tc i16 i16 = {
  output = i16;
  in_bounds = (fun a b -> FStar.Int.size (v a + v b) 16);
  (+.) = (fun x y -> x +^ y)
}

open FStar.Int32

instance _: add_tc i32 i32 = {
  output = i32;
  in_bounds = (fun a b -> FStar.Int.size (v a + v b) 32);
  (+.) = (fun x y -> x +^ y)
}

open FStar.Int64

instance _: add_tc i64 i64 = {
  output = i64;
  in_bounds = (fun a b -> FStar.Int.size (v a + v b) 64);
  (+.) = (fun x y -> x +^ y)
}

open FStar.UInt8

instance _: add_tc u8 u8 = {
  output = u8;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 8);
  (+.) = (fun x y -> x +^ y)
}

open FStar.UInt16

instance _: add_tc u16 u16 = {
  output = u16;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 16);
  (+.) = (fun x y -> x +^ y)
}

open FStar.UInt32

instance _: add_tc u32 u32 = {
  output = u32;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 32);
  (+.) = (fun x y -> x +^ y)
}

open FStar.UInt64

instance _: add_tc u64 u64 = {
  output = u64;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 64);
  (+.) = (fun x y -> x +^ y)
}


instance _: add_tc SizeT.t SizeT.t = {
  output = SizeT.t;
  in_bounds = (fun a b -> SizeT.fits (SizeT.v a + SizeT.v b));
  (+.) = (fun x y -> SizeT.add x y)
}


let ( =. ) = (=)
let ( <>. ) = ( <> )

open FStar.Integers

let ( -. ) #w = op_Subtraction #w
let ( ^. ) #w = ( ^^ ) #w

let ( /. )  #w = ( / )  #w
let ( %. )  #w = ( % ) #w
let ( *. )  #w = ( * ) #w
let ( |. )  #w = ( |^ ) #w
let ( <<. )  #w = ( <<^ ) #w
let ( >>. )  #w = ( >>^ ) #w

let ( >=. ) #w = ( >= ) #w
let ( <=. ) #w = ( <= ) #w
let ( >. ) #w = ( > ) #w
let ( <. ) #w = ( < ) #w
let ( &. ) #w = ( &^ ) #w

let cast #from #to = cast #from #to


