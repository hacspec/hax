module Core.Ops

open Core.Types

class add_tc self rhs = {
  output: Type;
  in_bounds: self -> rhs -> Type0;
  (+.): x:self -> y:rhs {in_bounds x y} -> output;
}

open FStar.UInt32

instance _: add_tc u32 u32 = {
  output = u32;
  in_bounds = (fun a b -> FStar.UInt.size (v a + v b) 32);
  (+.) = (fun x y -> x +^ y)
}

instance _: add_tc SizeT.t SizeT.t = {
  output = SizeT.t;
  in_bounds = (fun a b -> SizeT.fits (SizeT.v a + SizeT.v b));
  (+.) = (fun x y -> SizeT.add x y)
}


let ( ^. ) x y = x
let ( /. ) = SizeT.div
let ( %. ) = SizeT.rem  
let ( *. ) (x y: 'a) = x
let ( |. ) (x y: 'a) = x
let ( ~. ) (x: 'a): 'a = x
let ( <<. ) #a: a -> u8 -> a = magic ()
let ( >>. ) #a: a -> u8 -> a = magic ()

let ( =. ) = (=)
let ( >=. ) (x y: 'a) = true
let ( <=. ) (x y: 'a) = true
let ( >. ) (x y: 'a) = true
let ( <. ) (x y: 'a) = true

let ( <>. ) (x y: 'a) = true
let ( &. ) (x y: 'a) = x 
let ( -. ) (x y: 'a) = x 

let cast #a #b (x: a): b = magic ()

