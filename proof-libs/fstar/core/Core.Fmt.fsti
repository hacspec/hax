module Core.Fmt
open Rust_primitives
open Core
open FStar.Mul

noeq type concrete_iter t = {
  length: option nat;
  seq: i:nat { match length with
           | Some length -> i < length
           | None        -> True
           }
      -> t
}

let nth #t (iter: concrete_iter t) (n: nat): option t = 
  match iter.length with
  | Some length -> if n < length
                  then Some (iter.seq n)
                  else None
  | _ -> Some (iter.seq n)

let next #t (iter: concrete_iter t): option t & concrete_iter t
  = match iter.length with
  | Some 0 -> None, iter
  | Some n -> Some (iter.seq 0)
           , { length = Some (n - 1)
             ; seq    = fun i -> iter.seq (i + 1) 
             }
  | None   -> None, iter

class t_TraitWithRequiresAndEnsures (v_Self: Type0) = {
  f_method_pre:self___: v_Self -> x: u8 -> pred: bool{x <. 100uy ==> pred};
  f_method_post:self___: v_Self -> x: u8 -> r: u8 -> pred: bool{pred ==> r >. 88uy};
  f_method:x0: v_Self -> x1: u8
    -> Prims.Pure u8 (f_method_pre x0 x1) (fun result -> f_method_post x0 x1 result)
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_TraitWithRequiresAndEnsures usize =
  {
    f_method_pre = (fun (self: usize) (x: u8) -> x <. 100uy);
    f_method_post = (fun (self: usize) (x: u8) (out: u8) -> out >. 120uy);
    f_method = fun (self: usize) (x: u8) -> 123uy
  }

let test
      (#v_T: Type0)
      (#[FStar.Tactics.Typeclasses.tcresolve ()] i1: t_TraitWithRequiresAndEnsures v_T)
      (x: v_T)
    : u8 = (f_method #v_T #FStar.Tactics.Typeclasses.solve x 99uy <: u8) -! 88uy



