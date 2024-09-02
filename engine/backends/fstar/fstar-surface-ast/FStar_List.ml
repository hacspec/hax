(* We give an implementation here using OCaml's BatList,
   which provides tail-recursive versions of most functions *)
let isEmpty l = l = []
let hd = BatList.hd
let tail = BatList.tl
let tl = BatList.tl

let rec last = function
  | x :: [] -> x
  | _ :: tl -> last tl
let length l = Z.of_int (BatList.length l)
let rev = BatList.rev
let append = BatList.append
let op_At = append
let flatten = BatList.flatten
let map = BatList.map
let mapi f l = BatList.mapi (fun i x -> f (Z.of_int i) x) l
let fold_left = BatList.fold_left
let fold_right = BatList.fold_right
let fold_left2 = BatList.fold_left2
let existsb f l = BatList.exists f l
let find f l = try Some (BatList.find f l) with | Not_found -> None
let filter = BatList.filter
let for_all = BatList.for_all
let collect f l = BatList.flatten (BatList.map f l)
let tryFind = find
let choose = BatList.filter_map
let partition = BatList.partition
let sortWith f l = BatList.sort (fun x y -> Z.to_int (f x y)) l

let isEmpty l = l = []
let singleton x = [x]
let mem = BatList.mem
let memT = mem
let hd = BatList.hd
let tl = BatList.tl
let tail = BatList.tl
let iter = BatList.iter
let forall2 = BatList.for_all2
