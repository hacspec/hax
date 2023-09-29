module Core.Array

open Core.Types
open FStar.Integers

instance index_array t (l: SizeT.t): index (array t l) usize = {
  output = t;
  in_range = (fun (s: array _ _) (i: usize) -> FStar.Seq.length s > FStar.SizeT.v i);
  (.[]) = (fun s i -> FStar.Seq.index s (FStar.SizeT.v i))
}

instance update_at_array t (l: SizeT.t): update_at (array t l) usize =
  let super_index = index_array t l in
  let self = array t l in
  let (.[]<-): s: self -> i: usize {super_index.in_range s i} -> super_index.output -> self = 
    fun s i v -> FStar.Seq.upd s (FStar.SizeT.v i) v
  in
  { super_index; (.[]<-) }

let array_of_list = Seq.seq_of_list

let array_create (x: 'a) (len: usize): array 'a len = 
  FStar.Seq.create (SizeT.v len) x

instance update_at_vec t: update_at (Alloc.Vec.t_Vec t ()) usize =
  magic ()


