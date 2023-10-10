module Core.Iter

open Rust_primitives

class iterator self = {
  item: Type;
  next: self -> self * option item;
  size_hint: self -> option usize;
  in_range: self -> item -> Type0;
  fold: #b:Type -> s:self -> b -> (b -> i:item{in_range s i} -> b) -> b;
  enumerate: self -> Core.Iter.Adapters.Enumerate.t_Enumerate self;
}

instance iterator_enumerate it {| i: iterator it |}: iterator (Core.Iter.Adapters.Enumerate.t_Enumerate it) = 
  let open Core.Iter.Adapters.Enumerate in
  {
    item = (usize * i.item);
    next = (fun {iter; count} -> 
      let open Core.Ops in
      let iter, opt = next iter in
      match opt with
      | Some value -> {iter; count (* + 1 *)}, Some (count, value)
      | None -> {iter; count}, None
    );
    size_hint = (fun s -> i.size_hint s.iter);
    // in_range = (fun s -> i.in_range s.iter);
    in_range = magic ();
    fold = magic ();
    enumerate = magic ();
  }

open Core.Ops.Range.Range

instance iterator_slice (t: eqtype): iterator (slice t) = {
  item = t;
  next = (fun s -> admit ());
  size_hint = (fun s -> Some (admit ()));
  in_range = (fun (s: slice t) i -> Seq.mem i s);
  fold = (fun #b s init f -> admit ());
  enumerate = magic ();
}

instance iterator_array (t: eqtype) len: iterator (array t len) = {
  item = t;
  next = (fun s -> admit ());
  size_hint = (fun s -> Some (admit()));
  in_range = (fun (arr: array t len) i -> Seq.mem i arr);
  fold = (fun #b s init f -> admit ());
  enumerate = magic ();
}

let rec fold_range'
  (min: usize) (max: usize {v min <= v max})
  (init: 'a) (f: ('a -> i:usize{v i < v max /\ v i >= v min} -> 'a))
  : Tot 'a (decreases (v max - v min))
  = if min = max
    then init
    else fold_range' (add min (sz 1)) max (f init min) f

instance iterator_range: iterator range = 
  {
  item = usize;
  next = (fun {f_start; f_end} -> 
    if f_start <. f_end
    then ({f_start = f_start +. sz 1; f_end}, Some f_start)
    else ({f_start; f_end}, None)
  );
  size_hint = (fun {f_start; f_end} -> 
    magic ()
    // Some (if f_start <. f_end
    //       then f_end -. f_start 
    //       else 0sz)
  );
  in_range = (fun x i -> v i < v x.f_end /\ v i >= v x.f_start);
  fold = (fun #b r init f -> 
    if r.f_start <. r.f_end
    then fold_range' r.f_start r.f_end init (fun x i -> f x i)
    else init
  );
  enumerate = magic ();
}

(* 
instance range_index t len : index (array t len) range = {
  output = slice t;
  in_range = (fun (arr: array t len) {f_start; f_end} -> 
    v f_start <= v len &&
    v f_end   <= v len
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start <. f_end
      then Seq.slice arr (v f_start) (v f_end)
      else Seq.empty
    );
}

instance range_index_slice t : index (slice t) Core.Ops.Range.Range.range = {
  output = slice t;
  in_range = (fun (arr: slice t) {f_start; f_end} -> 
    v f_start <= Seq.length arr &&
    v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start <. f_end
      then Seq.slice arr (v f_start) (v f_end)
      else Seq.empty
    );
}

module RangeTo = Core.Ops.Range.RangeTo

instance rangeTo_index t len : index (array t len) RangeTo.range = {
  output = slice t;
  in_range = (fun (arr: array t len) { RangeTo.f_end } -> 
    v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr { f_end } -> 
      Seq.slice arr 0 (v f_end)
    );
}

module RangeFrom = Core.Ops.Range.RangeFrom

instance rangeFrom_index t len : index (array t len) RangeFrom.range = {
  output = slice t;
  in_range = (fun (arr: array t len) { RangeFrom.f_start } -> 
    v f_start < v len
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (v f_start) (Seq.length arr)
    );
}

instance rangeFrom_index_slice_usize t : index (slice t) usize = magic ()

instance rangeFrom_index_slice t : index (slice t) RangeFrom.range = {
  output = slice t;
  in_range = (fun (arr: slice t) { RangeFrom.f_start } -> 
    v f_start < Seq.length arr
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (v f_start) (Seq.length arr)
    );
}

let cloned x = x

class collect_tc (it: Type) (target: Type) = {
  collect: it -> target;
}

instance collect_tc_slice (it: Type) {| it_i: iterator it |}: collect_tc it (slice it_i.item) 
  = magic ()

instance collect_tc_slice_slice (t: eqtype): collect_tc (slice t) (slice t)
  = magic ()

// let enumerate (l: slice 'a): slice (nat * 'a)<
//   = magic ()

// instance map_tc (it: Type) = {
//   map: it -> 
// }


*)
