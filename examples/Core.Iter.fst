module Core.Iter

open Core.Types

class iterator self = {
  item: Type;
  next: self -> self * option item;
  size_hint: self -> option usize;
  in_range: self -> item -> Type0;
  fold: #b:Type -> s:self -> b -> (b -> i:item{in_range s i} -> b) -> b;
  enumerate: self -> Core.Iter.Adapters.Enumerate.t_Enumerate item;
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
  (min: SizeT.t) (max: SizeT.t {SizeT.v min <= SizeT.v max})
  (init: 'a) (f: ('a -> i:usize{SizeT.v i < SizeT.v max /\ SizeT.v i >= SizeT.v min} -> 'a))
  : Tot 'a (decreases (SizeT.v max - SizeT.v min))
  = let open FStar.SizeT in
    if min = max
    then init
    else fold_range' (min +^ 1sz) max (f init min) f
  
instance iterator_range: iterator range = 
  let open FStar.SizeT in
  {
  item = usize;
  next = (fun {f_start; f_end} -> 
    if f_start <^ f_end
    then ({f_start = f_start `SizeT.add` 1sz; f_end}, Some f_start)
    else ({f_start; f_end}, None)
  );
  size_hint = (fun {f_start; f_end} -> 
    Some (if f_start <^ f_end
          then f_end -^ f_start 
          else 0sz)
  );
  in_range = (fun x i -> SizeT.v i < SizeT.v x.f_end /\ SizeT.v i >= SizeT.v x.f_start);
  fold = (fun #b r init f -> 
    if r.f_start <^ r.f_end
    then fold_range' r.f_start r.f_end init (fun x i -> f x i)
    else init
  );
  enumerate = magic ();
}

instance range_index t len : index (array t len) range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) {f_start; f_end} -> 
    SizeT.v f_start <= SizeT.v len &&
    SizeT.v f_end   <= SizeT.v len
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start `SizeT.lt` f_end
      then Seq.slice arr (SizeT.v f_start) (SizeT.v f_end)
      else Seq.empty
    );
}

instance range_index_slice t : index (slice t) Core.Ops.Range.Range.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: slice t) {f_start; f_end} -> 
    SizeT.v f_start <= Seq.length arr &&
    SizeT.v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr {f_start; f_end} -> 
      if f_start `SizeT.lt` f_end
      then Seq.slice arr (SizeT.v f_start) (SizeT.v f_end)
      else Seq.empty
    );
}

module RangeTo = Core.Ops.Range.RangeTo

instance rangeTo_index t len : index (array t len) RangeTo.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) { RangeTo.f_end } -> 
    SizeT.v f_end   <= Seq.length arr
  );
  (.[]) = (fun arr { f_end } -> 
      Seq.slice arr 0 (SizeT.v f_end)
    );
}

module RangeFrom = Core.Ops.Range.RangeFrom

instance rangeFrom_index t len : index (array t len) RangeFrom.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: array t len) { RangeFrom.f_start } -> 
    SizeT.v f_start < SizeT.v len
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (SizeT.v f_start) (Seq.length arr)
    );
}

instance rangeFrom_index_slice_usize t : index (slice t) usize = magic ()

instance rangeFrom_index_slice t : index (slice t) RangeFrom.range = {
  output = Core.Types.slice t;
  in_range = (fun (arr: slice t) { RangeFrom.f_start } -> 
    SizeT.v f_start < Seq.length arr
  );
  (.[]) = (fun arr { f_start } -> 
      Seq.slice arr (SizeT.v f_start) (Seq.length arr)
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


