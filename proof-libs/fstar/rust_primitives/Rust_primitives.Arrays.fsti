module Rust_primitives.Arrays

open Rust_primitives.Integers
open FStar.Mul

/// Rust slices and arrays are represented as sequences
type t_Slice t = s:Seq.seq t{Seq.length s <= max_usize}
type t_Array t (l:usize) = s: Seq.seq t { Seq.length s == v l }

/// Length of a slice
let length (#a: Type) (s: t_Slice a): usize = sz (Seq.length s)

/// Check whether a slice contains an item
let contains (#t: eqtype) (s: t_Slice t) (x: t): bool = Seq.mem x s

/// Converts an F* list into an array
val of_list (#t:Type) (l: list t {FStar.List.Tot.length l < maxint U16}):
    t_Array t (sz (FStar.List.Tot.length l))
/// Converts an slice into a F* list
val to_list (#t:Type) (s: t_Slice t): list t

val map_array (#a #b: Type) #n (arr: t_Array a n) (f: a -> b): t_Array b n

/// Creates an array of size `l` using a function `f`
val createi #t (l:usize) (f:(u:usize{u <. l} -> t))
    : Pure (t_Array t l)
      (requires True)
      (ensures (fun res -> (forall i. Seq.index res (v i) == f i)))

unfold let map #a #b #p
  (f:(x:a{p x} -> b))
  (s: t_Slice a {forall (i:nat). i < Seq.length s ==> p (Seq.index s i)}): t_Slice b
  = createi (length s) (fun i -> f (Seq.index s (v i)))

/// Concatenates two slices
let concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) :
           r:t_Array t (length x +! length y) = Seq.append x y

/// Translate indexes of `concat x y` into indexes of `x` or of `y`
val lemma_index_concat #t (x:t_Slice t) (y:t_Slice t{range (v (length x) + v (length y)) usize_inttype}) (i:usize{i <. length x +! length y}):
           Lemma (if i <. length x then
                    Seq.index (concat x y) (v i) == Seq.index x (v i)
                  else 
                    Seq.index (concat x y) (v i) == Seq.index y (v (i -! length x)))
           [SMTPat (Seq.index (concat #t x y) i)]

/// Take a subslice given `x` a slice and `i` and `j` two indexes
let slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x}):
           r:t_Array t (j -! i) = Seq.slice x (v i) (v j)

/// Translate indexes for subslices
val lemma_index_slice #t (x:t_Slice t) (i:usize{i <=. length x}) (j:usize{i <=. j /\ j <=. length x})
                                (k:usize{k <. j -! i}):
           Lemma (Seq.index (slice x i j) (v k) == Seq.index x (v (i +! k)))
           [SMTPat (Seq.index (slice x i j) (v k))]

/// Introduce bitwise equality principle for sequences
val eq_intro #t (a : Seq.seq t) (b:Seq.seq t{Seq.length a == Seq.length b}):
       Lemma
       (requires forall i. {:pattern Seq.index a i; Seq.index b i}
                      i < Seq.length a ==>
                      Seq.index a i == Seq.index b i)
       (ensures Seq.equal a b)
       [SMTPat (Seq.equal a b)]

/// Split a slice in two at index `m`
let split #t (a:t_Slice t) (m:usize{m <=. length a}):
       Pure (t_Array t m & t_Array t (length a -! m))
       True (ensures (fun (x,y) ->
         x == slice a (sz 0) m /\
         y == slice a m (length a) /\
         concat #t x y == a)) = 
         let x = Seq.slice a 0 (v m) in
         let y = Seq.slice a (v m) (Seq.length a) in
         assert (Seq.equal a (concat x y));
         (x,y)

let lemma_slice_append #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z)) usize_inttype /\
                   length y +! length z == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length x)))
        (ensures (x == concat y z)) = 
        assert (Seq.equal x (concat y z))

let lemma_slice_append_3 #t (x:t_Slice t) (y:t_Slice t) (z:t_Slice t) (w:t_Slice t):
  Lemma (requires (range (v (length y) + v (length z) + v (length w)) usize_inttype /\
                   length y +! length z +! length w == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length x)))
        (ensures (x == concat y (concat z w))) =
         assert (Seq.equal x (Seq.append y (Seq.append z w)))

let lemma_slice_append_4 #t (x y z w u:t_Slice t) :
  Lemma (requires (range (v (length y) + v (length z) + v (length w) + v (length u)) usize_inttype /\
                   length y +! length z +! length w +! length u == length x /\
                   y == slice x (sz 0) (length y) /\ 
                   z == slice x (length y) (length y +! length z) /\
                   w == slice x (length y +! length z) (length y +! length z +! length w) /\
                   u == slice x (length y +! length z +! length w) (length x)))
        (ensures (x == concat y (concat z (concat w u)))) =
         assert (Seq.equal x (Seq.append y (Seq.append z (Seq.append w u))))


