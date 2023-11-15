module Std.Collections.Hash.Set

open Std.Collections.Hash.Map
open Core.Option
open Rust_primitives

// https://doc.rust-lang.org/std/collections/struct.HashSet.html.
//
// Modelled as a FStar.Set.set
// TODO: this ignores state for now
type t_HashSet t t_RandomState = FStar.FiniteSet.Base.set t

// Convenience type alias
type set t = t_HashSet t t_RandomState

val impl_1__capacity #t (s: set t): usize

val impl_1__clear #t (s: set t): set t

val impl_2__contains #t (s: set t) (x: t): bool

// https://doc.rust-lang.org/std/collections/hash_set/struct.Difference.html
//
// A lazy iterator producing elements in the difference of HashSets
//
// Modelled as a FStar.Set.set
type t_Difference t t_RandomState = FStar.FiniteSet.Base.set t

val impl_2__difference #t (s1: set t) (s2: set t):
   t_Difference t t_RandomState

val impl_2__get #t (s: set t) (x: t): t_Option t

val impl_2__insert #t (s: set t) (x: t): set t & bool

// https://doc.rust-lang.org/std/collections/hash_set/struct.Intersection.html
//
// A lazy iterator producing elements in the intersection of HashSets
//
// Modelled as a FStar.Set.set
type t_Intersection t t_RandomState = FStar.FiniteSet.Base.set t

val impl_2__intersection #t (s1: set t) (s2: set t):
    t_Intersection t t_RandomState

val impl_2__is_disjoint #t (s1: set t) (s2: set t): bool

val impl_1__is_empty #t (s: set t): bool

val impl_2__is_subset #t (s1: set t) (s2: set t): bool

val impl_2__is_superset #t (s1: set t) (s2: set t): bool

val impl_1__len #t (s: set t): usize

val impl__new #t: set t

val impl_2__remove #t (s: set t) (x: t): set t & bool
