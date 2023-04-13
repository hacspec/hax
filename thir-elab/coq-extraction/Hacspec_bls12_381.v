From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

(** Should be moved to Hacspec_Lib.v **)
     Definition int_xI {WS : WORDSIZE} (a : int) : int := MachineIntegers.add (MachineIntegers.mul a (repr 2)) MachineIntegers.one.
Definition int_xO {WS : WORDSIZE} (a : int) : int := MachineIntegers.mul a (repr 2).
Number Notation int Pos.of_num_int Pos.to_num_int (via positive mapping [[int_xI] => xI, [int_xO] => xO , [MachineIntegers.one] => xH]) : hacspec_scope.
Notation "0" := (repr O).
Notation U8_t := int8.
Notation U8 := id.
Notation U16_t := int16.
Notation U16 := id.
Notation U32_t := int32.
Notation U32 := id.
Notation U64_t := int64.
Notation U64 := id.
Notation U128_t := int128.
Notation U128 := id.

Notation " x .[ a ]" := (array_index x a) (at level 40).
Notation " x .[ i ]<- a" := (array_upd x i a) (at level 40).

Class Addition A := add : A -> A -> A.
Notation "a .+ b" := (add a b).
Instance array_add_inst {ws : WORDSIZE} {len: nat} : Addition (nseq (@int ws) len) := { add a b := a array_add b }.
Instance int_add_inst {ws : WORDSIZE} : Addition (@int ws) := { add a b := MachineIntegers.add a b }.

Class Subtraction A := sub : A -> A -> A.
Notation "a .- b" := (sub a b).
Instance array_sub_inst {ws : WORDSIZE} {len: nat} : Subtraction (nseq (@int ws) len) := { sub := array_join_map MachineIntegers.sub }.
Instance int_sub_inst {ws : WORDSIZE} : Subtraction (@int ws) := { sub a b := MachineIntegers.sub a b }.

Class Multiplication A := mul : A -> A -> A.
Notation "a .* b" := (mul a b).
Instance array_mul_inst {ws : WORDSIZE} {len: nat} : Multiplication (nseq (@int ws) len) := { mul a b := a array_mul b }.
Instance int_mul_inst {ws : WORDSIZE} : Multiplication (@int ws) := { mul a b := MachineIntegers.mul a b }.

Class Xor A := xor : A -> A -> A.
Notation "a .^ b" := (xor a b).

Instance array_xor_inst {ws : WORDSIZE} {len: nat} : Xor (nseq (@int ws) len) := { xor a b := a array_xor b }.
Instance int_xor_inst {ws : WORDSIZE} : Xor (@int ws) := { xor a b := MachineIntegers.xor a b }.

Definition new {A : Type} `{Default A} {len} : nseq A len := array_new_ default _.
Class array_or_seq A len :=
{ as_seq : seq A ; as_nseq : nseq A len }.

Arguments as_seq {_} {_} array_or_seq.
Arguments as_nseq {_} {_} array_or_seq.
Coercion as_seq : array_or_seq >-> seq.
Coercion as_nseq : array_or_seq >-> nseq.

Instance nseq_array_or_seq {A len} (a : nseq A len) : array_or_seq A len :=
{ as_seq := array_to_seq a ; as_nseq := a ; }.
Coercion nseq_array_or_seq : nseq >-> array_or_seq.

Instance seq_array_or_seq {A} `{Default A} (a : seq A) : array_or_seq A (length a) :=
{ as_seq := a ; as_nseq := array_from_seq _ a ; }.
Coercion seq_array_or_seq : seq >-> array_or_seq.

Definition update {A : Type}  `{Default A} {len slen} (s : nseq A len) start (start_a : array_or_seq A slen) : nseq A len :=
array_update (a := A) (len := len) s start (as_seq start_a).

Definition to_le_U32s {A l} := array_to_le_uint32s (A := A) (l := l).
Axiom to_le_bytes : forall {ws : WORDSIZE} {len}, nseq (@int ws) len -> seq int8.
Definition from_seq {A : Type}  `{Default A} {len slen} (s : array_or_seq A slen) : nseq A len := array_from_seq _ (as_seq s).

Notation Seq_t := seq.
Notation len := (fun s => seq_len s : int32).

Notation slice := array_slice.
Notation new_seq := seq_new.
Notation num_exact_chunks := seq_num_exact_chunks.
Notation get_exact_chunk := seq_get_exact_chunk.
Definition set_chunk
{a: Type}
`{Default a}
{len}
(s: seq a)
(chunk_len: nat)
(chunk_num: nat)
(chunk: array_or_seq a len) : seq a :=
seq_set_chunk s chunk_len chunk_num (as_seq chunk).
Definition set_exact_chunk {a} `{H : Default a} {len} := @set_chunk a H len.
Notation get_remainder_chunk := seq_get_remainder_chunk.
Notation "a <> b" := (negb (eqb a b)).

Notation from_secret_literal := nat_mod_from_secret_literal.
Definition pow2 {m} (x : @int WORDSIZE32) := nat_mod_pow2 m (unsigned x).
Instance nat_mod_addition {n} : Addition (nat_mod n) := { add a b := a +% b }.
Instance nat_mod_subtraction {n} : Subtraction (nat_mod n) := { sub a b := a -% b }.
Instance nat_mod_multiplication {n} : Multiplication (nat_mod n) := { mul a b := a *% b }.
Definition from_slice {a: Type} `{Default a} {len slen} (x : array_or_seq a slen) := array_from_slice default len (as_seq x).
Notation zero := nat_mod_zero.
Notation to_byte_seq_le := nat_mod_to_byte_seq_le.
Notation U128_to_le_bytes := u128_to_le_bytes.
Notation from_byte_seq_le := nat_mod_from_byte_seq_le.
Definition from_literal {m} := nat_mod_from_literal m.
Notation inv := nat_mod_inv.
Notation update_start := array_update_start.
Notation pow := nat_mod_pow_self.
Notation bit := nat_mod_bit.

Definition int_to_int {ws1 ws2} (i : @int ws1) : @int ws2 := repr (unsigned i).
Coercion int_to_int : int >-> int.
Notation push := seq_push.
Notation Build_secret := secret.
Notation "a -× b" :=
(prod a b) (at level 80, right associativity) : hacspec_scope.
Notation Result_t := (fun '(x,y) => result).
Axiom TODO_name : Type.
Notation ONE := nat_mod_one.
Notation exp := nat_mod_exp.
Notation nat_mod := GZnZ.znz.
Instance nat_mod_znz_addition {n} : Addition (GZnZ.znz n) := { add a b := a +% b }.
Instance nat_mod_znz_subtraction {n} : Subtraction (GZnZ.znz n) := { sub a b := a -% b }.
Instance nat_mod_znz_multiplication {n} : Multiplication (GZnZ.znz n) := { mul a b := a *% b }.
Notation TWO := nat_mod_two.
Notation ne := (fun x y => negb (eqb x y)).
Notation eq := (eqb).
(** end of: Should be moved to Hacspec_Lib.v **)


(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation FpCanvas := (nseq int8 384).
Notation Fp_t := (nat_mod 0x1a0111ea397fe69a4b1ba7b6434bacd764774b84f38512bf6730d2a0f6b0f6241eabfffeb153ffffb9feffffffffaaab).
Definition Fp : Fp_t -> Fp_t :=
  id.

Notation SerializedFp_t := (nseq int8 48).
Definition SerializedFp : SerializedFp_t -> SerializedFp_t :=
  id.

Notation ArrayFp_t := (nseq int32 6).
Definition ArrayFp : ArrayFp_t -> ArrayFp_t :=
  id.

Notation ScalarCanvas := (nseq int8 256).
Notation Scalar_t := (nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000).
Definition Scalar : Scalar_t -> Scalar_t :=
  id.

Notation G1_t := ((Fp_t '× Fp_t '× bool)).

Notation Fp2_t := ((Fp_t '× Fp_t)).

Notation G2_t := (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)).

Notation Fp6_t := (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))).

Notation Fp12_t := ((((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))).

Definition fp2fromfp (n : Fp_t) : (Fp_t '× Fp_t) :=
  (n,zero).

Definition fp2zero : (Fp_t '× Fp_t) :=
  fp2fromfp zero.

Definition fp2neg (n : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  let '(n1,n2) := n : (Fp_t '× Fp_t) in
  (zero.-n1,zero.-n2).

Definition fp2add (n : (Fp_t '× Fp_t)) (m : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  let '(n1,n2) := n : (Fp_t '× Fp_t) in
  let '(m1,m2) := m : (Fp_t '× Fp_t) in
  (n1.+m1,n2.+m2).

Definition fp2sub (n : (Fp_t '× Fp_t)) (m : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  fp2add n (fp2neg m).

Definition fp2mul (n : (Fp_t '× Fp_t)) (m : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  let '(n1,n2) := n : (Fp_t '× Fp_t) in
  let '(m1,m2) := m : (Fp_t '× Fp_t) in
  let x1 := (n1.*m1).-(n2.*m2) : Fp_t in
  let x2 := (n1.*m2).+(n2.*m1) : Fp_t in
  (x1,x2).

Definition fp2inv (n : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  let '(n1,n2) := n : (Fp_t '× Fp_t) in
  let t0 := (n1.*n1).+(n2.*n2) : Fp_t in
  let t1 := inv t0 : Fp_t in
  let x1 := n1.*t1 : Fp_t in
  let x2 := zero.-(n2.*t1) : Fp_t in
  (x1,x2).

Definition fp2conjugate (n : (Fp_t '× Fp_t)) : (Fp_t '× Fp_t) :=
  let '(n1,n2) := n : (Fp_t '× Fp_t) in
  (n1,zero.-n2).

Definition fp6fromfp2 (n : (Fp_t '× Fp_t)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  (n,fp2zero,fp2zero).

Definition fp6zero : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  fp6fromfp2 fp2zero.

Definition fp6neg (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  let '(n1,n2,n3) := n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  (fp2sub fp2zero n1,fp2sub fp2zero n2,fp2sub fp2zero n3).

Definition fp6add (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) (m : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  let '(n1,n2,n3) := n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let '(m1,m2,m3) := m : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  (fp2add n1 m1,fp2add n2 m2,fp2add n3 m3).

Definition fp6sub (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) (m : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  fp6add n (fp6neg m).

Definition fp6mul (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) (m : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  let '(n1,n2,n3) := n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let '(m1,m2,m3) := m : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let eps := (ONE,ONE) : (Fp_t '× Fp_t) in
  let t1 := fp2mul n1 m1 : (Fp_t '× Fp_t) in
  let t2 := fp2mul n2 m2 : (Fp_t '× Fp_t) in
  let t3 := fp2mul n3 m3 : (Fp_t '× Fp_t) in
  let t4 := fp2mul (fp2add n2 n3) (fp2add m2 m3) : (Fp_t '× Fp_t) in
  let t5 := fp2sub (fp2sub t4 t2) t3 : (Fp_t '× Fp_t) in
  let x := fp2add (fp2mul t5 eps) t1 : (Fp_t '× Fp_t) in
  let t4 := fp2mul (fp2add n1 n2) (fp2add m1 m2) : (Fp_t '× Fp_t) in
  let t5 := fp2sub (fp2sub t4 t1) t2 : (Fp_t '× Fp_t) in
  let y := fp2add t5 (fp2mul eps t3) : (Fp_t '× Fp_t) in
  let t4 := fp2mul (fp2add n1 n3) (fp2add m1 m3) : (Fp_t '× Fp_t) in
  let t5 := fp2sub (fp2sub t4 t1) t3 : (Fp_t '× Fp_t) in
  let z := fp2add t5 t2 : (Fp_t '× Fp_t) in
  (x,y,z).

Definition fp6inv (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) :=
  let '(n1,n2,n3) := n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let eps := (ONE,ONE) : (Fp_t '× Fp_t) in
  let t1 := fp2mul n1 n1 : (Fp_t '× Fp_t) in
  let t2 := fp2mul n2 n2 : (Fp_t '× Fp_t) in
  let t3 := fp2mul n3 n3 : (Fp_t '× Fp_t) in
  let t4 := fp2mul n1 n2 : (Fp_t '× Fp_t) in
  let t5 := fp2mul n1 n3 : (Fp_t '× Fp_t) in
  let t6 := fp2mul n2 n3 : (Fp_t '× Fp_t) in
  let x0 := fp2sub t1 (fp2mul eps t6) : (Fp_t '× Fp_t) in
  let y0 := fp2sub (fp2mul eps t3) t4 : (Fp_t '× Fp_t) in
  let z0 := fp2sub t2 t5 : (Fp_t '× Fp_t) in
  let t0 := fp2mul n1 x0 : (Fp_t '× Fp_t) in
  let t0 := fp2add t0 (fp2mul eps (fp2mul n3 y0)) : (Fp_t '× Fp_t) in
  let t0 := fp2add t0 (fp2mul eps (fp2mul n2 z0)) : (Fp_t '× Fp_t) in
  let t0 := fp2inv t0 : (Fp_t '× Fp_t) in
  let x := fp2mul x0 t0 : (Fp_t '× Fp_t) in
  let y := fp2mul y0 t0 : (Fp_t '× Fp_t) in
  let z := fp2mul z0 t0 : (Fp_t '× Fp_t) in
  (x,y,z).

Definition fp12fromfp6 (n : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  (n,fp6zero).

Definition fp12neg (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(n1,n2) := n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  (fp6sub fp6zero n1,fp6sub fp6zero n2).

Definition fp12add (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) (m : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(n1,n2) := n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let '(m1,m2) := m : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  (fp6add n1 m1,fp6add n2 m2).

Definition fp12sub (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) (m : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  fp12add n (fp12neg m).

Definition fp12mul (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) (m : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(n1,n2) := n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let '(m1,m2) := m : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let gamma := (fp2zero,fp2fromfp ONE,fp2zero) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t1 := fp6mul n1 m1 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t2 := fp6mul n2 m2 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let x := fp6add t1 (fp6mul t2 gamma) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let y := fp6mul (fp6add n1 n2) (fp6add m1 m2) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let y := fp6sub (fp6sub y t1) t2 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  (x,y).

Definition fp12inv (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(n1,n2) := n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let gamma := (fp2zero,fp2fromfp ONE,fp2zero) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t1 := fp6mul n1 n1 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t2 := fp6mul n2 n2 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t1 := fp6sub t1 (fp6mul gamma t2) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let t2 := fp6inv t1 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let x := fp6mul n1 t2 : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  let y := fp6neg (fp6mul n2 t2) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) in
  (x,y).

Definition fp12exp (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) (k : Scalar_t) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let c := fp12fromfp6 (fp6fromfp2 (fp2fromfp ONE)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  foldi (@repr WORDSIZE32 0) (@repr WORDSIZE32 256) (fun i c =>
    let c := fp12mul c c : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
    if
      bit k ((@repr WORDSIZE32 255).-i)
    then
      fp12mul c n
    else
      c) c.

Definition fp12conjugate (n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(n1,n2) := n : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  (n1,fp6neg n2).

Definition fp12zero : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  fp12fromfp6 fp6zero.

Definition g1add_a (p : (Fp_t '× Fp_t '× bool)) (q : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let '(x1,y1,_) := p : (Fp_t '× Fp_t '× bool) in
  let '(x2,y2,_) := q : (Fp_t '× Fp_t '× bool) in
  let x_diff := x2.-x1 : Fp_t in
  let y_diff := y2.-y1 : Fp_t in
  let xovery := y_diff.*(inv x_diff) : Fp_t in
  let x3 := ((exp xovery (@repr WORDSIZE32 2)).-x1).-x2 : Fp_t in
  let y3 := (xovery.*(x1.-x3)).-y1 : Fp_t in
  (x3,y3,false).

Definition g1double_a (p : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let '(x1,y1,_) := p : (Fp_t '× Fp_t '× bool) in
  let x12 := exp x1 (@repr WORDSIZE32 2) : Fp_t in
  let xovery := ((from_literal (@repr WORDSIZE128 3)).*x12).*(inv (TWO.*y1)) : Fp_t in
  let x3 := (exp xovery (@repr WORDSIZE32 2)).-(TWO.*x1) : Fp_t in
  let y3 := (xovery.*(x1.-x3)).-y1 : Fp_t in
  (x3,y3,false).

Definition g1double (p : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let '(_x1,y1,inf1) := p : (Fp_t '× Fp_t '× bool) in
  if
    andb (ne y1 zero) inf1
  then
    g1double_a p
  else
    (zero,zero,true).

Definition g1add (p : (Fp_t '× Fp_t '× bool)) (q : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let '(x1,y1,inf1) := p : (Fp_t '× Fp_t '× bool) in
  let '(x2,y2,inf2) := q : (Fp_t '× Fp_t '× bool) in
  if
    inf1
  then
    q
  else
    if
      inf2
    then
      p
    else
      if
        eq p q
      then
        g1double p
      else
        if
          andb (eq x1 x2) (eq y1 (zero.-y2))
        then
          g1add_a p q
        else
          (zero,zero,true).

Definition g1mul (m : Scalar_t) (p : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let t := (zero,zero,true) : (Fp_t '× Fp_t '× bool) in
  foldi (@repr WORDSIZE32 0) (@repr WORDSIZE32 256) (fun i t =>
    let t := g1double t : (Fp_t '× Fp_t '× bool) in
    if
      bit m ((@repr WORDSIZE32 255).-i)
    then
      g1add t p
    else
      t) t.

Definition g1neg (p : (Fp_t '× Fp_t '× bool)) : (Fp_t '× Fp_t '× bool) :=
  let '(x,y,inf) := p : (Fp_t '× Fp_t '× bool) in
  (x,zero.-y,inf).

Definition g2add_a (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) (q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let '(x1,y1,_) := p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let '(x2,y2,_) := q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let x_diff := fp2sub x2 x1 : (Fp_t '× Fp_t) in
  let y_diff := fp2sub y2 y1 : (Fp_t '× Fp_t) in
  let xovery := fp2mul y_diff (fp2inv x_diff) : (Fp_t '× Fp_t) in
  let t1 := fp2mul xovery xovery : (Fp_t '× Fp_t) in
  let t2 := fp2sub t1 x1 : (Fp_t '× Fp_t) in
  let x3 := fp2sub t2 x2 : (Fp_t '× Fp_t) in
  let t1 := fp2sub x1 x3 : (Fp_t '× Fp_t) in
  let t2 := fp2mul xovery t1 : (Fp_t '× Fp_t) in
  let y3 := fp2sub t2 y1 : (Fp_t '× Fp_t) in
  (x3,y3,false).

Definition g2double_a (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let '(x1,y1,_) := p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let x12 := fp2mul x1 x1 : (Fp_t '× Fp_t) in
  let t1 := fp2mul (fp2fromfp (from_literal (@repr WORDSIZE128 3))) x12 : (Fp_t '× Fp_t) in
  let t2 := fp2inv (fp2mul (fp2fromfp TWO) y1) : (Fp_t '× Fp_t) in
  let xovery := fp2mul t1 t2 : (Fp_t '× Fp_t) in
  let t1 := fp2mul xovery xovery : (Fp_t '× Fp_t) in
  let t2 := fp2mul (fp2fromfp TWO) x1 : (Fp_t '× Fp_t) in
  let x3 := fp2sub t1 t2 : (Fp_t '× Fp_t) in
  let t1 := fp2sub x1 x3 : (Fp_t '× Fp_t) in
  let t2 := fp2mul xovery t1 : (Fp_t '× Fp_t) in
  let y3 := fp2sub t2 y1 : (Fp_t '× Fp_t) in
  (x3,y3,false).

Definition g2double (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let '(_x1,y1,inf1) := p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  if
    andb (ne y1 fp2zero) inf1
  then
    g2double_a p
  else
    (fp2zero,fp2zero,true).

Definition g2add (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) (q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let '(x1,y1,inf1) := p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let '(x2,y2,inf2) := q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  if
    inf1
  then
    q
  else
    if
      inf2
    then
      p
    else
      if
        eq p q
      then
        g2double p
      else
        if
          andb (eq x1 x2) (eq y1 (fp2neg y2))
        then
          g2add_a p q
        else
          (fp2zero,fp2zero,true).

Definition g2mul (m : Scalar_t) (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let t := (fp2zero,fp2zero,true) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  foldi (@repr WORDSIZE32 0) (@repr WORDSIZE32 256) (fun i t =>
    let t := g2double t : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
    if
      bit m ((@repr WORDSIZE32 255).-i)
    then
      g2add t p
    else
      t) t.

Definition g2neg (p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) :=
  let '(x,y,inf) := p : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  (x,fp2neg y,inf).

Definition twist (p : (Fp_t '× Fp_t '× bool)) : ((((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) '× (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) :=
  let '(p0,p1,_) := p : (Fp_t '× Fp_t '× bool) in
  let x := ((fp2zero,fp2fromfp p0,fp2zero),fp6zero) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let y := (fp6zero,(fp2zero,fp2fromfp p1,fp2zero)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  (x,y).

Definition line_double_p (r : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) (p : (Fp_t '× Fp_t '× bool)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(r0,r1,_) := r : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let a := fp2mul (fp2fromfp (from_literal (@repr WORDSIZE128 3))) (fp2mul r0 r0) : (Fp_t '× Fp_t) in
  let a := fp2mul a (fp2inv (fp2mul (fp2fromfp TWO) r1)) : (Fp_t '× Fp_t) in
  let b := fp2sub r1 (fp2mul a r0) : (Fp_t '× Fp_t) in
  let a := fp12fromfp6 (fp6fromfp2 a) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let b := fp12fromfp6 (fp6fromfp2 b) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let '(x,y) := twist p : ((((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) '× (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) in
  fp12neg (fp12sub (fp12sub y (fp12mul a x)) b).

Definition line_add_p (r : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) (q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) (p : (Fp_t '× Fp_t '× bool)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '(r0,r1,_) := r : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let '(q0,q1,_) := q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let a := fp2mul (fp2sub q1 r1) (fp2inv (fp2sub q0 r0)) : (Fp_t '× Fp_t) in
  let b := fp2sub r1 (fp2mul a r0) : (Fp_t '× Fp_t) in
  let a := fp12fromfp6 (fp6fromfp2 a) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let b := fp12fromfp6 (fp6fromfp2 b) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let '(x,y) := twist p : ((((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) '× (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) in
  fp12neg (fp12sub (fp12sub y (fp12mul a x)) b).

Definition frobenius (f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let '((g0,g1,g2),(h0,h1,h2)) := f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp2conjugate g0 : (Fp_t '× Fp_t) in
  let t2 := fp2conjugate h0 : (Fp_t '× Fp_t) in
  let t3 := fp2conjugate g1 : (Fp_t '× Fp_t) in
  let t4 := fp2conjugate h1 : (Fp_t '× Fp_t) in
  let t5 := fp2conjugate g2 : (Fp_t '× Fp_t) in
  let t6 := fp2conjugate h2 : (Fp_t '× Fp_t) in
  let c1 := ArrayFp (array_from_list _ [0x8D0775ED92235FB8;0xF67EA53D63E7813D;0x7B2443D784BAB9C4;0x0FD603FD3CBD5F4F;0xC231BEB4202C0D1F;0x1904D3BF02BB0667]) : ArrayFp_t in
  let c1 := to_le_bytes c1 : Seq_t U8_t in
  let c1 := from_byte_seq_le c1 : Fp_t in
  let c2 := ArrayFp (array_from_list _ [0x2CF78A126DDC4AF3;0x282D5AC14D6C7EC2;0xEC0C8EC971F63C5F;0x54A14787B6C7B36F;0x88E9E902231F9FB8;0x00FC3E2B36C4E032]) : ArrayFp_t in
  let c2 := to_le_bytes c2 : Seq_t U8_t in
  let c2 := from_byte_seq_le c2 : Fp_t in
  let gamma11 := (c1,c2) : (Fp_t '× Fp_t) in
  let gamma12 := fp2mul gamma11 gamma11 : (Fp_t '× Fp_t) in
  let gamma13 := fp2mul gamma12 gamma11 : (Fp_t '× Fp_t) in
  let gamma14 := fp2mul gamma13 gamma11 : (Fp_t '× Fp_t) in
  let gamma15 := fp2mul gamma14 gamma11 : (Fp_t '× Fp_t) in
  let t2 := fp2mul t2 gamma11 : (Fp_t '× Fp_t) in
  let t3 := fp2mul t3 gamma12 : (Fp_t '× Fp_t) in
  let t4 := fp2mul t4 gamma13 : (Fp_t '× Fp_t) in
  let t5 := fp2mul t5 gamma14 : (Fp_t '× Fp_t) in
  let t6 := fp2mul t6 gamma15 : (Fp_t '× Fp_t) in
  ((t1,t3,t5),(t2,t4,t6)).

Definition final_exponentiation (f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)))) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let fp6 := fp12conjugate f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let finv := fp12inv f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let fp6_1 := fp12mul fp6 finv : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let fp8 := frobenius (frobenius fp6_1) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let f := fp12mul fp8 fp6_1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let u := from_literal (@repr WORDSIZE128 15132376222941642752) : Scalar_t in
  let u_half := from_literal (@repr WORDSIZE128 7566188111470821376) : Scalar_t in
  let t0 := fp12mul f f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12exp t0 u : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12conjugate t1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12exp t1 u_half : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12conjugate t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t3 := fp12conjugate f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12mul t3 t1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12conjugate t1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12mul t1 t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12exp t1 u : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12conjugate t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t3 := fp12exp t2 u : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t3 := fp12conjugate t3 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12conjugate t1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t3 := fp12mul t1 t3 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12conjugate t1 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := frobenius (frobenius (frobenius t1)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := frobenius (frobenius t2) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12mul t1 t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12exp t3 u : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12conjugate t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12mul t2 t0 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := fp12mul t2 f : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t1 := fp12mul t1 t2 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let t2 := frobenius t3 : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  fp12mul t1 t2.

Definition pairing (p : (Fp_t '× Fp_t '× bool)) (q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) :=
  let t := from_literal (@repr WORDSIZE128 15132376222941642752) : Scalar_t in
  let r := q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
  let f := fp12fromfp6 (fp6fromfp2 (fp2fromfp ONE)) : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
  let '(f,r) := foldi (@repr WORDSIZE32 1) (@repr WORDSIZE32 64) (fun i '(f,r) =>
      let lrr := line_double_p r p : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
      let r := g2double r : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
      let f := fp12mul (fp12mul f f) lrr : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
      if
        bit t (((@repr WORDSIZE32 64).-i).-(@repr WORDSIZE32 1))
      then
        let lrq := line_add_p r q p : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
        let r := g2add r q : ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool) in
        let f := fp12mul f lrq : (((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) in
        (f,r)
      else
        (f,r)) (f,r) : ((((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t)) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× (Fp_t '× Fp_t))) '× ((Fp_t '× Fp_t) '× (Fp_t '× Fp_t) '× bool)) in
  final_exponentiation (fp12conjugate f).
