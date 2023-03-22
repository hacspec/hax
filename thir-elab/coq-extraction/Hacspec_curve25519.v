From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Definition int_xI {WS : WORDSIZE} (a : int) : int := MachineIntegers.add (MachineIntegers.mul a (repr 2)) MachineIntegers.one.
Definition int_xO {WS : WORDSIZE} (a : int) : int := MachineIntegers.mul a (repr 2).
Number Notation int Pos.of_num_int Pos.to_num_int (via positive mapping [[int_xI] => xI, [int_xO] => xO , [MachineIntegers.one] => xH]) : hacspec_scope.
Notation "0" := (repr O).
Notation U8 := int8. (* Secret int  *)
Notation U16 := int16. (* Secret int  *)
Notation U32 := int32. (* Secret int  *)
Notation U64 := int64. (* Secret int  *)
Notation U128 := int128. (* Secret int  *)

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

Notation Seq := seq.
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


(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation FieldCanvas := (nseq int8 256).
Notation X25519FieldElement := (nat_mod 0x7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffed).

Notation ScalarCanvas := (nseq int8 256).
Notation Scalar := (nat_mod 0x8000000000000000000000000000000000000000000000000000000000000000).

Notation Point := ((X25519FieldElement '× X25519FieldElement)).

Notation X25519SerializedPoint := (nseq int8 32).

Notation X25519SerializedScalar := (nseq int8 32).

Definition mask_scalar (s : X25519SerializedScalar) : X25519SerializedScalar :=
  let k := s : X25519SerializedScalar in
  let k := k.[0]<-((k.[0]).&(Build_secret 248)) : X25519SerializedScalar in
  let k := k.[31]<-((k.[31]).&(Build_secret 127)) : X25519SerializedScalar in
  k.[31]<-((k.[31]).|(Build_secret 64)).

Definition decode_scalar (s : X25519SerializedScalar) : Scalar :=
  let k := mask_scalar s : X25519SerializedScalar in
  from_byte_seq_le k.

Definition decode_point (u : X25519SerializedPoint) : (X25519FieldElement '× X25519FieldElement) :=
  let u_ := u : X25519SerializedPoint in
  let u_ := u_.[31]<-((u_.[31]).&(Build_secret 127)) : X25519SerializedPoint in
  (from_byte_seq_le u_,from_literal 1).

Definition encode_point (p : (X25519FieldElement '× X25519FieldElement)) : X25519SerializedPoint :=
  let '(x,y) := p : (X25519FieldElement '× X25519FieldElement) in
  let b := x.*(inv y) : X25519FieldElement in
  update_start new (to_byte_seq_le b).

Definition point_add_and_double (q : (X25519FieldElement '× X25519FieldElement)) (np : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement))) : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) :=
  let '(nq,nqp1) := np : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
  let '(x_1,_z_1) := q : (X25519FieldElement '× X25519FieldElement) in
  let '(x_2,z_2) := nq : (X25519FieldElement '× X25519FieldElement) in
  let '(x_3,z_3) := nqp1 : (X25519FieldElement '× X25519FieldElement) in
  let a := x_2.+z_2 : X25519FieldElement in
  let aa := pow a 2 : X25519FieldElement in
  let b := x_2.-z_2 : X25519FieldElement in
  let bb := b.*b : X25519FieldElement in
  let e := aa.-bb : X25519FieldElement in
  let c := x_3.+z_3 : X25519FieldElement in
  let d := x_3.-z_3 : X25519FieldElement in
  let da := d.*a : X25519FieldElement in
  let cb := c.*b : X25519FieldElement in
  let x_3 := pow (da.+cb) 2 : X25519FieldElement in
  let z_3 := x_1.*(pow (da.-cb) 2) : X25519FieldElement in
  let x_2 := aa.*bb : X25519FieldElement in
  let e121665 := from_literal 121665 : X25519FieldElement in
  let z_2 := e.*(aa.+(e121665.*e)) : X25519FieldElement in
  ((x_2,z_2),(x_3,z_3)).

Definition swap (x : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement))) : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) :=
  let '(x0,x1) := x : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
  (x1,x0).

Definition montgomery_ladder (k : Scalar) (init : (X25519FieldElement '× X25519FieldElement)) : (X25519FieldElement '× X25519FieldElement) :=
  let inf := (from_literal 1,from_literal 0) : (X25519FieldElement '× X25519FieldElement) in
  let acc := (inf,init) : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
  let acc := foldi 0 256 (fun i acc =>
      if
        bit k (255.-i)
      then
        let acc := swap acc : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
        let acc := point_add_and_double init acc : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
        swap acc
      else
        point_add_and_double init acc) acc : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
  let '(out,_) := acc : ((X25519FieldElement '× X25519FieldElement) '× (X25519FieldElement '× X25519FieldElement)) in
  out.

Definition x25519_scalarmult (s : X25519SerializedScalar) (p : X25519SerializedPoint) : X25519SerializedPoint :=
  let s_ := decode_scalar s : Scalar in
  let p_ := decode_point p : (X25519FieldElement '× X25519FieldElement) in
  let r := montgomery_ladder s_ p_ : (X25519FieldElement '× X25519FieldElement) in
  encode_point r.

Definition x25519_secret_to_public (s : X25519SerializedScalar) : X25519SerializedPoint :=
  let base := new : X25519SerializedPoint in
  let base := base.[0]<-(Build_secret 9) : X25519SerializedPoint in
  x25519_scalarmult s base.
