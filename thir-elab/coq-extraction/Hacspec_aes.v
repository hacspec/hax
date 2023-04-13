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


Record x_t : Type :={
  temp : int32;
}.

Definition x_test : x_t :=
  Build_x_t 3.

Notation Name_t := (nseq int8 3).
Definition Name : Name_t -> Name_t :=
  id.

Definition name_test : Name_t :=
  Name (array_from_list _ [3;4;5]).

Inductive p_t : Type :=
| CASE1 : int32 -> p_t
| CASE2 : int8 -> p_t.

Definition enum_test : p_t :=
  CASE1 32.

Definition private : U64_t :=
  U64 5.

Definition BLOCKSIZE : int32 :=
  16.

Definition IVSIZE : int32 :=
  12.

Definition KEY_LENGTH : int32 :=
  4.

Definition ROUNDS : int32 :=
  10.

Definition KEY_SCHEDULE_LENGTH : int32 :=
  176.

Definition ITERATIONS : int32 :=
  40.

Definition INVALID_KEY_EXPANSION_INDEX : int8 :=
  1.

Notation Block_t := (nseq int8 BLOCKSIZE).
Definition Block : Block_t -> Block_t :=
  id.

Notation Word_t := (nseq int8 KEY_LENGTH).
Definition Word : Word_t -> Word_t :=
  id.

Notation RoundKey_t := (nseq int8 BLOCKSIZE).
Definition RoundKey : RoundKey_t -> RoundKey_t :=
  id.

Notation AesNonce_t := (nseq int8 IVSIZE).
Definition AesNonce : AesNonce_t -> AesNonce_t :=
  id.

Notation SBox_t := (nseq int8 2).
Definition SBox : SBox_t -> SBox_t :=
  id.

Notation RCon_t := (nseq int8 15).
Definition RCon : RCon_t -> RCon_t :=
  id.

Notation Bytes144_t := (nseq int8 144).
Definition Bytes144 : Bytes144_t -> Bytes144_t :=
  id.

Notation Bytes176_t := (nseq int8 KEY_SCHEDULE_LENGTH).
Definition Bytes176 : Bytes176_t -> Bytes176_t :=
  id.

Notation Key128_t := (nseq int8 BLOCKSIZE).
Definition Key128 : Key128_t -> Key128_t :=
  id.

Notation ByteSeqResult_t := (Result_t Seq_t U8_t int8).

Notation BlockResult_t := (Result_t Block_t int8).

Notation WordResult_t := (Result_t Word_t int8).

Definition SBOX : SBox_t :=
  SBox (array_from_list _ [0x8d;0x10]).
