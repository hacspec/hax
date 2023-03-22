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

Notation PolyKey := (nseq int8 32).

Definition BLOCKSIZE : int32 :=
  16.

Notation PolyBlock := (nseq int8 16).

Notation Poly1305Tag := (nseq int8 16).

Notation SubBlock := (Seq U8).

Notation BlockIndex := (int32).

Notation FieldCanvas := (nseq int8 131).
Notation FieldElement := (nat_mod 0x03fffffffffffffffffffffffffffffffb).

Notation PolyState := ((FieldElement '× FieldElement '× PolyKey)).

Definition poly1305_encode_r (b : PolyBlock) : FieldElement :=
  let n := uint128_from_le_bytes (from_seq b) : U128 in
  let n := n.&(Build_secret 21267647620597763993911028882763415551) : U128 in
  from_secret_literal n.

Definition poly1305_encode_block (b : PolyBlock) : FieldElement :=
  let n := uint128_from_le_bytes (from_seq b) : U128 in
  let f := from_secret_literal n : FieldElement in
  f.+(pow2 128).

Definition poly1305_encode_last (pad_len : int32) (b : Seq U8) : FieldElement :=
  let n := uint128_from_le_bytes (from_slice b 0 (len b)) : U128 in
  let f := from_secret_literal n : FieldElement in
  f.+(pow2 (8.*pad_len)).

Definition poly1305_init (k : PolyKey) : (FieldElement '× FieldElement '× PolyKey) :=
  let r := poly1305_encode_r (from_slice k 0 16) : FieldElement in
  (zero,r,k).

Definition poly1305_update_block (b : PolyBlock) (st : (FieldElement '× FieldElement '× PolyKey)) : (FieldElement '× FieldElement '× PolyKey) :=
  let '(acc,r,k) := st : (FieldElement '× FieldElement '× PolyKey) in
  (((poly1305_encode_block b).+acc).*r,r,k).

Definition poly1305_update_blocks (m : Seq U8) (st : (FieldElement '× FieldElement '× PolyKey)) : (FieldElement '× FieldElement '× PolyKey) :=
  let st := st : (FieldElement '× FieldElement '× PolyKey) in
  let n_blocks := (len m)/BLOCKSIZE : int32 in
  foldi 0 n_blocks (fun i st =>
    let block := from_seq (get_exact_chunk m BLOCKSIZE i) : PolyBlock in
    poly1305_update_block block st) st.

Definition poly1305_update_last (pad_len : int32) (b : Seq U8) (st : (FieldElement '× FieldElement '× PolyKey)) : (FieldElement '× FieldElement '× PolyKey) :=
  let st := st : (FieldElement '× FieldElement '× PolyKey) in
  if
    (len b)<>0
  then
    let '(acc,r,k) := st : (FieldElement '× FieldElement '× PolyKey) in
    (((poly1305_encode_last pad_len b).+acc).*r,r,k)
  else
    st.

Definition poly1305_update (m : Seq U8) (st : (FieldElement '× FieldElement '× PolyKey)) : (FieldElement '× FieldElement '× PolyKey) :=
  let st := poly1305_update_blocks m st : (FieldElement '× FieldElement '× PolyKey) in
  let last := get_remainder_chunk m BLOCKSIZE : Seq U8 in
  poly1305_update_last (len last) last st.

Definition poly1305_finish (st : (FieldElement '× FieldElement '× PolyKey)) : Poly1305Tag :=
  let '(acc,_,k) := st : (FieldElement '× FieldElement '× PolyKey) in
  let n := uint128_from_le_bytes (from_slice k 16 16) : U128 in
  let aby := to_byte_seq_le acc : Seq U8 in
  let a := uint128_from_le_bytes (from_slice aby 0 16) : U128 in
  from_seq (U128_to_le_bytes (a.+n)).

Definition poly1305 (m : Seq U8) (key : PolyKey) : Poly1305Tag :=
  let st := poly1305_init key : (FieldElement '× FieldElement '× PolyKey) in
  let st := poly1305_update m st : (FieldElement '× FieldElement '× PolyKey) in
  poly1305_finish st.
