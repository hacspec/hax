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

Notation State := (nseq int32 16).

Notation Constants := (nseq int32 4).

Notation Block := (nseq int8 64).

Notation ChaChaIV := (nseq int8 12).

Notation ChaChaKey := (nseq int8 32).

Definition chacha20_line (a : int32) (b : int32) (d : int32) (s : int32) (m : State) : State :=
  let state := m : State in
  let state := state.[a]<-((state.[a]).+(state.[b])) : State in
  let state := state.[d]<-((state.[d]).^(state.[a])) : State in
  state.[d]<-(rol (state.[d]) s).

  Definition chacha20_quarter_round (a : int32) (b : int32) (c : int32)
                                    (d : int32) (state : State) : State :=
    let state := chacha20_line a b d 16 state : State in
    let state := chacha20_line c d b 12 state : State in
    let state := chacha20_line a b d 8 state : State in
    chacha20_line c d b 7 state.

Definition chacha20_double_round (state : State) : State :=
  let state := chacha20_quarter_round 0 4 8 12 state : State in
  let state := chacha20_quarter_round 1 5 9 13 state : State in
  let state := chacha20_quarter_round 2 6 10 14 state : State in
  let state := chacha20_quarter_round 3 7 11 15 state : State in
  let state := chacha20_quarter_round 0 5 10 15 state : State in
  let state := chacha20_quarter_round 1 6 11 12 state : State in
  let state := chacha20_quarter_round 2 7 8 13 state : State in
  chacha20_quarter_round 3 4 9 14 state.

Definition chacha20_rounds (state : State) : State :=
  let st := state : State in
  foldi 0 10 (fun _i st =>
    chacha20_double_round st) st.

Definition chacha20_core (ctr : U32) (st0 : State) : State :=
  let state := st0 : State in
  let state := state.[12]<-((state.[12]).+ctr) : State in
  let k := chacha20_rounds state : State in
  k.+state.

Definition chacha20_constants_init : Constants :=
  let constants := new : Constants in
  let constants := constants.[0]<-(Build_secret 1634760805) : Constants in
  let constants := constants.[1]<-(Build_secret 857760878) : Constants in
  let constants := constants.[2]<-(Build_secret 2036477234) : Constants in
  constants.[3]<-(Build_secret 1797285236).

Definition chacha20_init (key : ChaChaKey) (iv : ChaChaIV) (ctr : U32) : State :=
  let st := new : State in
  let st := update st 0 chacha20_constants_init : State in
  let st := update st 4 (to_le_U32s key) : State in
  let st := st.[12]<-ctr : State in
  update st 13 (to_le_U32s iv).

Definition chacha20_key_block (state : State) : Block :=
  let state := chacha20_core (Build_secret 0) state : State in
  from_seq (to_le_bytes state).

Definition chacha20_key_block0 (key : ChaChaKey) (iv : ChaChaIV) : Block :=
  let state := chacha20_init key iv (Build_secret 0) : State in
  chacha20_key_block state.

Definition chacha20_encrypt_block (st0 : State) (ctr : U32) (plain : Block) : Block :=
  let st := chacha20_core ctr st0 : State in
  let pl := from_seq (to_le_U32s plain) : State in
  let st := pl.^st : State in
  from_seq (to_le_bytes st).

Definition chacha20_encrypt_last (st0 : State) (ctr : U32) (plain : Seq U8) : Seq U8 :=
  let b := new : Block in
  let b := update b 0 plain : Block in
  let b := chacha20_encrypt_block st0 ctr b : Block in
  slice b 0 (len plain).

Definition chacha20_update (st0 : State) (m : Seq U8) : Seq U8 :=
  let blocks_out := new_seq (len m) : Seq U8 in
  let n_blocks := num_exact_chunks m 64 : int32 in
  let blocks_out := foldi 0 n_blocks (fun i blocks_out =>
      let msg_block := get_exact_chunk m 64 i : Seq U8 in
      let b := chacha20_encrypt_block st0 (Build_secret i) (from_seq msg_block) : Block in
      set_exact_chunk blocks_out 64 i b) blocks_out : Seq U8 in
  let last_block := get_remainder_chunk m 64 : Seq U8 in
  if
    (len last_block)<>0
  then
    let b := chacha20_encrypt_last st0 (Build_secret n_blocks) last_block : Seq U8 in
    set_chunk blocks_out 64 n_blocks b
  else
    blocks_out.

Definition chacha20 (key : ChaChaKey) (iv : ChaChaIV) (ctr : int32) (m : Seq U8) : Seq U8 :=
  let state := chacha20_init key iv (Build_secret ctr) : State in
  chacha20_update state m.
