From Hacspec Require Import Hacspec_Lib MachineIntegers.
From Coq Require Import ZArith.
Import List.ListNotations.
Open Scope Z_scope.
Open Scope bool_scope.
Open Scope hacspec_scope.

Definition U8 := int8. (* Secret int  *)
Definition U16 := int16. (* Secret int  *)
Definition U32 := int32. (* Secret int  *)
Definition U64 := int64. (* Secret int  *)
Definition U128 := int128. (* Secret int  *)

Notation " x .[ a ]" := (array_index x a) (at level 40).
Notation " x .[ i ]<- a" := (array_upd x i a) (at level 40).

Class Addition A := add : A -> A -> A.
Notation "a .+ b" := (add a b).
Instance array_add_inst {ws : WORDSIZE} {len: nat} : Addition (nseq (@int ws) len) := { add a b := a array_add b }.
Instance int_add_inst {ws : WORDSIZE} : Addition (@int ws) := { add a b := MachineIntegers.add a b }.

Class Xor A := xor : A -> A -> A.
Notation "a .^ b" := (xor a b).

Instance array_xor_inst {ws : WORDSIZE} {len: nat} : Xor (nseq (@int ws) len) := { xor a b := a array_xor b }.
Instance int_xor_inst {ws : WORDSIZE} : Xor (@int ws) := { xor a b := MachineIntegers.xor a b }.

Definition new {A : Type} `{Default A} {len} : nseq A len := array_new_ default _.
Class array_or_seq A len :=
{ as_seq : seq A ; as_nseq : nseq A len }.

Arguments as_seq {_} {_} array_or_seq.
Arguments as_nseq {_} {_} array_or_seq.

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
Definition from_seq {A : Type}  `{Default A} {len} (s : seq A) : nseq A len := array_from_seq _ s.

Notation Seq := seq.
Notation len := length.

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


(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation State := (nseq U32 16).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation StateIdx := (int32).

Notation Constants := (nseq U32 4).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation ConstantsIdx := (int32).

Notation Block := (nseq U8 64).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation ChaChaIV := (nseq U8 12).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Notation ChaChaKey := (nseq U8 32).

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

(*Not implemented yet? todo(item)*)

Definition chacha20_line (a : int32) (b : int32) (d : int32) (s : int32) (m : State) : State :=
  let state : State := m in
  let state : State := state.[a]<-((state.[a]).+(state.[b])) in
  let state : State := state.[d]<-((state.[d]) .^ (state.[a])) in
  state.[d]<-(rol (state.[d]) s).

Definition chacha20_quarter_round (a : int32) (b : int32) (c : int32) (d : int32) (state : State) : State :=
  let state : State := chacha20_line a b d 16 state in
  let state : State := chacha20_line c d b 12 state in
  let state : State := chacha20_line a b d 8 state in
  chacha20_line c d b 7 state.

Definition chacha20_double_round (state : State) : State :=
  let state : State := chacha20_quarter_round 0 4 8 12 state in
  let state : State := chacha20_quarter_round 1 5 9 13 state in
  let state : State := chacha20_quarter_round 2 6 10 14 state in
  let state : State := chacha20_quarter_round 3 7 11 15 state in
  let state : State := chacha20_quarter_round 0 5 10 15 state in
  let state : State := chacha20_quarter_round 1 6 11 12 state in
  let state : State := chacha20_quarter_round 2 7 8 13 state in
  chacha20_quarter_round 3 4 9 14 state.

Definition chacha20_rounds (state : State) : State :=
  let st : State := state in
  foldi 0 10 (fun _i st =>
    chacha20_double_round st) st.

Definition chacha20_core (ctr : U32) (st0 : State) : State :=
  let state : State := st0 in
  let state : State := state.[12]<-((state.[12]).+ctr) in
  let k : State := chacha20_rounds state in
  k.+state.

Definition chacha20_constants_init : Constants :=
  let constants : Constants := new in
  let constants : Constants := constants.[0]<-(secret 1634760805) in
  let constants : Constants := constants.[1]<-(secret 857760878) in
  let constants : Constants := constants.[2]<-(secret 2036477234) in
  constants.[3]<-(secret 1797285236).

Definition chacha20_init (key : ChaChaKey) (iv : ChaChaIV) (ctr : U32) : State :=
  let st : State := new in
  let st : State := update st 0 chacha20_constants_init in
  let st : State := update st 4 (to_le_U32s key) in
  let st : State := st.[12]<-ctr in
  update st 13 (to_le_U32s iv).

Definition chacha20_key_block (state : State) : Block :=
  let state : State := chacha20_core (secret 0) state in
  from_seq (to_le_bytes state).

Definition chacha20_key_block0 (key : ChaChaKey) (iv : ChaChaIV) : Block :=
  let state : State := chacha20_init key iv (secret 0) in
  chacha20_key_block state.

Definition chacha20_encrypt_block (st0 : State) (ctr : U32) (plain : Block) : Block :=
  let st : State := chacha20_core ctr st0 in
  let pl : State := from_seq (to_le_U32s plain) in
  let st : State := pl .^ st in
  from_seq (to_le_bytes st).

Definition chacha20_encrypt_last (st0 : State) (ctr : U32) (plain : Seq U8) : Seq U8 :=
  let b : Block := new in
  let b : Block := update b 0 plain in
  let b : Block := chacha20_encrypt_block st0 ctr b in
  slice b 0 (len plain).

Definition chacha20_update (st0 : State) (m : Seq U8) : Seq U8 :=
  let blocks_out : Seq U8 := new_seq (len m) in
  let n_blocks : int32 := num_exact_chunks m 64 in
  let blocks_out : Seq U8 := foldi 0 n_blocks (fun i blocks_out =>
      let msg_block : Seq U8 := get_exact_chunk m 64 i in
      let b : Block := chacha20_encrypt_block st0 (secret i) (from_seq msg_block) in
      set_exact_chunk blocks_out 64 i b) blocks_out in
  let last_block : Seq U8 := get_remainder_chunk m 64 in
  if
    (len last_block)<>0
  then
    let b : Seq U8 := chacha20_encrypt_last st0 (secret n_blocks) last_block in
    set_chunk blocks_out 64 n_blocks b
  else
    blocks_out.

Definition chacha20 (key : ChaChaKey) (iv : ChaChaIV) (ctr : int32) (m : Seq U8) : Seq U8 :=
  let state : State := chacha20_init key iv (secret ctr) in
  chacha20_update state m.