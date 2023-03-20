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

Notation SBox := (nseq int8 256).
Definition Build_SBox (x : nseq int8 256) : nseq int8 256 :=
  x.

Notation RCon := (nseq int8 15).
Definition Build_RCon (x : nseq int8 15) : nseq int8 15 :=
  x.

Notation PBytes256 := (nseq int8 256).
Definition Build_PBytes256 (x : nseq int8 256) : nseq int8 256 :=
  x.

Definition SBOX : SBox :=
  Build_SBox (array_from_list _ [99;124;119;123;242;107;111;197;48;1;103;43;254;215;171;118;202;130;201;125;250;89;71;240;173;212;162;175;156;164;114;192;183;253;147;38;54;63;247;204;52;165;229;241;113;216;49;21;4;199;35;195;24;150;5;154;7;18;128;226;235;39;178;117;9;131;44;26;27;110;90;160;82;59;214;179;41;227;47;132;83;209;0;237;32;252;177;91;106;203;190;57;74;76;88;207;208;239;170;251;67;77;51;133;69;249;2;127;80;60;159;168;81;163;64;143;146;157;56;245;188;182;218;33;16;255;243;210;205;12;19;236;95;151;68;23;196;167;126;61;100;93;25;115;96;129;79;220;34;42;144;136;70;238;184;20;222;94;11;219;224;50;58;10;73;6;36;92;194;211;172;98;145;149;228;121;231;200;55;109;141;213;78;169;108;86;244;234;101;122;174;8;186;120;37;46;28;166;180;198;232;221;116;31;75;189;139;138;112;62;181;102;72;3;246;14;97;53;87;185;134;193;29;158;225;248;152;17;105;217;142;148;155;30;135;233;206;85;40;223;140;161;137;13;191;230;66;104;65;153;45;15;176;84;187;22]).

Definition RCON : RCon :=
  Build_RCon (array_from_list _ [141;1;2;4;8;16;32;64;128;27;54;108;216;171;77]).

Definition index_u32 (s : int128) (i : int32) : int32 :=
  (s shift_right (i.*32)).%(1 shift_left 32).

Definition index_u8 (s : int32) (i : int32) : int8 :=
  (s shift_right (i.*8)).%(1 shift_left 8).

Definition rebuild_u32 (s0 : int8) (s1 : int8) (s2 : int8) (s3 : int8) : int32 :=
  s0.|((s1 shift_left 8).|((s2 shift_left 16).|(s3 shift_left 24))).

Definition rebuild_u128 (s0 : int32) (s1 : int32) (s2 : int32) (s3 : int32) : int128 :=
  s0.|((s1 shift_left 32).|((s2 shift_left 64).|(s3 shift_left 96))).

Definition subword (v : int32) : int32 :=
  rebuild_u32 (SBOX.[(index_u8 v 0)]) (SBOX.[(index_u8 v 1)]) (SBOX.[(index_u8 v 2)]) (SBOX.[(index_u8 v 3)]).

Definition rotword (v : int32) : int32 :=
  rebuild_u32 (index_u8 v 1) (index_u8 v 2) (index_u8 v 3) (index_u8 v 0).

Definition vpshufd1 (s : int128) (o : int8) (i : int32) : int32 :=
  index_u32 (s shift_right (32.*((o shift_right (2.*i)).%4))) 0.

Definition vpshufd (s : int128) (o : int8) : int128 :=
  let d1 := vpshufd1 s o 0 : int32 in
  let d2 := vpshufd1 s o 1 : int32 in
  let d3 := vpshufd1 s o 2 : int32 in
  let d4 := vpshufd1 s o 3 : int32 in
  rebuild_u128 d1 d2 d3 d4.

Definition vshufps (s1 : int128) (s2 : int128) (o : int8) : int128 :=
  let d1 := vpshufd1 s1 o 0 : int32 in
  let d2 := vpshufd1 s1 o 1 : int32 in
  let d3 := vpshufd1 s2 o 2 : int32 in
  let d4 := vpshufd1 s2 o 3 : int32 in
  rebuild_u128 d1 d2 d3 d4.

Definition key_combine (rkey : int128) (temp1 : int128) (temp2 : int128) : (int128 '× int128) :=
  let temp1 := vpshufd temp1 255 : int128 in
  let temp2 := vshufps temp2 rkey 16 : int128 in
  let rkey := rkey.^temp2 : int128 in
  let temp2 := vshufps temp2 rkey 140 : int128 in
  let rkey := rkey.^temp2 : int128 in
  let rkey := rkey.^temp1 : int128 in
  (rkey,temp2).

Definition aeskeygenassist (v1 : int128) (v2 : int8) : int128 :=
  let x1 := index_u32 v1 1 : int32 in
  let x3 := index_u32 v1 3 : int32 in
  let y0 := subword x1 : int32 in
  let y1 := (rotword y0).^v2 : int32 in
  let y2 := subword x3 : int32 in
  let y3 := (rotword y2).^v2 : int32 in
  rebuild_u128 y0 y1 y2 y3.

Definition key_expand (rcon : int8) (rkey : int128) (temp2 : int128) : (int128 '× int128) :=
  let temp1 := aeskeygenassist rkey rcon : int128 in
  key_combine rkey temp1 temp2.

Notation KeyList := (Seq int128).

Definition keys_expand (key : int128) : Seq int128 :=
  let rkeys := new_seq 0 : Seq int128 in
  let key := key : int128 in
  let rkeys := push rkeys key : Seq int128 in
  let temp2 := 0 : int128 in
  let '(key,rkeys,temp2) := foldi 1 11 (fun round '(key,rkeys,temp2) =>
      let rcon := RCON.[round] : int8 in
      let '(key_temp,temp2_temp) := key_expand rcon key temp2 : (int128 '× int128) in
      let key := key_temp : int128 in
      let temp2 := temp2_temp : int128 in
      let rkeys := push rkeys key : Seq int128 in
      (key,rkeys,temp2)) (key,rkeys,temp2) : (int128 '× Seq int128 '× int128) in
  rkeys.

Definition subbytes (s : int128) : int128 :=
  rebuild_u128 (subword (index_u32 s 0)) (subword (index_u32 s 1)) (subword (index_u32 s 2)) (subword (index_u32 s 3)).

Definition matrix_index (s : int128) (i : int32) (j : int32) : int8 :=
  index_u8 (index_u32 s j) i.

Definition shiftrows (s : int128) : int128 :=
  rebuild_u128 (rebuild_u32 (matrix_index s 0 0) (matrix_index s 1 1) (matrix_index s 2 2) (matrix_index s 3 3)) (rebuild_u32 (matrix_index s 0 1) (matrix_index s 1 2) (matrix_index s 2 3) (matrix_index s 3 0)) (rebuild_u32 (matrix_index s 0 2) (matrix_index s 1 3) (matrix_index s 2 0) (matrix_index s 3 1)) (rebuild_u32 (matrix_index s 0 3) (matrix_index s 1 0) (matrix_index s 2 1) (matrix_index s 3 2)).

Definition xtime (x : int8) : int8 :=
  let x1 := x shift_left 1 : int8 in
  let x7 := x shift_right 7 : int8 in
  let x71 := x7.&1 : int8 in
  let x711b := x71.*27 : int8 in
  x1.^x711b.

Definition mixcolumn (c : int32) (state : int128) : int32 :=
  let s0 := matrix_index state 0 c : int8 in
  let s1 := matrix_index state 1 c : int8 in
  let s2 := matrix_index state 2 c : int8 in
  let s3 := matrix_index state 3 c : int8 in
  let tmp := ((s0.^s1).^s2).^s3 : int8 in
  let r0 := (s0.^tmp).^(xtime (s0.^s1)) : int8 in
  let r1 := (s1.^tmp).^(xtime (s1.^s2)) : int8 in
  let r2 := (s2.^tmp).^(xtime (s2.^s3)) : int8 in
  let r3 := (s3.^tmp).^(xtime (s3.^s0)) : int8 in
  rebuild_u32 r0 r1 r2 r3.

Definition mixcolumns (state : int128) : int128 :=
  let c0 := mixcolumn 0 state : int32 in
  let c1 := mixcolumn 1 state : int32 in
  let c2 := mixcolumn 2 state : int32 in
  let c3 := mixcolumn 3 state : int32 in
  rebuild_u128 c0 c1 c2 c3.

Definition aesenc (state : int128) (rkey : int128) : int128 :=
  let state := shiftrows state : int128 in
  let state := subbytes state : int128 in
  let state := mixcolumns state : int128 in
  state.^rkey.

Definition aesenclast (state : int128) (rkey : int128) : int128 :=
  let state := shiftrows state : int128 in
  let state := subbytes state : int128 in
  state.^rkey.

Definition aes_rounds (rkeys : Seq int128) (inp : int128) : int128 :=
  let state := inp.^(rkeys.[0]) : int128 in
  let state := foldi 1 10 (fun round state =>
      aesenc state (rkeys.[round])) state : int128 in
  aesenclast state (rkeys.[10]).

Definition aes (key : int128) (inp : int128) : int128 :=
  let rkeys := keys_expand key : Seq int128 in
  aes_rounds rkeys inp.
