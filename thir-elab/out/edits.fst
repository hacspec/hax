
open FStar.Mul
open Hacspec.Lib

type state = lseq (uint32) (16)

let state_idx =
  nat_mod (16)

type constants = lseq (uint32) (4)

let constants_idx =
  nat_mod (4)

type block = lseq (uint8) (64)

type cha_cha_iv = lseq (uint8) (12)

type cha_cha_key = lseq (uint8) (32)

let (.[]<-) (#a: Type) (#len:uint_size) = array_upd #a #len
