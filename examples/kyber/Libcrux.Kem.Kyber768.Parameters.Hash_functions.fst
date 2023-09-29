module Libcrux.Kem.Kyber768.Parameters.Hash_functions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_G (input: slice u8) : array u8 64sz = Libcrux.Digest.sha3_512_ input

let v_H_DIGEST_SIZE: usize = Libcrux.Digest.digest_size Libcrux.Digest.Algorithm_Sha3_256_

let v_H (input: slice u8) : array u8 32sz = Libcrux.Digest.sha3_256_ input

let v_PRF (#len: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input

let v_XOF (#len: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake128 input

let v_KDF (#len: usize) (input: slice u8) : array u8 v_LEN = Libcrux.Digest.shake256 input