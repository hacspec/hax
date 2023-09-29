module Libcrux.Kem.Kyber768.Parameters
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_FIELD_MODULUS: i32 = 3329l

let v_BITS_PER_COEFFICIENT: usize = 12sz

let v_COEFFICIENTS_IN_RING_ELEMENT: usize = 256sz

let v_BITS_PER_RING_ELEMENT: usize = v_COEFFICIENTS_IN_RING_ELEMENT *. 12sz

let v_BYTES_PER_RING_ELEMENT: usize = v_BITS_PER_RING_ELEMENT /. 8sz

let v_REJECTION_SAMPLING_SEED_SIZE: usize = 168sz *. 5sz

let v_RANK: usize = 3sz

let v_T_AS_NTT_ENCODED_SIZE: usize =
  ((v_RANK *. v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *. v_BITS_PER_COEFFICIENT <: usize) /. 8sz

let v_VECTOR_U_COMPRESSION_FACTOR: usize = 10sz

let v_VECTOR_V_COMPRESSION_FACTOR: usize = 4sz

let v_BYTES_PER_ENCODED_ELEMENT_OF_U: usize =
  (v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_U_COMPRESSION_FACTOR <: usize) /. 8sz

let v_VECTOR_U_ENCODED_SIZE: usize = v_RANK *. v_BYTES_PER_ENCODED_ELEMENT_OF_U

let v_VECTOR_V_ENCODED_SIZE: usize =
  (v_COEFFICIENTS_IN_RING_ELEMENT *. v_VECTOR_V_COMPRESSION_FACTOR <: usize) /. 8sz

let v_CPA_PKE_KEY_GENERATION_SEED_SIZE: usize = 32sz

let v_CPA_PKE_SECRET_KEY_SIZE: usize =
  ((v_RANK *. v_COEFFICIENTS_IN_RING_ELEMENT <: usize) *. v_BITS_PER_COEFFICIENT <: usize) /. 8sz

let v_CPA_PKE_PUBLIC_KEY_SIZE: usize = v_T_AS_NTT_ENCODED_SIZE +. 32sz

let v_CPA_PKE_CIPHERTEXT_SIZE: usize = v_VECTOR_U_ENCODED_SIZE +. v_VECTOR_V_ENCODED_SIZE

let v_CPA_PKE_MESSAGE_SIZE: usize = 32sz

// let v_CPA_SERIALIZED_KEY_LEN: usize =
//   ((v_CPA_PKE_SECRET_KEY_SIZE +. v_CPA_PKE_PUBLIC_KEY_SIZE <: usize) +.
//     Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
//     <:
//     usize) +.
//   v_CPA_PKE_MESSAGE_SIZE
  
