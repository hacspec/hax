module Libcrux.Kem.Kyber768
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

let v_SHARED_SECRET_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE

let v_KEY_GENERATION_SEED_SIZE: usize =
  Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE +. v_SHARED_SECRET_SIZE

let v_PUBLIC_KEY_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE

// let v_SECRET_KEY_SIZE: usize =
//   ((Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE +.
//       Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
//       <:
//       usize) +.
//     Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
//     <:
//     usize) +.
//   v_SHARED_SECRET_SIZE

let v_CIPHERTEXT_SIZE: usize = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_CIPHERTEXT_SIZE

let t_Kyber768PublicKey = array u8 1184sz

let t_Kyber768PrivateKey = array u8 2400sz

let t_Kyber768Ciphertext = array u8 1088sz

let t_Kyber768SharedSecret = array u8 32sz

type t_BadRejectionSamplingRandomnessError =
  | BadRejectionSamplingRandomnessError : t_BadRejectionSamplingRandomnessError

(*
let generate_keypair (randomness: array u8 64sz)
    : Core.Result.t_Result (array u8 1184sz & array u8 2400sz) t_BadRejectionSamplingRandomnessError =
  let ind_cpa_keypair_randomness:slice u8 =
    randomness.[ {
        Core.Ops.Range.Range.f_start = 0sz;
        Core.Ops.Range.Range.f_end
        =
        Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let implicit_rejection_value:slice u8 =
    randomness.[ {
        Core.Ops.Range.RangeFrom.f_start
        =
        Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_KEY_GENERATION_SEED_SIZE
      } ]
  in
  let ind_cpa_key_pair, sampling_a_error:(Libcrux.Kem.Kyber768.Ind_cpa.t_KeyPair &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber768.Ind_cpa.generate_keypair ind_cpa_keypair_randomness
  in
  let secret_key_serialized:array u8 2400sz =
    Libcrux.Kem.Kyber768.Ind_cpa.serialize_secret_key_under_impl ind_cpa_key_pair
      implicit_rejection_value
  in
  match sampling_a_error with
  | Core.Option.Option_Some error -> Core.Result.Result_Err error
  | _ ->
    Core.Result.Result_Ok
    (Libcrux.Kem.Kyber768.Ind_cpa.pk_under_impl ind_cpa_key_pair, secret_key_serialized)

let encapsulate (public_key: array u8 1184sz) (randomness: array u8 32sz)
    : Core.Result.t_Result (array u8 1088sz & array u8 32sz) t_BadRejectionSamplingRandomnessError =
  let randomness_hashed:array u8 32sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize randomness
        <:
        slice u8)
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize randomness_hashed
        <:
        slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({
          Core.Ops.Range.RangeFrom.f_start
          =
          Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
                })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                      public_key
                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
        <:
        slice u8)
  in
  let hashed:array u8 64sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let ciphertext, sampling_a_error:(array u8 1088sz &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber768.Ind_cpa.encrypt (Rust_primitives.unsize public_key <: slice u8)
      randomness_hashed
      pseudorandomness
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array k_not
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({
          Core.Ops.Range.RangeFrom.f_start
          =
          Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
                })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                      ciphertext
                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
        <:
        slice u8)
  in
  let (shared_secret: array u8 32sz):array u8 32sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_KDF (Rust_primitives.unsize to_hash <: slice u8
      )
  in
  if Core.Option.is_some_under_impl sampling_a_error
  then Core.Result.Result_Err (Core.Option.unwrap_under_impl sampling_a_error)
  else Core.Result.Result_Ok (ciphertext, shared_secret)

let decapsulate (secret_key: array u8 2400sz) (ciphertext: array u8 1088sz) : array u8 32sz =
  let ind_cpa_secret_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize secret_key <: slice u8)
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_SECRET_KEY_SIZE
  in
  let ind_cpa_public_key, secret_key:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key
      Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_PUBLIC_KEY_SIZE
  in
  let ind_cpa_public_key_hash, implicit_rejection_value:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl secret_key
      Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H_DIGEST_SIZE
  in
  let decrypted:array u8 32sz =
    Libcrux.Kem.Kyber768.Ind_cpa.decrypt ind_cpa_secret_key ciphertext
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize decrypted <: slice u8
      )
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE }
      )
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({
                  Core.Ops.Range.RangeFrom.f_start
                  =
                  Libcrux.Kem.Kyber768.Parameters.v_CPA_PKE_MESSAGE_SIZE
                })
            <:
            slice u8)
          ind_cpa_public_key_hash
        <:
        slice u8)
  in
  let hashed:array u8 64sz =
    Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_G (Rust_primitives.unsize to_hash <: slice u8)
  in
  let k_not, pseudorandomness:(slice u8 & slice u8) =
    Core.Slice.split_at_under_impl (Rust_primitives.unsize hashed <: slice u8) 32sz
  in
  let expected_ciphertext, _:(array u8 1088sz &
    Core.Option.t_Option t_BadRejectionSamplingRandomnessError) =
    Libcrux.Kem.Kyber768.Ind_cpa.encrypt ind_cpa_public_key decrypted pseudorandomness
  in
  let selector:u8 =
    Libcrux.Kem.Kyber768.Constant_time_ops.compare_ciphertexts_in_constant_time (Rust_primitives.unsize
          ciphertext
        <:
        slice u8)
      (Rust_primitives.unsize expected_ciphertext <: slice u8)
  in
  let to_hash:array u8 32sz =
    Libcrux.Kem.Kyber768.Constant_time_ops.select_shared_secret_in_constant_time k_not
      implicit_rejection_value
      selector
  in
  let (to_hash: array u8 64sz):array u8 64sz =
    Libcrux.Kem.Kyber768.Conversions.into_padded_array (Rust_primitives.unsize to_hash <: slice u8)
  in
  let to_hash:array u8 64sz =
    Rust_primitives.Hax.update_at to_hash
      ({ Core.Ops.Range.RangeFrom.f_start = v_SHARED_SECRET_SIZE })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut to_hash
              ({ Core.Ops.Range.RangeFrom.f_start = v_SHARED_SECRET_SIZE })
            <:
            slice u8)
          (Rust_primitives.unsize (Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_H (Rust_primitives.unsize
                      ciphertext
                    <:
                    slice u8)
                <:
                array u8 32sz)
            <:
            slice u8)
        <:
        slice u8)
  in
  Libcrux.Kem.Kyber768.Parameters.Hash_functions.v_KDF (Rust_primitives.unsize to_hash <: slice u8)
  *)
  
