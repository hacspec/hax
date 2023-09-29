module Libcrux.Kem.Kyber768.Conversions
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core

(*
let into_padded_array (#len: usize) (slice: slice u8) : array u8 v_LEN =
  let _:Prims.unit =
    if true
    then
      let _:Prims.unit =
        if ~.((Core.Slice.len_under_impl slice <: usize) <=. v_LEN <: bool)
        then
          Rust_primitives.Hax.never_to_any (Core.Panicking.panic "assertion failed: slice.len() <= LEN"

              <:
              Rust_primitives.Hax.t_Never)
      in
      ()
  in
  let out:array u8 v_LEN = Rust_primitives.Hax.repeat 0uy v_LEN in
  let out:array u8 v_LEN =
    Rust_primitives.Hax.update_at out
      ({
          Core.Ops.Range.Range.f_start = 0sz;
          Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl slice <: usize
        })
      (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut out
              ({
                  Core.Ops.Range.Range.f_start = 0sz;
                  Core.Ops.Range.Range.f_end = Core.Slice.len_under_impl slice <: usize
                })
            <:
            slice u8)
          slice
        <:
        slice u8)
  in
  out

class t_UpdatingArray (v_Self: Type) = { push:self -> slice u8 -> self }

type t_UpdatableArray = {
  f_value:array u8 v_LEN;
  f_pointer:usize
}

let new_under_impl (#len: usize) (value: array u8 v_LEN) : t_UpdatableArray v_LEN =
  {
    Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_value = value;
    Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer = 0sz
  }

let array_under_impl (#len: usize) (self: t_UpdatableArray v_LEN) : array u8 v_LEN =
  self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_value

let impl (#len: usize) : t_UpdatingArray (t_UpdatableArray v_LEN) =
  {
    push
    =
    fun (#len: usize) (self: t_UpdatableArray v_LEN) (other: slice u8) ->
      let self:t_UpdatableArray v_LEN =
        {
          self with
          Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_value
          =
          Rust_primitives.Hax.update_at (Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_value self

              <:
              t_UpdatableArray v_LEN)
            ({
                Core.Ops.Range.Range.f_start
                =
                self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer;
                Core.Ops.Range.Range.f_end
                =
                self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer +.
                (Core.Slice.len_under_impl other <: usize)
                <:
                usize
              })
            (Core.Slice.copy_from_slice_under_impl (Core.Ops.Index.IndexMut.index_mut self
                      .Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_value
                    ({
                        Core.Ops.Range.Range.f_start
                        =
                        self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer;
                        Core.Ops.Range.Range.f_end
                        =
                        self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer +.
                        (Core.Slice.len_under_impl other <: usize)
                        <:
                        usize
                      })
                  <:
                  slice u8)
                other
              <:
              slice u8)
        }
      in
      let self:t_UpdatableArray v_LEN =
        {
          self with
          Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer
          =
          self.Libcrux.Kem.Kyber768.Conversions.UpdatableArray.f_pointer +.
          (Core.Slice.len_under_impl other <: usize)
        }
      in
      self
  }

  *)
  
let to_unsigned_representative (fe: i32) : u16 =
  cast (fe +. ((fe <<. 15l <: i32) &. Libcrux.Kem.Kyber768.Parameters.v_FIELD_MODULUS <: i32))
