module Attributes
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let v_CBOR_NEG_INT_1BYTE_START: u8 = 32uy

let v_MAX_MESSAGE_SIZE_LEN: usize = sz 128 +! sz 64

type t_EdhocMessageBuffer = {
  f_content:t_Array u8 (sz 192);
  f_len:f_len: usize{f_len <=. v_MAX_MESSAGE_SIZE_LEN}
}

let impl__EdhocMessageBuffer__new: t_EdhocMessageBuffer =
  { f_content = Rust_primitives.Hax.repeat 0uy (sz 192); f_len = sz 0 } <: t_EdhocMessageBuffer

type t_EADItem = {
  f_label:u8;
  f_is_critical:bool;
  f_value:Core.Option.t_Option t_EdhocMessageBuffer
}

let encode_ead_item (ead_1_: t_EADItem)
    : Prims.Pure t_EdhocMessageBuffer
      (requires
        (~.ead_1_.f_is_critical || ead_1_.f_label <=. (255uy -! v_CBOR_NEG_INT_1BYTE_START <: u8)) &&
        (match ead_1_.f_value with
          | Core.Option.Option_Some ead_1_value -> ead_1_value.f_len <. sz 192
          | Core.Option.Option_None  -> true))
      (fun _ -> Prims.l_True) =
  let output:t_EdhocMessageBuffer = impl__EdhocMessageBuffer__new in
  let output:t_EdhocMessageBuffer =
    if ead_1_.f_is_critical
    then
      let output:t_EdhocMessageBuffer =
        {
          output with
          f_content
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output.f_content
            (sz 0)
            ((ead_1_.f_label +! v_CBOR_NEG_INT_1BYTE_START <: u8) -! 1uy <: u8)
        }
        <:
        t_EdhocMessageBuffer
      in
      output
    else
      let output:t_EdhocMessageBuffer =
        {
          output with
          f_content
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_usize output.f_content
            (sz 0)
            ead_1_.f_label
        }
        <:
        t_EdhocMessageBuffer
      in
      output
  in
  let output:t_EdhocMessageBuffer = { output with f_len = sz 1 } <: t_EdhocMessageBuffer in
  let output:t_EdhocMessageBuffer =
    match ead_1_.f_value with
    | Core.Option.Option_Some ead_1_value ->
      let output:t_EdhocMessageBuffer =
        {
          output with
          f_content
          =
          Rust_primitives.Hax.Monomorphized_update_at.update_at_range output.f_content
            ({
                Core.Ops.Range.f_start = sz 1;
                Core.Ops.Range.f_end = sz 1 +! ead_1_value.f_len <: usize
              }
              <:
              Core.Ops.Range.t_Range usize)
            (Core.Slice.impl__copy_from_slice (output.f_content.[ {
                      Core.Ops.Range.f_start = sz 1;
                      Core.Ops.Range.f_end = sz 1 +! ead_1_value.f_len <: usize
                    }
                    <:
                    Core.Ops.Range.t_Range usize ]
                  <:
                  t_Slice u8)
                (ead_1_value.f_content.[ { Core.Ops.Range.f_end = ead_1_value.f_len }
                    <:
                    Core.Ops.Range.t_RangeTo usize ]
                  <:
                  t_Slice u8)
              <:
              t_Slice u8)
        }
        <:
        t_EdhocMessageBuffer
      in
      let output:t_EdhocMessageBuffer =
        { output with f_len = output.f_len +! ead_1_value.f_len } <: t_EdhocMessageBuffer
      in
      output
    | _ -> output
  in
  output
