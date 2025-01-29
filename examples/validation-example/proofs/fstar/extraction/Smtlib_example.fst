module Smtlib_example
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

type t_Error =
  | Error_AuthenticationFailed : t_Error
  | Error_MessageTooOld : t_Error
  | Error_NotAcceptingNew : t_Error
  | Error_NotReadyToApply : t_Error
  | Error_UnexpectedVerifiedMsg : t_Error

let t_Error_cast_to_repr (x: t_Error) : isize =
  match x <: t_Error with
  | Error_AuthenticationFailed  -> mk_isize 0
  | Error_MessageTooOld  -> mk_isize 1
  | Error_NotAcceptingNew  -> mk_isize 3
  | Error_NotReadyToApply  -> mk_isize 6
  | Error_UnexpectedVerifiedMsg  -> mk_isize 10

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_1': Core.Fmt.t_Debug t_Error

let impl_1 = impl_1'


[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Cmp.t_PartialEq t_Error t_Error

let impl_3 = impl_3'

type t_ProtocolLibrary = {
  f_value:usize;
  f_last_changed:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_4': Core.Fmt.t_Debug t_ProtocolLibrary

let impl_4 = impl_4'

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: Core.Default.t_Default t_ProtocolLibrary =
  {
    f_default_pre = (fun (_: Prims.unit) -> true);
    f_default_post = (fun (_: Prims.unit) (out: t_ProtocolLibrary) -> true);
    f_default
    =
    fun (_: Prims.unit) ->
      { f_value = mk_usize 0; f_last_changed = mk_usize 0 } <: t_ProtocolLibrary
  }

type t_UnverifiedMessage = {
  f_sender:usize;
  f_authenticator:usize;
  f_timestamp:usize;
  f_value:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_5': Core.Fmt.t_Debug t_UnverifiedMessage

let impl_5 = impl_5'

type t_VerifiedMessage = {
  f_sender:usize;
  f_timestamp:usize;
  f_value:usize;
  f_state_last_changed:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_VerifiedMessage

let impl_7 = impl_7'


[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_9': Core.Cmp.t_PartialEq t_VerifiedMessage t_VerifiedMessage

let impl_9 = impl_9'

assume
val send': sender: usize -> timestamp: usize -> value: usize -> bool

let send = send'

assume
val impl__UnverifiedMessage__authenticate': self: t_UnverifiedMessage
  -> Prims.Pure bool
      Prims.l_True
      (ensures
        fun valid ->
          let valid:bool = valid in
          if valid then send self.f_sender self.f_timestamp self.f_value else true)

let impl__UnverifiedMessage__authenticate = impl__UnverifiedMessage__authenticate'

let impl__ProtocolLibrary__validate (self: t_ProtocolLibrary) (msg: t_UnverifiedMessage)
    : Core.Result.t_Result t_VerifiedMessage t_Error =
  if ~.(impl__UnverifiedMessage__authenticate msg <: bool)
  then
    Core.Result.Result_Err (Error_AuthenticationFailed <: t_Error)
    <:
    Core.Result.t_Result t_VerifiedMessage t_Error
  else
    if msg.f_timestamp <=. self.f_last_changed
    then
      Core.Result.Result_Err (Error_MessageTooOld <: t_Error)
      <:
      Core.Result.t_Result t_VerifiedMessage t_Error
    else
      Core.Result.Result_Ok
      ({
          f_sender = msg.f_sender;
          f_value = msg.f_value;
          f_timestamp = msg.f_timestamp;
          f_state_last_changed = self.f_last_changed
        }
        <:
        t_VerifiedMessage)
      <:
      Core.Result.t_Result t_VerifiedMessage t_Error

let impl__ProtocolLibrary__apply (self: t_ProtocolLibrary) (msg: t_VerifiedMessage)
    : Prims.Pure (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
      (requires
        Hax_lib.v_exists #(t_ProtocolLibrary & t_UnverifiedMessage)
          (fun temp_0_ ->
              let s, um:(t_ProtocolLibrary & t_UnverifiedMessage) = temp_0_ in
              (Core.Result.Result_Ok msg <: Core.Result.t_Result t_VerifiedMessage t_Error) =.
              (impl__ProtocolLibrary__validate s um
                <:
                Core.Result.t_Result t_VerifiedMessage t_Error)
              <:
              bool))
      (fun _ -> Prims.l_True) =
  if self.f_last_changed <>. msg.f_state_last_changed
  then
    self,
    (Core.Result.Result_Err (Error_UnexpectedVerifiedMsg <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
  else
    let _:Prims.unit = Hax_lib.v_assert (send msg.f_sender msg.f_timestamp msg.f_value <: bool) in
    let _:Prims.unit = Hax_lib.v_assert (msg.f_timestamp >. self.f_last_changed <: bool) in
    let self:t_ProtocolLibrary = { self with f_value = msg.f_value } <: t_ProtocolLibrary in
    let self:t_ProtocolLibrary =
      { self with f_last_changed = msg.f_timestamp } <: t_ProtocolLibrary
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    self, hax_temp_output <: (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
