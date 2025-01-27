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
val impl_2': Core.Fmt.t_Debug t_Error

let impl_2 = impl_2'

type t_State =
  | State_Idle : t_State
  | State_WaitToApply { f_verification_id:usize }: t_State

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_3': Core.Fmt.t_Debug t_State

let impl_3 = impl_3'

type t_ProtocolLibrary = {
  f_state:t_State;
  f_value:usize;
  f_last_changed:usize;
  f_msg_ctr:usize
}

assume
val send': sender: usize -> timestamp: usize -> value: usize -> bool

let send = send'

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
      {
        f_state = State_Idle <: t_State;
        f_value = mk_usize 0;
        f_last_changed = mk_usize 0;
        f_msg_ctr = mk_usize 0
      }
      <:
      t_ProtocolLibrary
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
  f_verification_id:usize
}

[@@ FStar.Tactics.Typeclasses.tcinstance]
assume
val impl_7': Core.Fmt.t_Debug t_VerifiedMessage

let impl_7 = impl_7'

let impl__ProtocolLibrary__apply (self: t_ProtocolLibrary) (msg: t_VerifiedMessage)
    : (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error) =
  match self.f_state <: t_State with
  | State_Idle  ->
    self,
    (Core.Result.Result_Err (Error_NotReadyToApply <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
  | State_WaitToApply { f_verification_id = verification_id } ->
    if verification_id <>. msg.f_verification_id
    then
      self,
      (Core.Result.Result_Err (Error_UnexpectedVerifiedMsg <: t_Error)
        <:
        Core.Result.t_Result Prims.unit t_Error)
      <:
      (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
    else
      let _:Prims.unit = (assert (send msg.f_sender msg.f_timestamp msg.f_value)) <: Prims.unit in
      let self:t_ProtocolLibrary = { self with f_value = msg.f_value } <: t_ProtocolLibrary in
      let self:t_ProtocolLibrary =
        { self with f_last_changed = msg.f_timestamp } <: t_ProtocolLibrary
      in
      let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
        Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
      in
      self, hax_temp_output <: (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)

let impl__ProtocolLibrary__abort (self: t_ProtocolLibrary)
    : (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error) =
  if
    ~.(match self.f_state <: t_State with
      | State_WaitToApply {  } -> true
      | _ -> false)
  then
    self,
    (Core.Result.Result_Err (Error_NotReadyToApply <: t_Error)
      <:
      Core.Result.t_Result Prims.unit t_Error)
    <:
    (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)
  else
    let self:t_ProtocolLibrary =
      { self with f_state = State_Idle <: t_State } <: t_ProtocolLibrary
    in
    let hax_temp_output:Core.Result.t_Result Prims.unit t_Error =
      Core.Result.Result_Ok (() <: Prims.unit) <: Core.Result.t_Result Prims.unit t_Error
    in
    self, hax_temp_output <: (t_ProtocolLibrary & Core.Result.t_Result Prims.unit t_Error)


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
    : (t_ProtocolLibrary & Core.Result.t_Result t_VerifiedMessage t_Error) =
  if
    ~.(match self.f_state <: t_State with
      | State_Idle  -> true
      | _ -> false)
  then
    self,
    (Core.Result.Result_Err (Error_NotAcceptingNew <: t_Error)
      <:
      Core.Result.t_Result t_VerifiedMessage t_Error)
    <:
    (t_ProtocolLibrary & Core.Result.t_Result t_VerifiedMessage t_Error)
  else
    if ~.(impl__UnverifiedMessage__authenticate msg <: bool)
    then
      self,
      (Core.Result.Result_Err (Error_AuthenticationFailed <: t_Error)
        <:
        Core.Result.t_Result t_VerifiedMessage t_Error)
      <:
      (t_ProtocolLibrary & Core.Result.t_Result t_VerifiedMessage t_Error)
    else
      if msg.f_timestamp <. self.f_last_changed
      then
        self,
        (Core.Result.Result_Err (Error_MessageTooOld <: t_Error)
          <:
          Core.Result.t_Result t_VerifiedMessage t_Error)
        <:
        (t_ProtocolLibrary & Core.Result.t_Result t_VerifiedMessage t_Error)
      else
        let verification_id:usize = self.f_msg_ctr in
        let self:t_ProtocolLibrary =
          { self with f_msg_ctr = self.f_msg_ctr +! mk_usize 1 } <: t_ProtocolLibrary
        in
        let self:t_ProtocolLibrary =
          {
            self with
            f_state
            =
            State_WaitToApply ({ f_verification_id = verification_id })
            <:
            t_State
          }
          <:
          t_ProtocolLibrary
        in
        let hax_temp_output:Core.Result.t_Result t_VerifiedMessage t_Error =
          Core.Result.Result_Ok
          ({
              f_sender = msg.f_sender;
              f_value = msg.f_value;
              f_timestamp = msg.f_timestamp;
              f_verification_id = verification_id
            }
            <:
            t_VerifiedMessage)
          <:
          Core.Result.t_Result t_VerifiedMessage t_Error
        in
        self, hax_temp_output
        <:
        (t_ProtocolLibrary & Core.Result.t_Result t_VerifiedMessage t_Error)
