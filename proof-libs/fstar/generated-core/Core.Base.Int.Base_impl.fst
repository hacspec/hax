module Core.Base.Int.Base_impl
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

open Core.Cmp

let impl_7__sub__double_mask (lhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos lhs with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS p ->
    Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO p
        <:
        Core.Base.Int.t_Positive)

let impl_7__sub__succ_double_mask (lhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos lhs with
  | Core.Base.Int.POS_ZERO  ->
    Core.Base.Int.Base_spec.impl_4__to_int Core.Base.Int.Base_spec.impl_8__xH
  | Core.Base.Int.POS_POS p ->
    Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xI p
        <:
        Core.Base.Int.t_Positive)

let impl_8__double (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS p ->
    Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO p
        <:
        Core.Base.Int.t_Positive)

let impl_8__half (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS n ->
    match Core.Base.Int.Base_spec.impl_8__match_positive n with
    | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
    | Core.Base.Int.POSITIVE_XO p -> Core.Base.Int.Base_spec.impl_4__to_int p
    | Core.Base.Int.POSITIVE_XI p -> Core.Base.Int.Base_spec.impl_4__to_int p

let impl_8__succ_double (self: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_8__xH
  | Core.Base.Int.POS_POS p -> Core.Base.Int.Base_spec.impl_8__xI p

let rec impl__cmp__cmp_binary_cont (x y: Core.Base.Int.t_Positive) (r: Core.Cmp.t_Ordering)
    : Core.Cmp.t_Ordering =
  match Core.Base.Int.Base_spec.impl_8__match_positive x with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive y with
      | Core.Base.Int.POSITIVE_XH  -> r
      | Core.Base.Int.POSITIVE_XO q
      | Core.Base.Int.POSITIVE_XI q -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive y with
      | Core.Base.Int.POSITIVE_XH  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
      | Core.Base.Int.POSITIVE_XO q -> impl__cmp__cmp_binary_cont p q r
      | Core.Base.Int.POSITIVE_XI q ->
        impl__cmp__cmp_binary_cont p q (Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive y with
    | Core.Base.Int.POSITIVE_XH  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
    | Core.Base.Int.POSITIVE_XO q ->
      impl__cmp__cmp_binary_cont p q (Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
    | Core.Base.Int.POSITIVE_XI q -> impl__cmp__cmp_binary_cont p q r

let impl__cmp (lhs rhs: Core.Base.Int.t_Positive) : Core.Cmp.t_Ordering =
  impl__cmp__cmp_binary_cont lhs rhs (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: Core.Cmp.t_PartialEq Core.Base.Int.t_Positive Core.Base.Int.t_Positive =
  {
    f_eq_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_eq_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_eq
    =
    (fun x y -> x = y)
    // (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
    //     (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
    //             #FStar.Tactics.Typeclasses.solve
    //             self
    //           <:
    //           Core.Base.Int.t_Positive)
    //         (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
    //           <:
    //           Core.Base.Int.t_Positive)
    //       <:
    //       Core.Cmp.t_Ordering) =.
    //     (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering))
  ;
    f_ne_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_ne_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_ne
    =
    fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
      ~.((impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_Positive)
            (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_Positive)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
        <:
        bool)
  }

let impl_2__cmp (lhs rhs: Core.Base.Int.t_HaxInt) : Core.Cmp.t_Ordering =
  match Core.Base.Int.Base_spec.impl_9__match_pos lhs with
  | Core.Base.Int.POS_ZERO  ->
    (match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
      | Core.Base.Int.POS_ZERO  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
      | Core.Base.Int.POS_POS q -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
    | Core.Base.Int.POS_POS q -> impl__cmp p q

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: Core.Cmp.t_PartialEq Core.Base.Int.t_HaxInt Core.Base.Int.t_HaxInt =
  {
    f_eq_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_eq_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_eq
    =
    (fun x y -> x = y)
    // (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
    //     (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
    //             #FStar.Tactics.Typeclasses.solve
    //             self
    //           <:
    //           Core.Base.Int.t_HaxInt)
    //         (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
    //           <:
    //           Core.Base.Int.t_HaxInt)
    //       <:
    //       Core.Cmp.t_Ordering) =.
    //     (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering))
  ;
    f_ne_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_ne_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_ne
    =
    fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
      ~.((impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Cmp.t_Ordering) =.
        (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)
        <:
        bool)
  }

let rec impl_4__succ (self: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  ->
    Core.Base.Int.Base_spec.impl_8__xO Core.Base.Int.Base_spec.impl_8__xH
  | Core.Base.Int.POSITIVE_XO q -> Core.Base.Int.Base_spec.impl_8__xI q
  | Core.Base.Int.POSITIVE_XI q ->
    Core.Base.Int.Base_spec.impl_8__xO (impl_4__succ q <: Core.Base.Int.t_Positive)

let rec impl_7__sub__pred_double (lhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_8__xH
  | Core.Base.Int.POSITIVE_XO p ->
    Core.Base.Int.Base_spec.impl_8__xI (impl_7__sub__pred_double p <: Core.Base.Int.t_Positive)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Base.Int.Base_spec.impl_8__xI (Core.Base.Int.Base_spec.impl_8__xO p
        <:
        Core.Base.Int.t_Positive)

let impl_7__sub__double_pred_mask (lhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POSITIVE_XO p ->
    Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO (impl_7__sub__pred_double
              p
            <:
            Core.Base.Int.t_Positive)
        <:
        Core.Base.Int.t_Positive)
  | Core.Base.Int.POSITIVE_XI p ->
    Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO (Core.Base.Int.Base_spec.impl_8__xO
              p
            <:
            Core.Base.Int.t_Positive)
        <:
        Core.Base.Int.t_Positive)

let rec impl_9__power_of_two (self: Core.Base.Int.t_Unary) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_6__match_unary self with
  | Core.Base.Int.UNARY_ZERO  -> Core.Base.Int.Base_spec.impl_8__xH
  | Core.Base.Int.UNARY_SUCC x ->
    Core.Base.Int.Base_spec.impl_8__xO (impl_9__power_of_two x <: Core.Base.Int.t_Positive)

let rec impl_12__shl__shl_helper (rhs: Core.Base.Int.t_Unary) (lhs: Core.Base.Int.t_HaxInt)
    : Core.Base.Int.t_HaxInt =
  if
    Core.Base.Int.Base_spec.impl_9__is_zero (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        Core.Base.Int.t_HaxInt)
  then lhs
  else
    match Core.Base.Int.Base_spec.impl_6__match_unary rhs with
    | Core.Base.Int.UNARY_ZERO  -> lhs
    | Core.Base.Int.UNARY_SUCC n ->
      impl_12__shl__shl_helper n (impl_8__double lhs <: Core.Base.Int.t_HaxInt)

let impl_12__shl (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  impl_12__shl__shl_helper (Core.Base.Int.Base_spec.impl_5__from_int rhs <: Core.Base.Int.t_Unary)
    self

let rec impl_13__shr__shr_helper (rhs: Core.Base.Int.t_Unary) (lhs: Core.Base.Int.t_HaxInt)
    : Core.Base.Int.t_HaxInt =
  if
    Core.Base.Int.Base_spec.impl_9__is_zero (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        Core.Base.Int.t_HaxInt)
  then lhs
  else
    match Core.Base.Int.Base_spec.impl_6__match_unary rhs with
    | Core.Base.Int.UNARY_ZERO  -> lhs
    | Core.Base.Int.UNARY_SUCC n ->
      impl_13__shr__shr_helper n (impl_8__half lhs <: Core.Base.Int.t_HaxInt)

let impl_13__shr (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  impl_13__shr__shr_helper (Core.Base.Int.Base_spec.impl_5__from_int rhs <: Core.Base.Int.t_Unary)
    self

let rec impl_14__bitxor__bitxor_binary (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
      | Core.Base.Int.POSITIVE_XO q ->
        Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xI q
            <:
            Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO q
            <:
            Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xI p
            <:
            Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XO q ->
        impl_8__double (impl_14__bitxor__bitxor_binary p q <: Core.Base.Int.t_HaxInt)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double (impl_14__bitxor__bitxor_binary p
                  q
                <:
                Core.Base.Int.t_HaxInt)
            <:
            Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  ->
      Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO p
          <:
          Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XO q ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double (impl_14__bitxor__bitxor_binary p
                q
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XI q ->
      impl_8__double (impl_14__bitxor__bitxor_binary p q <: Core.Base.Int.t_HaxInt)

let impl_14__bitxor (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> rhs
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_4__to_int p
    | Core.Base.Int.POS_POS q -> impl_14__bitxor__bitxor_binary p q

let rec impl_15__bitand__bitand_binary (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XO q -> Core.Base.Int.Base_spec.impl_9__ZERO
      | Core.Base.Int.POSITIVE_XI _
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ONE)
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
      | Core.Base.Int.POSITIVE_XO q
      | Core.Base.Int.POSITIVE_XI q ->
        impl_8__double (impl_15__bitand__bitand_binary p q <: Core.Base.Int.t_HaxInt))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ONE
    | Core.Base.Int.POSITIVE_XO q ->
      impl_8__double (impl_15__bitand__bitand_binary p q <: Core.Base.Int.t_HaxInt)
    | Core.Base.Int.POSITIVE_XI q ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double (impl_15__bitand__bitand_binary p
                q
              <:
              Core.Base.Int.t_HaxInt)
          <:
          Core.Base.Int.t_Positive)

let impl_15__bitand (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
    | Core.Base.Int.POS_POS q -> impl_15__bitand__bitand_binary p q

let rec impl_16__bitor__bitor_binary (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XO q -> Core.Base.Int.Base_spec.impl_8__xI q
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_8__xH
      | Core.Base.Int.POSITIVE_XI q -> Core.Base.Int.Base_spec.impl_8__xI q)
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_8__xI p
      | Core.Base.Int.POSITIVE_XO q ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_16__bitor__bitor_binary p q
            <:
            Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_8__xI (impl_16__bitor__bitor_binary p q
            <:
            Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_8__xI p
    | Core.Base.Int.POSITIVE_XO q
    | Core.Base.Int.POSITIVE_XI q ->
      Core.Base.Int.Base_spec.impl_8__xI (impl_16__bitor__bitor_binary p q
          <:
          Core.Base.Int.t_Positive)

let impl_16__bitor (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> rhs
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_4__to_int p
    | Core.Base.Int.POS_POS q ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_16__bitor__bitor_binary p q
          <:
          Core.Base.Int.t_Positive)

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_17: Core.Cmp.t_PartialOrd Core.Base.Int.t_Positive Core.Base.Int.t_Positive =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: Core.Base.Int.t_Positive)
        (other: Core.Base.Int.t_Positive)
        (out: Core.Option.t_Option Core.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
        Core.Option.Option_Some
        (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_Positive)
            (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_Positive))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_lt_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_lt
    =
    (fun self other -> self < other)
    // (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
    //     match
    //       Core.Option.Option_Some
    //       (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
    //               #FStar.Tactics.Typeclasses.solve
    //               self
    //             <:
    //             Core.Base.Int.t_Positive)
    //           (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
    //             <:
    //             Core.Base.Int.t_Positive))
    //       <:
    //       Core.Option.t_Option Core.Cmp.t_Ordering
    //     with
    //     | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
    //     | _ -> false)
  ;
    f_le_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_le_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_le
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
        match
          Core.Option.Option_Some
          (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
                  #FStar.Tactics.Typeclasses.solve
                  self
                <:
                Core.Base.Int.t_Positive)
              (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
                <:
                Core.Base.Int.t_Positive))
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_gt_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_gt
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
        match
          Core.Option.Option_Some
          (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
                  #FStar.Tactics.Typeclasses.solve
                  self
                <:
                Core.Base.Int.t_Positive)
              (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
                <:
                Core.Base.Int.t_Positive))
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) -> true);
    f_ge_post
    =
    (fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) (out: bool) -> true);
    f_ge
    =
    fun (self: Core.Base.Int.t_Positive) (other: Core.Base.Int.t_Positive) ->
      match
        Core.Option.Option_Some
        (impl__cmp (Core.Clone.f_clone #Core.Base.Int.t_Positive
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_Positive)
            (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_Positive))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_18: Core.Cmp.t_PartialOrd Core.Base.Int.t_HaxInt Core.Base.Int.t_HaxInt =
  {
    _super_9014672428308350468 = FStar.Tactics.Typeclasses.solve;
    f_partial_cmp_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_partial_cmp_post
    =
    (fun
        (self: Core.Base.Int.t_HaxInt)
        (other: Core.Base.Int.t_HaxInt)
        (out: Core.Option.t_Option Core.Cmp.t_Ordering)
        ->
        true);
    f_partial_cmp
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
        Core.Option.Option_Some
        (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering);
    f_lt_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_lt_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_lt
    = (fun self other -> self < other)
    // (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
    //     match
    //       Core.Option.Option_Some
    //       (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
    //               #FStar.Tactics.Typeclasses.solve
    //               self
    //             <:
    //             Core.Base.Int.t_HaxInt)
    //           (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
    //             <:
    //             Core.Base.Int.t_HaxInt))
    //       <:
    //       Core.Option.t_Option Core.Cmp.t_Ordering
    //     with
    //     | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
    //     | _ -> false)
  ;
    f_le_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_le_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_le
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
        match
          Core.Option.Option_Some
          (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
                  #FStar.Tactics.Typeclasses.solve
                  self
                <:
                Core.Base.Int.t_HaxInt)
              (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
                <:
                Core.Base.Int.t_HaxInt))
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
        | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
        | _ -> false);
    f_gt_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_gt_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_gt
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
        match
          Core.Option.Option_Some
          (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
                  #FStar.Tactics.Typeclasses.solve
                  self
                <:
                Core.Base.Int.t_HaxInt)
              (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
                <:
                Core.Base.Int.t_HaxInt))
          <:
          Core.Option.t_Option Core.Cmp.t_Ordering
        with
        | Core.Option.Option_Some (Core.Cmp.Ordering_Greater ) -> true
        | _ -> false);
    f_ge_pre = (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) -> true);
    f_ge_post
    =
    (fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) (out: bool) -> true);
    f_ge
    =
    fun (self: Core.Base.Int.t_HaxInt) (other: Core.Base.Int.t_HaxInt) ->
      match
        Core.Option.Option_Some
        (impl_2__cmp (Core.Clone.f_clone #Core.Base.Int.t_HaxInt
                #FStar.Tactics.Typeclasses.solve
                self
              <:
              Core.Base.Int.t_HaxInt)
            (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve other
              <:
              Core.Base.Int.t_HaxInt))
        <:
        Core.Option.t_Option Core.Cmp.t_Ordering
      with
      | Core.Option.Option_Some (Core.Cmp.Ordering_Greater )
      | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
      | _ -> false
  }

let rec impl_4__add (self rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_8__xO Core.Base.Int.Base_spec.impl_8__xH
      | Core.Base.Int.POSITIVE_XO q -> Core.Base.Int.Base_spec.impl_8__xI q
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_4__succ q <: Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_8__xI p
      | Core.Base.Int.POSITIVE_XO q ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_4__add p q <: Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_8__xI (impl_4__add p q <: Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  ->
      Core.Base.Int.Base_spec.impl_8__xO (impl_4__succ p <: Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XO q ->
      Core.Base.Int.Base_spec.impl_8__xI (impl_4__add p q <: Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XI q ->
      Core.Base.Int.Base_spec.impl_8__xO (impl_4__add__add_carry p q <: Core.Base.Int.t_Positive)

and impl_4__add__add_carry (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_8__xI Core.Base.Int.Base_spec.impl_8__xH
      | Core.Base.Int.POSITIVE_XO q ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_4__succ q <: Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_8__xI (impl_4__succ q <: Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_4__succ p <: Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XO q ->
        Core.Base.Int.Base_spec.impl_8__xI (impl_4__add p q <: Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_8__xO (impl_4__add__add_carry p q <: Core.Base.Int.t_Positive))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  ->
      Core.Base.Int.Base_spec.impl_8__xI (impl_4__succ p <: Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XO q ->
      Core.Base.Int.Base_spec.impl_8__xO (impl_4__add__add_carry p q <: Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XI q ->
      Core.Base.Int.Base_spec.impl_8__xI (impl_4__add__add_carry p q <: Core.Base.Int.t_Positive)

let impl_6__add (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> rhs
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_4__to_int p
    | Core.Base.Int.POS_POS q ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_4__add p q <: Core.Base.Int.t_Positive)

let rec impl_7__sub__sub_binary (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_4__to_int (impl_7__sub__pred_double p
            <:
            Core.Base.Int.t_Positive)
      | Core.Base.Int.POSITIVE_XO q ->
        impl_7__sub__double_mask (impl_7__sub__sub_binary p q <: Core.Base.Int.t_HaxInt)
      | Core.Base.Int.POSITIVE_XI q ->
        impl_7__sub__succ_double_mask (impl_7__sub__sub_carry p q <: Core.Base.Int.t_HaxInt))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  ->
      Core.Base.Int.Base_spec.impl_4__to_int (Core.Base.Int.Base_spec.impl_8__xO p
          <:
          Core.Base.Int.t_Positive)
    | Core.Base.Int.POSITIVE_XO q ->
      impl_7__sub__succ_double_mask (impl_7__sub__sub_binary p q <: Core.Base.Int.t_HaxInt)
    | Core.Base.Int.POSITIVE_XI q ->
      impl_7__sub__double_mask (impl_7__sub__sub_binary p q <: Core.Base.Int.t_HaxInt)

and impl_7__sub__sub_carry (lhs rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_8__match_positive lhs with
  | Core.Base.Int.POSITIVE_XH  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POSITIVE_XO p ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
      | Core.Base.Int.POSITIVE_XH  -> impl_7__sub__double_pred_mask p
      | Core.Base.Int.POSITIVE_XO q ->
        impl_7__sub__succ_double_mask (impl_7__sub__sub_carry p q <: Core.Base.Int.t_HaxInt)
      | Core.Base.Int.POSITIVE_XI q ->
        impl_7__sub__double_mask (impl_7__sub__sub_carry p q <: Core.Base.Int.t_HaxInt))
  | Core.Base.Int.POSITIVE_XI p ->
    match Core.Base.Int.Base_spec.impl_8__match_positive rhs with
    | Core.Base.Int.POSITIVE_XH  ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_7__sub__pred_double p <: Core.Base.Int.t_Positive
        )
    | Core.Base.Int.POSITIVE_XO q ->
      impl_7__sub__double_mask (impl_7__sub__sub_binary p q <: Core.Base.Int.t_HaxInt)
    | Core.Base.Int.POSITIVE_XI q ->
      impl_7__sub__succ_double_mask (impl_7__sub__sub_carry p q <: Core.Base.Int.t_HaxInt)

let impl_7__sub (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_4__to_int p
    | Core.Base.Int.POS_POS q -> impl_7__sub__sub_binary p q

let rec impl_5__mul (self rhs: Core.Base.Int.t_Positive) : Core.Base.Int.t_Positive =
  match Core.Base.Int.Base_spec.impl_8__match_positive self with
  | Core.Base.Int.POSITIVE_XH  -> rhs
  | Core.Base.Int.POSITIVE_XO p ->
    Core.Base.Int.Base_spec.impl_8__xO (impl_5__mul p rhs <: Core.Base.Int.t_Positive)
  | Core.Base.Int.POSITIVE_XI p ->
    impl_4__add (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve rhs
        <:
        Core.Base.Int.t_Positive)
      (Core.Base.Int.Base_spec.impl_8__xO (impl_5__mul p rhs <: Core.Base.Int.t_Positive)
        <:
        Core.Base.Int.t_Positive)

let impl_11__mul (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  match Core.Base.Int.Base_spec.impl_9__match_pos self with
  | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos rhs with
    | Core.Base.Int.POS_ZERO  -> Core.Base.Int.Base_spec.impl_9__ZERO
    | Core.Base.Int.POS_POS q ->
      Core.Base.Int.Base_spec.impl_4__to_int (impl_5__mul p q <: Core.Base.Int.t_Positive)

let rec impl_10__divmod__divmod_binary (a b: Core.Base.Int.t_Positive)
    : (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) =
  match Core.Base.Int.Base_spec.impl_8__match_positive a with
  | Core.Base.Int.POSITIVE_XH  ->
    (match Core.Base.Int.Base_spec.impl_8__match_positive b with
      | Core.Base.Int.POSITIVE_XH  ->
        Core.Base.Int.Base_spec.impl_9__ONE, Core.Base.Int.Base_spec.impl_9__ZERO
        <:
        (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
      | Core.Base.Int.POSITIVE_XO q
      | Core.Base.Int.POSITIVE_XI q ->
        Core.Base.Int.Base_spec.impl_9__ZERO, Core.Base.Int.Base_spec.impl_9__ONE
        <:
        (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt))
  | Core.Base.Int.POSITIVE_XO a___ ->
    let q, r:(Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) =
      impl_10__divmod__divmod_binary a___
        (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Int.t_Positive)
    in
    let r___:Core.Base.Int.t_HaxInt = impl_8__double r in
    if
      (Core.Base.Int.Base_spec.impl_4__to_int (Core.Clone.f_clone #Core.Base.Int.t_Positive
              #FStar.Tactics.Typeclasses.solve
              b
            <:
            Core.Base.Int.t_Positive)
        <:
        Core.Base.Int.t_HaxInt) <=.
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve r___
        <:
        Core.Base.Int.t_HaxInt)
    then
      Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double q <: Core.Base.Int.t_Positive),
      impl_7__sub r___ (Core.Base.Int.Base_spec.impl_4__to_int b <: Core.Base.Int.t_HaxInt)
      <:
      (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
    else impl_8__double q, r___ <: (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
  | Core.Base.Int.POSITIVE_XI a___ ->
    let q, r:(Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) =
      impl_10__divmod__divmod_binary a___
        (Core.Clone.f_clone #Core.Base.Int.t_Positive #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Int.t_Positive)
    in
    let r___:Core.Base.Int.t_HaxInt =
      Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double r <: Core.Base.Int.t_Positive)
    in
    if
      (Core.Base.Int.Base_spec.impl_4__to_int (Core.Clone.f_clone #Core.Base.Int.t_Positive
              #FStar.Tactics.Typeclasses.solve
              b
            <:
            Core.Base.Int.t_Positive)
        <:
        Core.Base.Int.t_HaxInt) <=.
      (Core.Clone.f_clone #Core.Base.Int.t_HaxInt #FStar.Tactics.Typeclasses.solve r___
        <:
        Core.Base.Int.t_HaxInt)
    then
      Core.Base.Int.Base_spec.impl_4__to_int (impl_8__succ_double q <: Core.Base.Int.t_Positive),
      impl_7__sub r___ (Core.Base.Int.Base_spec.impl_4__to_int b <: Core.Base.Int.t_HaxInt)
      <:
      (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
    else impl_8__double q, r___ <: (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)

let impl_10__divmod (a b: Core.Base.Int.t_HaxInt)
    : (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) =
  match Core.Base.Int.Base_spec.impl_9__match_pos a with
  | Core.Base.Int.POS_ZERO  ->
    Core.Base.Int.Base_spec.impl_9__ZERO, Core.Base.Int.Base_spec.impl_9__ZERO
    <:
    (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
  | Core.Base.Int.POS_POS p ->
    match Core.Base.Int.Base_spec.impl_9__match_pos b with
    | Core.Base.Int.POS_ZERO  ->
      Core.Base.Int.Base_spec.impl_9__ZERO, Core.Base.Int.Base_spec.impl_4__to_int p
      <:
      (Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt)
    | Core.Base.Int.POS_POS q -> impl_10__divmod__divmod_binary p q

let impl_10__div (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  let q, r:(Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) = impl_10__divmod self rhs in
  q

let impl_10__rem (self rhs: Core.Base.Int.t_HaxInt) : Core.Base.Int.t_HaxInt =
  if rhs = 0
  then self
  else self % rhs
  // let q, r:(Core.Base.Int.t_HaxInt & Core.Base.Int.t_HaxInt) = impl_10__divmod self rhs in
  // r

///////////////////////////

let rec lt_is_lt_hax (x y : Core.Base.Int.t_HaxInt) : Lemma (requires x < y) (ensures x <. y) [SMTPat (x <. y)] = ()
let rec lt_hax_is_lt (x y : Core.Base.Int.t_HaxInt) : Lemma (requires x <. y) (ensures x < y) [SMTPat (x <. y)] = ()

let eq_is_eq_hax (x y : Core.Base.Int.t_HaxInt) : Lemma (requires x = y) (ensures x =. y) [SMTPat (x =. y)] = ()
let eq_hax_is_eq (x y : Core.Base.Int.t_HaxInt) : Lemma (requires x =. y) (ensures x = y) [SMTPat (x =. y)] = ()
