module Core.Base.Pos
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let haxint_double (s: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos s with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO p
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_shr__half (s: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos s with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS n ->
    match Core.Base.Spec.Binary.Positive.match_positive n with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
      Core.Base.Spec.Binary.Positive.positive_to_int p
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
      Core.Base.Spec.Binary.Positive.positive_to_int p

let haxint_sub__double_mask (lhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO p
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_sub__succ_double_mask (lhs: Core.Base.Spec.Haxint.t_HaxInt)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Binary.Positive.positive_to_int Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xI p
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_succ_double (s: Core.Base.Spec.Haxint.t_HaxInt)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Pos.match_pos s with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Binary.Pos.POS_POS p -> Core.Base.Spec.Binary.Positive.xI p

let rec bitand_binary (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI _
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ONE)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        haxint_double (bitand_binary p q <: Core.Base.Spec.Haxint.t_HaxInt))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ONE
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      haxint_double (bitand_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double (bitand_binary p q
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let rec bitor_binary (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q -> Core.Base.Spec.Binary.Positive.xI q
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Binary.Positive.xH
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q -> Core.Base.Spec.Binary.Positive.xI q)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Binary.Positive.xI p
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Binary.Positive.xO (bitor_binary p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.xI (bitor_binary p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Binary.Positive.xI p
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      Core.Base.Spec.Binary.Positive.xI (bitor_binary p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_bitand (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
    | Core.Base.Spec.Binary.Pos.POS_POS q -> bitand_binary p q

let haxint_bitor (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> rhs
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.positive_to_int p
    | Core.Base.Spec.Binary.Pos.POS_POS q ->
      Core.Base.Spec.Binary.Positive.positive_to_int (bitor_binary p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let rec haxint_bitxor__bitxor_binary (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xI q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xI p
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        haxint_double (haxint_bitxor__bitxor_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double (haxint_bitxor__bitxor_binary
                  p
                  q
                <:
                Core.Base.Spec.Haxint.t_HaxInt)
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO p
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double (haxint_bitxor__bitxor_binary
                p
                q
              <:
              Core.Base.Spec.Haxint.t_HaxInt)
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      haxint_double (haxint_bitxor__bitxor_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)

let haxint_bitxor (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> rhs
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.positive_to_int p
    | Core.Base.Spec.Binary.Pos.POS_POS q -> haxint_bitxor__bitxor_binary p q

let haxint_cmp (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Cmp.t_Ordering =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    (match Core.Base.Spec.Binary.Pos.match_pos rhs with
      | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
      | Core.Base.Spec.Binary.Pos.POS_POS q -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
    | Core.Base.Spec.Binary.Pos.POS_POS q -> Core.Base.Binary.positive_cmp p q

let haxint_le (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : bool =
  match
    Core.Option.Option_Some (haxint_cmp lhs rhs) <: Core.Option.t_Option Core.Cmp.t_Ordering
  with
  | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
  | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
  | _ -> false

let haxint_lt (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : bool =
  match
    Core.Option.Option_Some (haxint_cmp lhs rhs) <: Core.Option.t_Option Core.Cmp.t_Ordering
  with
  | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
  | _ -> false

let rec haxint_shl__shl_helper (rhs: Core.Base.Spec.Unary.t_Unary) (lhs: Core.Base.Spec.Haxint.t_HaxInt)
    : Core.Base.Spec.Haxint.t_HaxInt =
  if
    Core.Base.Spec.Haxint.is_zero (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  then lhs
  else
    match Core.Base.Spec.Unary.match_unary rhs with
    | Core.Base.Spec.Unary.UNARY_ZERO  -> lhs
    | Core.Base.Spec.Unary.UNARY_SUCC n ->
      haxint_shl__shl_helper n (haxint_double lhs <: Core.Base.Spec.Haxint.t_HaxInt)

let haxint_shl (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  haxint_shl__shl_helper (Core.Base.Spec.Unary.unary_from_int rhs <: Core.Base.Spec.Unary.t_Unary)
    lhs

let rec haxint_shr__shr_helper (rhs: Core.Base.Spec.Unary.t_Unary) (lhs: Core.Base.Spec.Haxint.t_HaxInt)
    : Core.Base.Spec.Haxint.t_HaxInt =
  if
    Core.Base.Spec.Haxint.is_zero (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt
          #FStar.Tactics.Typeclasses.solve
          lhs
        <:
        Core.Base.Spec.Haxint.t_HaxInt)
  then lhs
  else
    match Core.Base.Spec.Unary.match_unary rhs with
    | Core.Base.Spec.Unary.UNARY_ZERO  -> lhs
    | Core.Base.Spec.Unary.UNARY_SUCC n ->
      haxint_shr__shr_helper n (haxint_shr__half lhs <: Core.Base.Spec.Haxint.t_HaxInt)

let haxint_shr (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  haxint_shr__shr_helper (Core.Base.Spec.Unary.unary_from_int rhs <: Core.Base.Spec.Unary.t_Unary)
    lhs

let haxint_sub__double_pred_mask (lhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO (Core.Base.Binary.positive_pred_double
              p
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO (Core.Base.Spec.Binary.Positive.xO
              p
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let rec power_of_two (s: Core.Base.Spec.Unary.t_Unary) : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Unary.match_unary s with
  | Core.Base.Spec.Unary.UNARY_ZERO  -> Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Unary.UNARY_SUCC x ->
    Core.Base.Spec.Binary.Positive.xO (power_of_two x <: Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_add (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> rhs
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.positive_to_int p
    | Core.Base.Spec.Binary.Pos.POS_POS q ->
      Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Binary.positive_add p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_sub (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.positive_to_int p
    | Core.Base.Spec.Binary.Pos.POS_POS q -> haxint_sub__sub_binary p q

let rec haxint_divmod__divmod_binary (a b: Core.Base.Spec.Binary.Positive.t_Positive)
    : (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
  match Core.Base.Spec.Binary.Positive.match_positive a with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive b with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Haxint.v_HaxInt_ONE, Core.Base.Spec.Haxint.v_HaxInt_ZERO
        <:
        (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Haxint.v_HaxInt_ZERO, Core.Base.Spec.Haxint.v_HaxInt_ONE
        <:
        (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO a___ ->
    let q, r:(Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
      haxint_divmod__divmod_binary a___
        (Core.Clone.f_clone #Core.Base.Spec.Binary.Positive.t_Positive
            #FStar.Tactics.Typeclasses.solve
            b
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    in
    let r___:Core.Base.Spec.Haxint.t_HaxInt = haxint_double r in
    if
      haxint_le (Core.Base.Spec.Binary.Positive.positive_to_int (Core.Clone.f_clone #Core.Base.Spec.Binary.Positive.t_Positive
                #FStar.Tactics.Typeclasses.solve
                b
              <:
              Core.Base.Spec.Binary.Positive.t_Positive)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve r___
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    then
      Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive),
      haxint_sub r___
        (Core.Base.Spec.Binary.Positive.positive_to_int b <: Core.Base.Spec.Haxint.t_HaxInt)
      <:
      (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
    else haxint_double q, r___ <: (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI a___ ->
    let q, r:(Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
      haxint_divmod__divmod_binary a___
        (Core.Clone.f_clone #Core.Base.Spec.Binary.Positive.t_Positive
            #FStar.Tactics.Typeclasses.solve
            b
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    in
    let r___:Core.Base.Spec.Haxint.t_HaxInt =
      Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double r
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    in
    if
      haxint_le (Core.Base.Spec.Binary.Positive.positive_to_int (Core.Clone.f_clone #Core.Base.Spec.Binary.Positive.t_Positive
                #FStar.Tactics.Typeclasses.solve
                b
              <:
              Core.Base.Spec.Binary.Positive.t_Positive)
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
        (Core.Clone.f_clone #Core.Base.Spec.Haxint.t_HaxInt #FStar.Tactics.Typeclasses.solve r___
          <:
          Core.Base.Spec.Haxint.t_HaxInt)
    then
      Core.Base.Spec.Binary.Positive.positive_to_int (haxint_succ_double q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive),
      haxint_sub r___
        (Core.Base.Spec.Binary.Positive.positive_to_int b <: Core.Base.Spec.Haxint.t_HaxInt)
      <:
      (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
    else haxint_double q, r___ <: (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)

let haxint_divmod (a b: Core.Base.Spec.Haxint.t_HaxInt)
    : (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
  match Core.Base.Spec.Binary.Pos.match_pos a with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Haxint.v_HaxInt_ZERO, Core.Base.Spec.Haxint.v_HaxInt_ZERO
    <:
    (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos b with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
      Core.Base.Spec.Haxint.v_HaxInt_ZERO, Core.Base.Spec.Binary.Positive.positive_to_int p
      <:
      (Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt)
    | Core.Base.Spec.Binary.Pos.POS_POS q -> haxint_divmod__divmod_binary p q

let haxint_div (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  let q, _:(Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
    haxint_divmod lhs rhs
  in
  q

let haxint_mul (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Pos.match_pos lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match Core.Base.Spec.Binary.Pos.match_pos rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
    | Core.Base.Spec.Binary.Pos.POS_POS q ->
      Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Binary.positive_mul p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let haxint_rem (lhs rhs: Core.Base.Spec.Haxint.t_HaxInt) : Core.Base.Spec.Haxint.t_HaxInt =
  let _, r:(Core.Base.Spec.Haxint.t_HaxInt & Core.Base.Spec.Haxint.t_HaxInt) =
    haxint_divmod lhs rhs
  in
  r

let rec haxint_sub__sub_binary (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Binary.positive_pred_double p
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        haxint_sub__double_mask (haxint_sub__sub_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        haxint_sub__succ_double_mask (haxint_sub__sub_carry p q <: Core.Base.Spec.Haxint.t_HaxInt))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Spec.Binary.Positive.xO p
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      haxint_sub__succ_double_mask (haxint_sub__sub_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      haxint_sub__double_mask (haxint_sub__sub_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)

and haxint_sub__sub_carry (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Haxint.t_HaxInt =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Haxint.v_HaxInt_ZERO
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> haxint_sub__double_pred_mask p
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        haxint_sub__succ_double_mask (haxint_sub__sub_carry p q <: Core.Base.Spec.Haxint.t_HaxInt)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        haxint_sub__double_mask (haxint_sub__sub_carry p q <: Core.Base.Spec.Haxint.t_HaxInt))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Positive.positive_to_int (Core.Base.Binary.positive_pred_double p
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      haxint_sub__double_mask (haxint_sub__sub_binary p q <: Core.Base.Spec.Haxint.t_HaxInt)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      haxint_sub__succ_double_mask (haxint_sub__sub_carry p q <: Core.Base.Spec.Haxint.t_HaxInt)
