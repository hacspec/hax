module Core.Base.Z
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let z_add__z_double (s: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match s with
  | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_POS p ->
    Core.Base.Spec.Z.Z_POS (Core.Base.Spec.Binary.Positive.xO p) <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_NEG p ->
    Core.Base.Spec.Z.Z_NEG (Core.Base.Spec.Binary.Positive.xO p) <: Core.Base.Spec.Z.t_Z

let z_bitor__haxint_ldiff__n_double (x: Core.Base.Spec.Binary.Pos.t_POS)
    : Core.Base.Spec.Binary.Pos.t_POS =
  match x with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Spec.Binary.Positive.xO p)
    <:
    Core.Base.Spec.Binary.Pos.t_POS

let z_bitor__haxint_ldiff__n_succ_double (x: Core.Base.Spec.Binary.Pos.t_POS)
    : Core.Base.Spec.Binary.Pos.t_POS =
  match x with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Binary.Pos.POS_POS Core.Base.Spec.Binary.Positive.xH
    <:
    Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Spec.Binary.Positive.xI p)
    <:
    Core.Base.Spec.Binary.Pos.t_POS

let z_bitor__n_succ (x: Core.Base.Spec.Binary.Pos.t_POS) : Core.Base.Spec.Binary.Positive.t_Positive =
  match x with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  -> Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    Core.Base.Spec.Binary.Positive.positive_from_int (Core.Base.Spec.Haxint.succ (Core.Base.Spec.Binary.Positive.positive_to_int
              p
            <:
            Core.Base.Spec.Haxint.t_HaxInt)
        <:
        Core.Base.Spec.Haxint.t_HaxInt)

let z_neg (x: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match x with
  | Core.Base.Spec.Z.Z_NEG p -> Core.Base.Spec.Z.Z_POS p <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_POS p -> Core.Base.Spec.Z.Z_NEG p <: Core.Base.Spec.Z.t_Z

let z_add__z_pred_double (s: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match s with
  | Core.Base.Spec.Z.Z_ZERO  ->
    Core.Base.Spec.Z.Z_NEG Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_POS p ->
    Core.Base.Spec.Z.Z_POS (Core.Base.Binary.positive_pred_double p) <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_NEG p ->
    Core.Base.Spec.Z.Z_NEG (Core.Base.Spec.Binary.Positive.xI p) <: Core.Base.Spec.Z.t_Z

let z_add__z_succ_double (s: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match s with
  | Core.Base.Spec.Z.Z_ZERO  ->
    Core.Base.Spec.Z.Z_POS Core.Base.Spec.Binary.Positive.xH <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_POS p ->
    Core.Base.Spec.Z.Z_POS (Core.Base.Spec.Binary.Positive.xI p) <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_NEG p ->
    Core.Base.Spec.Z.Z_NEG (Core.Base.Binary.positive_pred_double p) <: Core.Base.Spec.Z.t_Z

let rec z_bitor__haxint_ldiff__positive_ldiff (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Pos.t_POS =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO _ ->
        Core.Base.Spec.Binary.Pos.POS_POS Core.Base.Spec.Binary.Positive.xH
        <:
        Core.Base.Spec.Binary.Pos.t_POS
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI _ ->
        Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Spec.Binary.Positive.xO p)
        <:
        Core.Base.Spec.Binary.Pos.t_POS
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        z_bitor__haxint_ldiff__n_double (z_bitor__haxint_ldiff__positive_ldiff p q
            <:
            Core.Base.Spec.Binary.Pos.t_POS)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        z_bitor__haxint_ldiff__n_double (z_bitor__haxint_ldiff__positive_ldiff p q
            <:
            Core.Base.Spec.Binary.Pos.t_POS))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Spec.Binary.Positive.xO p)
      <:
      Core.Base.Spec.Binary.Pos.t_POS
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      z_bitor__haxint_ldiff__n_succ_double (z_bitor__haxint_ldiff__positive_ldiff p q
          <:
          Core.Base.Spec.Binary.Pos.t_POS)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      z_bitor__haxint_ldiff__n_double (z_bitor__haxint_ldiff__positive_ldiff p q
          <:
          Core.Base.Spec.Binary.Pos.t_POS)

let z_bitor__haxint_ldiff (lhs rhs: Core.Base.Spec.Binary.Pos.t_POS)
    : Core.Base.Spec.Binary.Pos.t_POS =
  match lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
      Core.Base.Spec.Binary.Pos.POS_POS p <: Core.Base.Spec.Binary.Pos.t_POS
    | Core.Base.Spec.Binary.Pos.POS_POS q -> z_bitor__haxint_ldiff__positive_ldiff p q

let z_bitor__n_and (lhs rhs: Core.Base.Spec.Binary.Pos.t_POS) : Core.Base.Spec.Binary.Pos.t_POS =
  match lhs with
  | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
    Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Pos.POS_POS p ->
    match rhs with
    | Core.Base.Spec.Binary.Pos.POS_ZERO  ->
      Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
    | Core.Base.Spec.Binary.Pos.POS_POS q ->
      Core.Base.Spec.Binary.Pos.POS_POS
      (Core.Base.Spec.Binary.Positive.positive_from_int (Core.Base.Pos.bitand_binary p q
            <:
            Core.Base.Spec.Haxint.t_HaxInt))
      <:
      Core.Base.Spec.Binary.Pos.t_POS

let z_bitor__positive_pred_N (x: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Pos.t_POS =
  match Core.Base.Spec.Binary.Positive.match_positive x with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    Core.Base.Spec.Binary.Pos.POS_ZERO <: Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Spec.Binary.Positive.xO p)
    <:
    Core.Base.Spec.Binary.Pos.t_POS
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Core.Base.Spec.Binary.Pos.POS_POS (Core.Base.Binary.positive_pred_double p)
    <:
    Core.Base.Spec.Binary.Pos.t_POS

let z_bitor (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match lhs with
  | Core.Base.Spec.Z.Z_ZERO  -> rhs
  | Core.Base.Spec.Z.Z_POS x ->
    (match rhs with
      | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_POS x <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_POS y ->
        Core.Base.Spec.Z.Z_POS (Core.Base.Pos.bitor_binary x y) <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_NEG y ->
        Core.Base.Spec.Z.Z_NEG
        (z_bitor__n_succ (z_bitor__haxint_ldiff (z_bitor__positive_pred_N y
                  <:
                  Core.Base.Spec.Binary.Pos.t_POS)
                (Core.Base.Spec.Binary.Pos.POS_POS x <: Core.Base.Spec.Binary.Pos.t_POS)
              <:
              Core.Base.Spec.Binary.Pos.t_POS))
        <:
        Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Z.Z_NEG x ->
    match rhs with
    | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_NEG x <: Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Z.Z_POS y ->
      Core.Base.Spec.Z.Z_NEG
      (z_bitor__n_succ (z_bitor__haxint_ldiff (z_bitor__positive_pred_N x
                <:
                Core.Base.Spec.Binary.Pos.t_POS)
              (Core.Base.Spec.Binary.Pos.POS_POS y <: Core.Base.Spec.Binary.Pos.t_POS)
            <:
            Core.Base.Spec.Binary.Pos.t_POS))
      <:
      Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Z.Z_NEG y ->
      Core.Base.Spec.Z.Z_NEG
      (z_bitor__n_succ (z_bitor__n_and (z_bitor__positive_pred_N x
                <:
                Core.Base.Spec.Binary.Pos.t_POS)
              (z_bitor__positive_pred_N y <: Core.Base.Spec.Binary.Pos.t_POS)
            <:
            Core.Base.Spec.Binary.Pos.t_POS))
      <:
      Core.Base.Spec.Z.t_Z

let z_cmp (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Cmp.t_Ordering =
  match lhs with
  | Core.Base.Spec.Z.Z_NEG p ->
    (match rhs with
      | Core.Base.Spec.Z.Z_NEG q ->
        (match Core.Base.Binary.positive_cmp p q with
          | Core.Cmp.Ordering_Equal  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
          | Core.Cmp.Ordering_Less  -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
          | Core.Cmp.Ordering_Greater  -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
      | _ -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
  | Core.Base.Spec.Z.Z_ZERO  ->
    (match rhs with
      | Core.Base.Spec.Z.Z_ZERO  -> Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering
      | Core.Base.Spec.Z.Z_POS _ -> Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering
      | Core.Base.Spec.Z.Z_NEG _ -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
  | Core.Base.Spec.Z.Z_POS p ->
    match rhs with
    | Core.Base.Spec.Z.Z_POS q -> Core.Base.Binary.positive_cmp p q
    | _ -> Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering

let z_le (lhs rhs: Core.Base.Spec.Z.t_Z) : bool =
  match Core.Option.Option_Some (z_cmp lhs rhs) <: Core.Option.t_Option Core.Cmp.t_Ordering with
  | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
  | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
  | _ -> false

let z_lt (lhs rhs: Core.Base.Spec.Z.t_Z) : bool =
  match Core.Option.Option_Some (z_cmp lhs rhs) <: Core.Option.t_Option Core.Cmp.t_Ordering with
  | Core.Option.Option_Some (Core.Cmp.Ordering_Less ) -> true
  | _ -> false

let rec z_add__pos_z_sub (x y: Core.Base.Spec.Binary.Positive.t_Positive) : Core.Base.Spec.Z.t_Z =
  match Core.Base.Spec.Binary.Positive.match_positive x with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive y with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Z.Z_NEG (Core.Base.Binary.positive_pred_double q) <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Z.Z_NEG (Core.Base.Spec.Binary.Positive.xO q) <: Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive y with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Z.Z_POS (Core.Base.Binary.positive_pred_double p) <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        z_add__z_double (z_add__pos_z_sub p q <: Core.Base.Spec.Z.t_Z)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        z_add__z_pred_double (z_add__pos_z_sub p q <: Core.Base.Spec.Z.t_Z))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive y with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Z.Z_POS (Core.Base.Spec.Binary.Positive.xO p) <: Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      z_add__z_succ_double (z_add__pos_z_sub p q <: Core.Base.Spec.Z.t_Z)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      z_add__z_double (z_add__pos_z_sub p q <: Core.Base.Spec.Z.t_Z)

let z_add (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match lhs with
  | Core.Base.Spec.Z.Z_NEG p ->
    (match rhs with
      | Core.Base.Spec.Z.Z_NEG q ->
        Core.Base.Spec.Z.Z_NEG (Core.Base.Binary.positive_add p q) <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_NEG p <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_POS q -> z_add__pos_z_sub q p)
  | Core.Base.Spec.Z.Z_ZERO  -> rhs
  | Core.Base.Spec.Z.Z_POS p ->
    match rhs with
    | Core.Base.Spec.Z.Z_NEG q -> z_add__pos_z_sub p q
    | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_POS p <: Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Z.Z_POS q ->
      Core.Base.Spec.Z.Z_POS (Core.Base.Binary.positive_add p q) <: Core.Base.Spec.Z.t_Z

let z_sub (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  z_add lhs (z_neg rhs <: Core.Base.Spec.Z.t_Z)

let z_mul (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  match lhs with
  | Core.Base.Spec.Z.Z_NEG p ->
    (match rhs with
      | Core.Base.Spec.Z.Z_NEG q ->
        Core.Base.Spec.Z.Z_POS (Core.Base.Binary.positive_mul p q) <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
      | Core.Base.Spec.Z.Z_POS q ->
        Core.Base.Spec.Z.Z_NEG (Core.Base.Binary.positive_mul p q) <: Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
  | Core.Base.Spec.Z.Z_POS p ->
    match rhs with
    | Core.Base.Spec.Z.Z_NEG q ->
      Core.Base.Spec.Z.Z_NEG (Core.Base.Binary.positive_mul p q) <: Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Z.Z_ZERO  -> Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z
    | Core.Base.Spec.Z.Z_POS q ->
      Core.Base.Spec.Z.Z_POS (Core.Base.Binary.positive_mul p q) <: Core.Base.Spec.Z.t_Z

let rec pos_div_eucl (a: Core.Base.Spec.Binary.Positive.t_Positive) (b: Core.Base.Spec.Z.t_Z)
    : (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
  match Core.Base.Spec.Binary.Positive.match_positive a with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    if
      z_le Core.Base.Spec.Z.v_Z_TWO
        (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Spec.Z.t_Z)
    then
      (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z), Core.Base.Spec.Z.v_Z_ONE
      <:
      (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
    else
      Core.Base.Spec.Z.v_Z_ONE, (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z)
      <:
      (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    let q, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
      pos_div_eucl p
        (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Spec.Z.t_Z)
    in
    let r___:Core.Base.Spec.Z.t_Z = z_mul Core.Base.Spec.Z.v_Z_TWO r in
    if
      z_lt (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve r___
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Spec.Z.t_Z)
    then z_mul Core.Base.Spec.Z.v_Z_TWO q, r___ <: (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
    else
      z_add (z_mul Core.Base.Spec.Z.v_Z_TWO q <: Core.Base.Spec.Z.t_Z) Core.Base.Spec.Z.v_Z_ONE,
      z_sub r___ b
      <:
      (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    let q, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
      pos_div_eucl p
        (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Spec.Z.t_Z)
    in
    let r___:Core.Base.Spec.Z.t_Z =
      z_add (z_mul Core.Base.Spec.Z.v_Z_TWO r <: Core.Base.Spec.Z.t_Z) Core.Base.Spec.Z.v_Z_ONE
    in
    if
      z_lt (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve r___
          <:
          Core.Base.Spec.Z.t_Z)
        (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
          <:
          Core.Base.Spec.Z.t_Z)
    then z_mul Core.Base.Spec.Z.v_Z_TWO q, r___ <: (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
    else
      z_add (z_mul Core.Base.Spec.Z.v_Z_TWO q <: Core.Base.Spec.Z.t_Z) Core.Base.Spec.Z.v_Z_ONE,
      z_sub r___ b
      <:
      (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)

let z_divmod (a b: Core.Base.Spec.Z.t_Z) : (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
  match a with
  | Core.Base.Spec.Z.Z_ZERO  ->
    (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z),
    (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z)
    <:
    (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
  | Core.Base.Spec.Z.Z_POS a___ ->
    (match Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b with
      | Core.Base.Spec.Z.Z_ZERO  ->
        (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z),
        (Core.Base.Spec.Z.Z_POS a___ <: Core.Base.Spec.Z.t_Z)
        <:
        (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
      | Core.Base.Spec.Z.Z_POS b___ -> pos_div_eucl a___ b
      | Core.Base.Spec.Z.Z_NEG b___ ->
        let q, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
          pos_div_eucl a___ (Core.Base.Spec.Z.Z_POS b___ <: Core.Base.Spec.Z.t_Z)
        in
        z_neg q, r <: (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z))
  | Core.Base.Spec.Z.Z_NEG a___ ->
    match Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b with
    | Core.Base.Spec.Z.Z_ZERO  ->
      (Core.Base.Spec.Z.Z_ZERO <: Core.Base.Spec.Z.t_Z),
      (Core.Base.Spec.Z.Z_NEG a___ <: Core.Base.Spec.Z.t_Z)
      <:
      (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
    | Core.Base.Spec.Z.Z_POS _ ->
      let q, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
        pos_div_eucl a___
          (Core.Clone.f_clone #Core.Base.Spec.Z.t_Z #FStar.Tactics.Typeclasses.solve b
            <:
            Core.Base.Spec.Z.t_Z)
      in
      z_neg q, z_neg r <: (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)
    | Core.Base.Spec.Z.Z_NEG b___ ->
      let q, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) =
        pos_div_eucl a___ (Core.Base.Spec.Z.Z_POS b___ <: Core.Base.Spec.Z.t_Z)
      in
      q, z_neg r <: (Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z)

let z_div (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  let q, _:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) = z_divmod lhs rhs in
  q

let z_rem (lhs rhs: Core.Base.Spec.Z.t_Z) : Core.Base.Spec.Z.t_Z =
  let _, r:(Core.Base.Spec.Z.t_Z & Core.Base.Spec.Z.t_Z) = z_divmod lhs rhs in
  r
