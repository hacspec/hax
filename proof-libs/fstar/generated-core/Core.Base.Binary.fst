module Core.Base.Binary
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

let rec positive_cmp__cmp_binary_cont
      (x y: Core.Base.Spec.Binary.Positive.t_Positive)
      (r: Core.Cmp.t_Ordering)
    : Core.Cmp.t_Ordering =
  match Core.Base.Spec.Binary.Positive.match_positive x with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive y with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> r
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive y with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q -> positive_cmp__cmp_binary_cont p q r
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        positive_cmp__cmp_binary_cont p q (Core.Cmp.Ordering_Less <: Core.Cmp.t_Ordering))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive y with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      positive_cmp__cmp_binary_cont p q (Core.Cmp.Ordering_Greater <: Core.Cmp.t_Ordering)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q -> positive_cmp__cmp_binary_cont p q r

let positive_cmp (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive) : Core.Cmp.t_Ordering =
  positive_cmp__cmp_binary_cont lhs rhs (Core.Cmp.Ordering_Equal <: Core.Cmp.t_Ordering)

let positive_le (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive) : bool =
  match
    Core.Option.Option_Some (positive_cmp lhs rhs) <: Core.Option.t_Option Core.Cmp.t_Ordering
  with
  | Core.Option.Option_Some (Core.Cmp.Ordering_Less )
  | Core.Option.Option_Some (Core.Cmp.Ordering_Equal ) -> true
  | _ -> false

let rec positive_pred_double (s: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive s with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Core.Base.Spec.Binary.Positive.xI (positive_pred_double p
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    Core.Base.Spec.Binary.Positive.xI (Core.Base.Spec.Binary.Positive.xO p
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let rec positive_succ (s: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive s with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    Core.Base.Spec.Binary.Positive.xO Core.Base.Spec.Binary.Positive.xH
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO q -> Core.Base.Spec.Binary.Positive.xI q
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
    Core.Base.Spec.Binary.Positive.xO (positive_succ q <: Core.Base.Spec.Binary.Positive.t_Positive)

let positive_add (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive = positive_add__add lhs rhs

let rec positive_mul (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> rhs
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    Core.Base.Spec.Binary.Positive.xO (positive_mul p rhs
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    positive_add (Core.Clone.f_clone #Core.Base.Spec.Binary.Positive.t_Positive
          #FStar.Tactics.Typeclasses.solve
          rhs
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)
      (Core.Base.Spec.Binary.Positive.xO (positive_mul p rhs
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
        <:
        Core.Base.Spec.Binary.Positive.t_Positive)

let rec positive_add__add (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Positive.xO Core.Base.Spec.Binary.Positive.xH
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q -> Core.Base.Spec.Binary.Positive.xI q
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.xO (positive_succ q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  -> Core.Base.Spec.Binary.Positive.xI p
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Binary.Positive.xO (positive_add__add p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.xI (positive_add__add p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Positive.xO (positive_succ p
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      Core.Base.Spec.Binary.Positive.xI (positive_add__add p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      Core.Base.Spec.Binary.Positive.xO (positive_add__add_carry p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)

let rec positive_add__add_carry (lhs rhs: Core.Base.Spec.Binary.Positive.t_Positive)
    : Core.Base.Spec.Binary.Positive.t_Positive =
  match Core.Base.Spec.Binary.Positive.match_positive lhs with
  | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Positive.xI Core.Base.Spec.Binary.Positive.xH
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Binary.Positive.xO (positive_succ q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.xI (positive_succ q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XO p ->
    (match Core.Base.Spec.Binary.Positive.match_positive rhs with
      | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
        Core.Base.Spec.Binary.Positive.xO (positive_succ p
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
        Core.Base.Spec.Binary.Positive.xI (positive_add__add p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive)
      | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
        Core.Base.Spec.Binary.Positive.xO (positive_add__add_carry p q
            <:
            Core.Base.Spec.Binary.Positive.t_Positive))
  | Core.Base.Spec.Binary.Positive.POSITIVE_XI p ->
    match Core.Base.Spec.Binary.Positive.match_positive rhs with
    | Core.Base.Spec.Binary.Positive.POSITIVE_XH  ->
      Core.Base.Spec.Binary.Positive.xI (positive_succ p
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XO q ->
      Core.Base.Spec.Binary.Positive.xO (positive_add__add_carry p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
    | Core.Base.Spec.Binary.Positive.POSITIVE_XI q ->
      Core.Base.Spec.Binary.Positive.xI (positive_add__add_carry p q
          <:
          Core.Base.Spec.Binary.Positive.t_Positive)
