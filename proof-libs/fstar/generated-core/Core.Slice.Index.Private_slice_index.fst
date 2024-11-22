module Core.Slice.Index.Private_slice_index
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open Core
open FStar.Mul

class t_Sealed (v_Self: Type0) = { __marker_trait_t_Sealed:Prims.unit }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_2: t_Sealed (Core.Ops.Range.t_RangeTo usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_3: t_Sealed (Core.Ops.Range.t_RangeFrom usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_4: t_Sealed Core.Ops.Range.t_RangeFull = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_5: t_Sealed (Core.Ops.Range.t_RangeInclusive usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_6: t_Sealed (Core.Ops.Range.t_RangeToInclusive usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_7: t_Sealed (Core.Ops.Range.t_Bound usize & Core.Ops.Range.t_Bound usize) =
  { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_1: t_Sealed (Core.Ops.Range.t_Range usize) = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl_8: t_Sealed Core.Ops.Index_range.t_IndexRange = { __marker_trait = () }

[@@ FStar.Tactics.Typeclasses.tcinstance]
let impl: t_Sealed Core.Primitive.t_usize = { __marker_trait = () }
