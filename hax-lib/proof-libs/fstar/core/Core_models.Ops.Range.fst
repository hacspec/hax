module Core_models.Ops.Range
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_RangeTo as t_RangeTo}

include Core_models.Bundle {t_RangeFrom as t_RangeFrom}

include Core_models.Bundle {t_Range as t_Range}

include Core_models.Bundle {t_RangeFull as t_RangeFull}

include Core_models.Bundle {RangeFull as RangeFull}

include Core_models.Bundle {t_RangeInclusive as t_RangeInclusive}

include Core_models.Bundle {t_RangeToInclusive as t_RangeToInclusive}

include Core_models.Bundle {impl_28__from__range as impl_28}

include Core_models.Bundle {impl_29__from__range as impl_29}

include Core_models.Bundle {impl_30__from__range as impl_30}

include Core_models.Bundle {impl_31__from__range as impl_31}

include Core_models.Bundle {impl_32__from__range as impl_32}

include Core_models.Bundle {impl_33__from__range as impl_33}

include Core_models.Bundle {impl_34__from__range as impl_34}

include Core_models.Bundle {impl_35__from__range as impl_35}

include Core_models.Bundle {impl_36__from__range as impl_36}

include Core_models.Bundle {impl_37__from__range as impl_37}

include Core_models.Bundle {impl_38__from__range as impl_38}

include Core_models.Bundle {impl_39__from__range as impl_39}

include Core_models.Bundle {t_Bound as t_Bound}

include Core_models.Bundle {Bound_Included as Bound_Included}

include Core_models.Bundle {Bound_Excluded as Bound_Excluded}

include Core_models.Bundle {Bound_Unbounded as Bound_Unbounded}

include Core_models.Bundle {t_RangeBounds as t_RangeBounds}

include Core_models.Bundle {f_start_bound_pre as f_start_bound_pre}

include Core_models.Bundle {f_start_bound_post as f_start_bound_post}

include Core_models.Bundle {f_start_bound as f_start_bound}

include Core_models.Bundle {f_end_bound_pre as f_end_bound_pre}

include Core_models.Bundle {f_end_bound_post as f_end_bound_post}

include Core_models.Bundle {f_end_bound as f_end_bound}

include Core_models.Bundle {t_IntoBounds as t_IntoBounds}

include Core_models.Bundle {f_into_bounds_pre as f_into_bounds_pre}

include Core_models.Bundle {f_into_bounds_post as f_into_bounds_post}

include Core_models.Bundle {f_into_bounds as f_into_bounds}

include Core_models.Bundle {t_OneSidedRangeBound_cast_to_repr as t_OneSidedRangeBound_cast_to_repr}

include Core_models.Bundle {t_OneSidedRangeBound as t_OneSidedRangeBound}

include Core_models.Bundle {OneSidedRangeBound_StartInclusive as OneSidedRangeBound_StartInclusive}

include Core_models.Bundle {OneSidedRangeBound_End as OneSidedRangeBound_End}

include Core_models.Bundle {OneSidedRangeBound_EndInclusive as OneSidedRangeBound_EndInclusive}

include Core_models.Bundle {t_OneSidedRange as t_OneSidedRange}

include Core_models.Bundle {f_bound_pre as f_bound_pre}

include Core_models.Bundle {f_bound_post as f_bound_post}

include Core_models.Bundle {f_bound as f_bound}

include Core_models.Bundle {after_start as after_start}

include Core_models.Bundle {before_end as before_end}

include Core_models.Bundle {bounds_are_empty as bounds_are_empty}

include Core_models.Bundle {bounds_intersect as bounds_intersect}

include Core_models.Bundle {bound_le as bound_le}

include Core_models.Bundle {bound_lt as bound_lt}

include Core_models.Bundle {impl as impl}

include Core_models.Bundle {impl_1__from__range as impl_1}

include Core_models.Bundle {impl_2__contains as impl_2__contains}

include Core_models.Bundle {impl_2__is_empty as impl_2__is_empty}

include Core_models.Bundle {impl_3__from__range as impl_3}

include Core_models.Bundle {impl_4__contains as impl_4__contains}

include Core_models.Bundle {impl_5 as impl_5}

include Core_models.Bundle {impl_6__contains as impl_6__contains}

include Core_models.Bundle {impl_7__new as impl_7__new}

include Core_models.Bundle {impl_7__start as impl_7__start}

include Core_models.Bundle {impl_7__end as impl_7__end}

include Core_models.Bundle {impl_7__into_inner as impl_7__into_inner}

include Core_models.Bundle {impl_9__from__range as impl_9}

include Core_models.Bundle {impl_10__contains as impl_10__contains}

include Core_models.Bundle {impl_10__is_empty as impl_10__is_empty}

include Core_models.Bundle {impl_11__from__range as impl_11}

include Core_models.Bundle {impl_12__contains as impl_12__contains}

include Core_models.Bundle {impl_13__as_ref as impl_13__as_ref}

include Core_models.Bundle {impl_13__map as impl_13__map}

include Core_models.Bundle {impl_14__copied as impl_14__copied}

include Core_models.Bundle {impl_15__cloned as impl_15__cloned}

include Core_models.Bundle {impl_16__from__range as impl_16}

include Core_models.Bundle {impl_17__from__range as impl_17}

include Core_models.Bundle {impl_18__from__range as impl_18}

include Core_models.Bundle {impl_19__from__range as impl_19}

include Core_models.Bundle {impl_20__from__range as impl_20}

include Core_models.Bundle {impl_21__from__range as impl_21}

include Core_models.Bundle {impl_22__from__range as impl_22}

include Core_models.Bundle {impl_23__from__range as impl_23}

include Core_models.Bundle {impl_24__from__range as impl_24}

include Core_models.Bundle {impl_25__from__range as impl_25}

include Core_models.Bundle {t_RangeBoundsDefaults as t_RangeBoundsDefaults}

include Core_models.Bundle {f_contains_pre as f_contains_pre}

include Core_models.Bundle {f_contains_post as f_contains_post}

include Core_models.Bundle {f_contains as f_contains}

include Core_models.Bundle {f_is_empty_pre as f_is_empty_pre}

include Core_models.Bundle {f_is_empty_post as f_is_empty_post}

include Core_models.Bundle {f_is_empty as f_is_empty}

include Core_models.Bundle {impl_26__from__range as impl_26}

include Core_models.Bundle {t_IntoBoundsDefaults as t_IntoBoundsDefaults}

include Core_models.Bundle {f_intersect_pre as f_intersect_pre}

include Core_models.Bundle {f_intersect_post as f_intersect_post}

include Core_models.Bundle {f_intersect as f_intersect}

include Core_models.Bundle {impl_27__from__range as impl_27}
