module Core_models.Cmp
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_PartialEq as t_PartialEq}

include Core_models.Bundle {f_eq_pre as f_eq_pre}

include Core_models.Bundle {f_eq_post as f_eq_post}

include Core_models.Bundle {f_eq as f_eq}

include Core_models.Bundle {t_Eq as t_Eq}

include Core_models.Bundle {t_Ordering_cast_to_repr as t_Ordering_cast_to_repr}

include Core_models.Bundle {t_Ordering as t_Ordering}

include Core_models.Bundle {Ordering_Less as Ordering_Less}

include Core_models.Bundle {Ordering_Equal as Ordering_Equal}

include Core_models.Bundle {Ordering_Greater as Ordering_Greater}

include Core_models.Bundle {anon_const_Ordering_Less__anon_const_0 as anon_const_Ordering_Less__anon_const_0}

include Core_models.Bundle {anon_const_Ordering_Equal__anon_const_0 as anon_const_Ordering_Equal__anon_const_0}

include Core_models.Bundle {anon_const_Ordering_Greater__anon_const_0 as anon_const_Ordering_Greater__anon_const_0}

include Core_models.Bundle {t_PartialOrd as t_PartialOrd}

include Core_models.Bundle {f_partial_cmp_pre as f_partial_cmp_pre}

include Core_models.Bundle {f_partial_cmp_post as f_partial_cmp_post}

include Core_models.Bundle {f_partial_cmp as f_partial_cmp}

include Core_models.Bundle {t_Neq as t_Neq}

include Core_models.Bundle {f_neq_pre as f_neq_pre}

include Core_models.Bundle {f_neq_post as f_neq_post}

include Core_models.Bundle {f_neq as f_neq}

include Core_models.Bundle {impl__from__cmp as impl}

include Core_models.Bundle {t_PartialOrdDefaults as t_PartialOrdDefaults}

include Core_models.Bundle {f_lt_pre as f_lt_pre}

include Core_models.Bundle {f_lt_post as f_lt_post}

include Core_models.Bundle {f_lt as f_lt}

include Core_models.Bundle {f_le_pre as f_le_pre}

include Core_models.Bundle {f_le_post as f_le_post}

include Core_models.Bundle {f_le as f_le}

include Core_models.Bundle {f_gt_pre as f_gt_pre}

include Core_models.Bundle {f_gt_post as f_gt_post}

include Core_models.Bundle {f_gt as f_gt}

include Core_models.Bundle {f_ge_pre as f_ge_pre}

include Core_models.Bundle {f_ge_post as f_ge_post}

include Core_models.Bundle {f_ge as f_ge}

include Core_models.Bundle {impl_1__from__cmp as impl_1}

include Core_models.Bundle {t_Ord as t_Ord}

include Core_models.Bundle {f_cmp_pre as f_cmp_pre}

include Core_models.Bundle {f_cmp_post as f_cmp_post}

include Core_models.Bundle {f_cmp as f_cmp}

include Core_models.Bundle {max as max}

include Core_models.Bundle {min as min}

include Core_models.Bundle {t_Reverse as t_Reverse}

include Core_models.Bundle {Reverse as Reverse}

include Core_models.Bundle {impl_2 as impl_2}

include Core_models.Bundle {impl_3 as impl_3}

include Core_models.Bundle {impl_4 as impl_4}

include Core_models.Bundle {impl_5__from__cmp as impl_5}

include Core_models.Bundle {impl_34 as impl_34}

include Core_models.Bundle {impl_35__from__cmp as impl_Ord_for_u8}

include Core_models.Bundle {impl_10 as impl_10}

include Core_models.Bundle {impl_11 as impl_Eq_for_u8}

include Core_models.Bundle {impl_36 as impl_36}

include Core_models.Bundle {impl_37__from__cmp as impl_Ord_for_i8}

include Core_models.Bundle {impl_12 as impl_12}

include Core_models.Bundle {impl_13 as impl_Eq_for_i8}

include Core_models.Bundle {impl_38 as impl_38}

include Core_models.Bundle {impl_39__from__cmp as impl_Ord_for_u16}

include Core_models.Bundle {impl_14 as impl_14}

include Core_models.Bundle {impl_15 as impl_Eq_for_u16}

include Core_models.Bundle {impl_40 as impl_40}

include Core_models.Bundle {impl_41__from__cmp as impl_Ord_for_i16}

include Core_models.Bundle {impl_16 as impl_16}

include Core_models.Bundle {impl_17 as impl_Eq_for_i16}

include Core_models.Bundle {impl_42 as impl_42}

include Core_models.Bundle {impl_43__from__cmp as impl_Ord_for_u32}

include Core_models.Bundle {impl_18 as impl_18}

include Core_models.Bundle {impl_19 as impl_Eq_for_u32}

include Core_models.Bundle {impl_44 as impl_44}

include Core_models.Bundle {impl_45__from__cmp as impl_Ord_for_i32}

include Core_models.Bundle {impl_20 as impl_20}

include Core_models.Bundle {impl_21 as impl_Eq_for_i32}

include Core_models.Bundle {impl_46 as impl_46}

include Core_models.Bundle {impl_47__from__cmp as impl_Ord_for_u64}

include Core_models.Bundle {impl_22 as impl_22}

include Core_models.Bundle {impl_23 as impl_Eq_for_u64}

include Core_models.Bundle {impl_48 as impl_48}

include Core_models.Bundle {impl_49__from__cmp as impl_Ord_for_i64}

include Core_models.Bundle {impl_24__from__cmp as impl_24}

include Core_models.Bundle {impl_25__from__cmp as impl_Eq_for_i64}

include Core_models.Bundle {impl_50 as impl_50}

include Core_models.Bundle {impl_51__from__cmp as impl_Ord_for_u128}

include Core_models.Bundle {impl_26__from__cmp as impl_26}

include Core_models.Bundle {impl_27__from__cmp as impl_Eq_for_u128}

include Core_models.Bundle {impl_52 as impl_52}

include Core_models.Bundle {impl_53__from__cmp as impl_Ord_for_i128}

include Core_models.Bundle {impl_28__from__cmp as impl_28}

include Core_models.Bundle {impl_29__from__cmp as impl_Eq_for_i128}

include Core_models.Bundle {impl_54 as impl_54}

include Core_models.Bundle {impl_55__from__cmp as impl_Ord_for_usize}

include Core_models.Bundle {impl_30__from__cmp as impl_30}

include Core_models.Bundle {impl_31__from__cmp as impl_Eq_for_usize}

include Core_models.Bundle {impl_56 as impl_56}

include Core_models.Bundle {impl_57__from__cmp as impl_Ord_for_isize}

include Core_models.Bundle {impl_32 as impl_32}

include Core_models.Bundle {impl_33 as impl_Eq_for_isize}

include Core_models.Bundle {impl_58__is_eq as impl_Ordering__is_eq}

include Core_models.Bundle {impl_58__is_ne as impl_Ordering__is_ne}

include Core_models.Bundle {impl_58__is_lt as impl_Ordering__is_lt}

include Core_models.Bundle {impl_58__is_gt as impl_Ordering__is_gt}

include Core_models.Bundle {impl_58__is_le as impl_Ordering__is_le}

include Core_models.Bundle {impl_58__is_ge as impl_Ordering__is_ge}

include Core_models.Bundle {impl_58__reverse as impl_Ordering__reverse}

include Core_models.Bundle {impl_58__then as impl_Ordering__then}

include Core_models.Bundle {impl_58__then_with as impl_Ordering__then_with}

include Core_models.Bundle {clamp as clamp}

include Core_models.Bundle {impl_6 as impl_6}

include Core_models.Bundle {impl_7 as impl_Eq_for_tuple_}

include Core_models.Bundle {impl_8 as impl_8}

include Core_models.Bundle {impl_9__from__cmp as impl_Ord_for_tuple_}
