module Core_models.Iter.Traits.Iterator
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Iterator as t_Iterator}

include Core_models.Bundle {f_Item as f_Item}

include Core_models.Bundle {f_next_pre as f_next_pre}

include Core_models.Bundle {f_next_post as f_next_post}

include Core_models.Bundle {f_next as f_next}

include Core_models.Bundle {t_IteratorMethods as t_IteratorMethods}

include Core_models.Bundle {f_fold_pre as f_fold_pre}

include Core_models.Bundle {f_fold_post as f_fold_post}

include Core_models.Bundle {f_fold as f_fold}

include Core_models.Bundle {f_all_pre as f_all_pre}

include Core_models.Bundle {f_all_post as f_all_post}

include Core_models.Bundle {f_all as f_all}

include Core_models.Bundle {f_map_pre as f_map_pre}

include Core_models.Bundle {f_map_post as f_map_post}

include Core_models.Bundle {f_map as f_map}

include Core_models.Bundle {f_enumerate_pre as f_enumerate_pre}

include Core_models.Bundle {f_enumerate_post as f_enumerate_post}

include Core_models.Bundle {f_enumerate as f_enumerate}

include Core_models.Bundle {f_step_by_pre as f_step_by_pre}

include Core_models.Bundle {f_step_by_post as f_step_by_post}

include Core_models.Bundle {f_step_by as f_step_by}

include Core_models.Bundle {f_take_pre as f_take_pre}

include Core_models.Bundle {f_take_post as f_take_post}

include Core_models.Bundle {f_take as f_take}

include Core_models.Bundle {f_skip_pre as f_skip_pre}

include Core_models.Bundle {f_skip_post as f_skip_post}

include Core_models.Bundle {f_skip as f_skip}

include Core_models.Bundle {f_filter_pre as f_filter_pre}

include Core_models.Bundle {f_filter_post as f_filter_post}

include Core_models.Bundle {f_filter as f_filter}

include Core_models.Bundle {f_filter_map_pre as f_filter_map_pre}

include Core_models.Bundle {f_filter_map_post as f_filter_map_post}

include Core_models.Bundle {f_filter_map as f_filter_map}

include Core_models.Bundle {f_take_while_pre as f_take_while_pre}

include Core_models.Bundle {f_take_while_post as f_take_while_post}

include Core_models.Bundle {f_take_while as f_take_while}

include Core_models.Bundle {f_skip_while_pre as f_skip_while_pre}

include Core_models.Bundle {f_skip_while_post as f_skip_while_post}

include Core_models.Bundle {f_skip_while as f_skip_while}

include Core_models.Bundle {f_map_while_pre as f_map_while_pre}

include Core_models.Bundle {f_map_while_post as f_map_while_post}

include Core_models.Bundle {f_map_while as f_map_while}

include Core_models.Bundle {f_inspect_pre as f_inspect_pre}

include Core_models.Bundle {f_inspect_post as f_inspect_post}

include Core_models.Bundle {f_inspect as f_inspect}

include Core_models.Bundle {f_fuse_pre as f_fuse_pre}

include Core_models.Bundle {f_fuse_post as f_fuse_post}

include Core_models.Bundle {f_fuse as f_fuse}

include Core_models.Bundle {f_flat_map_pre as f_flat_map_pre}

include Core_models.Bundle {f_flat_map_post as f_flat_map_post}

include Core_models.Bundle {f_flat_map as f_flat_map}

include Core_models.Bundle {f_flatten_pre as f_flatten_pre}

include Core_models.Bundle {f_flatten_post as f_flatten_post}

include Core_models.Bundle {f_flatten as f_flatten}

include Core_models.Bundle {f_zip_pre as f_zip_pre}

include Core_models.Bundle {f_zip_post as f_zip_post}

include Core_models.Bundle {f_zip as f_zip}

include Core_models.Bundle {f_chain_pre as f_chain_pre}

include Core_models.Bundle {f_chain_post as f_chain_post}

include Core_models.Bundle {f_chain as f_chain}

include Core_models.Bundle {f_any_pre as f_any_pre}

include Core_models.Bundle {f_any_post as f_any_post}

include Core_models.Bundle {f_any as f_any}

include Core_models.Bundle {f_find_pre as f_find_pre}

include Core_models.Bundle {f_find_post as f_find_post}

include Core_models.Bundle {f_find as f_find}

include Core_models.Bundle {f_find_map_pre as f_find_map_pre}

include Core_models.Bundle {f_find_map_post as f_find_map_post}

include Core_models.Bundle {f_find_map as f_find_map}

include Core_models.Bundle {f_position_pre as f_position_pre}

include Core_models.Bundle {f_position_post as f_position_post}

include Core_models.Bundle {f_position as f_position}

include Core_models.Bundle {f_count_pre as f_count_pre}

include Core_models.Bundle {f_count_post as f_count_post}

include Core_models.Bundle {f_count as f_count}

include Core_models.Bundle {f_nth_pre as f_nth_pre}

include Core_models.Bundle {f_nth_post as f_nth_post}

include Core_models.Bundle {f_nth as f_nth}

include Core_models.Bundle {f_last_pre as f_last_pre}

include Core_models.Bundle {f_last_post as f_last_post}

include Core_models.Bundle {f_last as f_last}

include Core_models.Bundle {f_for_each_pre as f_for_each_pre}

include Core_models.Bundle {f_for_each_post as f_for_each_post}

include Core_models.Bundle {f_for_each as f_for_each}

include Core_models.Bundle {f_reduce_pre as f_reduce_pre}

include Core_models.Bundle {f_reduce_post as f_reduce_post}

include Core_models.Bundle {f_reduce as f_reduce}

include Core_models.Bundle {f_min_pre as f_min_pre}

include Core_models.Bundle {f_min_post as f_min_post}

include Core_models.Bundle {f_min as f_min}

include Core_models.Bundle {f_max_pre as f_max_pre}

include Core_models.Bundle {f_max_post as f_max_post}

include Core_models.Bundle {f_max as f_max}

include Core_models.Bundle {f_collect_pre as f_collect_pre}

include Core_models.Bundle {f_collect_post as f_collect_post}

include Core_models.Bundle {f_collect as f_collect}

include Core_models.Bundle {iter_fold as iter_fold}

include Core_models.Bundle {iter_all as iter_all}

include Core_models.Bundle {iter_any as iter_any}

include Core_models.Bundle {iter_find as iter_find}

include Core_models.Bundle {iter_find_map as iter_find_map}

include Core_models.Bundle {iter_position as iter_position}

include Core_models.Bundle {iter_count as iter_count}

include Core_models.Bundle {iter_nth as iter_nth}

include Core_models.Bundle {iter_last as iter_last}

include Core_models.Bundle {iter_for_each as iter_for_each}

include Core_models.Bundle {iter_reduce as iter_reduce}

include Core_models.Bundle {iter_min as iter_min}

include Core_models.Bundle {iter_max as iter_max}

include Core_models.Bundle {impl__from__iterator as impl}

include Core_models.Bundle {impl_1__from__iterator as impl_1}
