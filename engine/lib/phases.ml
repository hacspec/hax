module Direct_and_mut = Phase_direct_and_mut.Make
module Drop_references = Phase_drop_references.Make
module Reconstruct_for_loops = Phase_reconstruct_for_loops.Make
module Trivialize_assign_lhs = Phase_trivialize_assign_lhs.Make
module Functionalize_loops = Phase_functionalize_loops.Make
module Reject = Phase_reject
