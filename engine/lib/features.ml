[%%declare_features
loop,
  for_loop,
  for_index_loop,
  state_passing_loop,
  continue,
  mutable_variable,
  mutable_reference,
  mutable_pointer,
  reference,
  slice,
  raw_pointer,
  early_exit,
  question_mark,
  macro,
  as_pattern,
  nontrivial_lhs,
  arbitrary_lhs,
  lifetime,
  construct_base,
  monadic_action,
  monadic_binding]

module Full = On

module Rust = struct
  include On
  include Off.For_loop
  include Off.For_index_loop
  include Off.Question_mark
  include Off.Monadic_action
  include Off.Monadic_binding
  include Off.State_passing_loop
end

module _ = struct
  module _ : T = Full
  module _ : T = Rust
end
