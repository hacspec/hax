[%%declare_features
loop,
  for_loop,
  for_index_loop,
  while_loop,
  state_passing_loop,
  continue,
  break,
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
  monadic_binding,
  quote,
  block]

module Full = On

module Rust = struct
  include On
  include Off.While_loop
  include Off.For_loop
  include Off.For_index_loop
  include Off.Question_mark
  include Off.Monadic_action
  include Off.Monadic_binding
  include Off.State_passing_loop
  include Off.Quote
end

let _ = Enumeration.all

module _ = struct
  module _ : T = Full
  module _ : T = Rust
end
