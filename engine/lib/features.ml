[%%declare_features
loop,
  for_loop,
  state_passing_loop,
  continue,
  mutable_variable,
  mutable_reference,
  mutable_pointer,
  reference,
  slice,
  raw_pointer,
  early_exit,
  macro,
  as_pattern,
  arbitrary_lhs,
  lifetime,
  monadic_action,
  monadic_binding]

module Full = On

module Rust = struct
  include On
  include Off.For_loop
  include Off.Monadic_action
  include Off.Monadic_binding
end

module _ = struct
  module _ : T = Full
  module _ : T = Rust
end
