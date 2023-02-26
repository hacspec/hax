
type on = unit [@@deriving show, yojson, eq]
type off = | [@@deriving show, yojson, eq]

[%%declare_features
  loop,
  continue,
  mutable_variable,
  mutable_reference,
  mutable_pointer,
  mutable_borrow,
  reference,
  slice,
  raw_pointer,
  early_exit,
  macro,
  as_pattern,
  lifetime,
  monadic_action,
  monadic_binding
]

module Full = On

module Rust = struct
  include On
  
  type monadic_action = off [@@deriving show, yojson, eq]
  type monadic_binding = off [@@deriving show, yojson, eq]
end

module FStar = struct
  include Off
  include On.Monadic_binding
end

module _ = struct
  module _ : T = Full
  module _ : T = Rust
  module _ : T = FStar
end
