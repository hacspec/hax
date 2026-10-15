import CoreModels.Core.Funs

namespace CoreModels

open Aeneas
open Aeneas.Std hiding namespace core alloc
open Std.Do WP RustM

set_option mvcgen.warning false

attribute [spec]
  CoreModels.core.num.U8.from_le_bytes
  CoreModels.core.num.U16.from_le_bytes
  CoreModels.core.num.U32.from_le_bytes
  CoreModels.core.num.U64.from_le_bytes
  CoreModels.core.num.U128.from_le_bytes
  CoreModels.core.num.Usize.from_le_bytes
  CoreModels.core.num.U8.to_le_bytes
  CoreModels.core.num.U16.to_le_bytes
  CoreModels.core.num.U32.to_le_bytes
  CoreModels.core.num.U64.to_le_bytes
  CoreModels.core.num.U128.to_le_bytes
  CoreModels.core.num.Usize.to_le_bytes

end CoreModels
