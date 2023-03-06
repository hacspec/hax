open Base
open Utils

module Make (FA : Features.T) = struct
  open Ast

  (* module FA = FA *)
  module FB = struct
    include FA

    (* include Features.Off.Mutable_reference *)
    include Features.Off.Raw_pointer
    include Features.Off.Mutable_pointer
  end

  (* module S: Features.Subtype with module A = FA and module B = FB = struct *)
  module S = struct
    module A = FA
    module B = FB
    include Features.SUBTYPE.Id

    let mutable_pointer _ = failwith "mutable_pointer"

    (* let mutable_reference _ = failwith "mutable_reference" *)
    let raw_pointer _ = failwith "raw_pointer"
  end

  include Subtype.Make (FA) (FB) (S)

  let metadata = Desugar_utils.Metadata.make "RejectMutableReferences"
end

module MakeContinueReject (FA : Features.T) = struct
  open Ast

  module FB = struct
    include FA
    include Features.Off.Continue
  end

  module S = struct
    module A = FA
    module B = FB
    include Features.SUBTYPE.Id

    let continue _ = failwith "continue"
  end

  include Subtype.Make (FA) (FB) (S)

  let metadata = Desugar_utils.Metadata.make "RejectContinue"
end

module EnsureIsFStar (FA : Features.T) = struct
  open Ast
  open Features
  module FB = Features.FStar

  module S = struct
    module A = FA
    module B = FB
    include Features.SUBTYPE.Id

    let loop _ = failwith "loop"
    let continue _ = failwith "continue"
    let mutable_variable _ = failwith "mutable_variable"
    let mutable_reference _ = failwith "mutable_reference"
    let mutable_pointer _ = failwith "mutable_pointer"
    let mutable_borrow _ = failwith "mutable_borrow"
    let reference _ = failwith "reference"
    let slice _ = failwith "slice"
    let raw_pointer _ = failwith "raw_pointer"

    (* let early_exit _ = failwith "early_exit"  *)
    let early_exit _ = Obj.magic ()
    let macro _ = failwith "macro"
    let as_pattern _ = failwith "as_pattern"
    let lifetime _ = failwith "lifetime"
    let monadic_action _ = failwith "monadic action"
    let monadic_binding _ = ()
    let for_loop _ = failwith "for_loop"
  end

  let metadata = Desugar_utils.Metadata.make "RejectAnythingNotFStar"

  include Subtype.Make (FA) (FB) (S)
end
