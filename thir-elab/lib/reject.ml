open Base
open Utils

module Continue (FA : Features.T) = struct
  module FB = struct
    include FA
    include Features.Off.Continue
  end

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let continue = reject
        let metadata = Desugar_utils.Metadata.make "RejectContinue"
      end)
end

module NotFStar (FA : Features.T) = struct
  module FB = Features.FStar

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let loop = reject
        let continue = reject
        let mutable_variable = reject
        let mutable_reference = reject
        let mutable_pointer = reject
        let mutable_borrow = reject
        let reference = reject
        let slice = reject
        let raw_pointer = reject
        let early_exit _ = Obj.magic ()
        let macro = reject
        let as_pattern = reject
        let lifetime = reject
        let monadic_action = reject
        let monadic_binding _ = ()
        let for_loop = reject
        let metadata = Desugar_utils.Metadata.make "RejectNotFStar"
      end)
end

module RawOrMutPointer (FA : Features.T) = struct
  module FB = struct
    include FA
    include Features.Off.Raw_pointer
    include Features.Off.Mutable_pointer
  end

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let mutable_pointer = reject
        let raw_pointer = reject
        let metadata = Desugar_utils.Metadata.make "RejectRawOrMutPointer"
      end)
end
