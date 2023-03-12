open Base
open Utils

module Arbitrary_lhs (FA : Features.T) = struct
  module FB = struct
    include FA
    include Features.Off.Arbitrary_lhs
  end

  include
    Feature_gate.Make (FA) (FB)
      (struct
        module A = FA
        module B = FB
        include Feature_gate.DefaultSubtype

        let arbitrary_lhs = reject
        let metadata = Desugar_utils.Metadata.make "RejectArbitrary_lhs"
      end)
end

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
