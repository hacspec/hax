-- Hand-written stub. Aeneas emits `FunsExternal_Template.lean` listing
-- axioms for items whose bodies it can't see; those already live in the
-- parent `CoreModels.FunsExternal` module, which is pulled in by
-- `import CoreModels` from the generated `Funs.lean`. This file just needs
-- to exist to satisfy the shim hax writes at `Extraction/FunsExternal.lean`.
module
public import Aeneas
@[expose] public section
