module Core_models.Result
#set-options "--fuel 0 --ifuel 1 --z3rlimit 15"
open FStar.Mul
open Rust_primitives

include Core_models.Bundle {t_Result as t_Result}

include Core_models.Bundle {Result_Ok as Result_Ok}

include Core_models.Bundle {Result_Err as Result_Err}

include Core_models.Bundle {impl__is_ok as impl__is_ok}

include Core_models.Bundle {impl__is_ok_and as impl__is_ok_and}

include Core_models.Bundle {impl__is_err as impl__is_err}

include Core_models.Bundle {impl__is_err_and as impl__is_err_and}

include Core_models.Bundle {impl__as_ref__from__result as impl__as_ref}

include Core_models.Bundle {impl__expect__from__result as impl__expect}

include Core_models.Bundle {impl__unwrap__from__result as impl__unwrap}

include Core_models.Bundle {impl__expect_err as impl__expect_err}

include Core_models.Bundle {impl__unwrap_err as impl__unwrap_err}

include Core_models.Bundle {impl__unwrap_or_else__from__result as impl__unwrap_or_else}

include Core_models.Bundle {impl__unwrap_or_default__from__result as impl__unwrap_or_default}

include Core_models.Bundle {impl__map__from__result as impl__map}

include Core_models.Bundle {impl__map_or__from__result as impl__map_or}

include Core_models.Bundle {impl__map_or_else__from__result as impl__map_or_else}

include Core_models.Bundle {impl__map_or_default__from__result as impl__map_or_default}

include Core_models.Bundle {impl__inspect__from__result as impl__inspect}

include Core_models.Bundle {impl__inspect_err as impl__inspect_err}

include Core_models.Bundle {impl__ok as impl__ok}

include Core_models.Bundle {impl__err as impl__err}

include Core_models.Bundle {impl__and__from__result as impl__and}

include Core_models.Bundle {impl__and_then__from__result as impl__and_then}

include Core_models.Bundle {impl__or__from__result as impl__or}

include Core_models.Bundle {impl__or_else__from__result as impl__or_else}

include Core_models.Bundle {impl__unwrap_or__from__result as impl__unwrap_or}

include Core_models.Bundle {impl__map_err as impl__map_err}

include Core_models.Bundle {impl__unwrap_unchecked__from__result as impl__unwrap_unchecked}

include Core_models.Bundle {impl__unwrap_err_unchecked as impl__unwrap_err_unchecked}

include Core_models.Bundle {impl__iter__from__result as impl__iter}

include Core_models.Bundle {impl__as_deref__from__result as impl__as_deref}

include Core_models.Bundle {impl_1__copied as impl_1__copied}

include Core_models.Bundle {impl_1__cloned as impl_1__cloned}

include Core_models.Bundle {impl_3__transpose as impl_3__transpose}

include Core_models.Bundle {impl_4__flatten as impl_4__flatten}

include Core_models.Bundle {t_SeqIter as t_SeqIter}

include Core_models.Bundle {SeqIter as SeqIter}

include Core_models.Bundle {impl_5__from__result as impl_5}

include Core_models.Bundle {impl_6__from__result as impl_6}

include Core_models.Bundle {impl_7__from__result as impl_7}

include Core_models.Bundle {impl_8__from__result as impl_8}

include Core_models.Bundle {t_Iter__from__result as t_Iter}

include Core_models.Bundle {Iter__from__result as Iter}

include Core_models.Bundle {impl_9__from__result as impl_9}

include Core_models.Bundle {t_IntoIter__from__result as t_IntoIter}

include Core_models.Bundle {IntoIter__from__result as IntoIter}

include Core_models.Bundle {impl_11__from__result as impl_11}

include Core_models.Bundle {impl_12__from__result as impl_12}
