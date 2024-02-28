use crate::prelude::*;
use crate::sinto_as_usize;

sinto_as_usize!(rustc_middle::ty, DebruijnIndex);
sinto_as_usize!(rustc_middle::ty, UniverseIndex);
sinto_as_usize!(rustc_middle::ty, BoundVar);
sinto_as_usize!(rustc_middle::middle::region, FirstStatementIndex);
sinto_as_usize!(rustc_hir::hir_id, ItemLocalId);
sinto_as_usize!(rustc_target::abi, VariantIdx);
sinto_as_usize!(rustc_middle::ty, RegionVid);
