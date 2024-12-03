(** This phase makes sure the items don't yield any cycle,
namespace-wise. It does so by creating namespaces we call bundles, in
which we regroup definitions that would otherwise yield cycles. *)

module Make : Phase_utils.UNCONSTRAINTED_MONOMORPHIC_PHASE
