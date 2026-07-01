import FirstOrderMethodsinOptimization.Chap08.Definition_8_16

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 11.1 is a `bridge/view` recall of the Chapter 8 finite-sum model. Domain sampling:
- `finite_sum_objective` is the upstream chapter owner for the aggregate objective
  `x ↦ ∑ i, f i x`;
- `finite_sum_objective_apply` is its pointwise evaluation formula;
- `isMinOn_finite_sum_objective_iff` is the canonical feasible-set bridge to the explicit sum.

The primitive data here is only the finite family `f : Fin m → E → α`; the aggregate objective
and the minimization reformulation are already owned upstream with the exact interface needed for
Definition 11.1. This file therefore recalls those declarations directly instead of keeping a
parallel Chapter 11 alias. -/
recall finite_sum_objective
recall finite_sum_objective_apply
recall isMinOn_finite_sum_objective_iff
