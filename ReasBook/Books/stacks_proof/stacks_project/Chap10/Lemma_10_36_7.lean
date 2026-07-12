import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

/- Lemma 10.36.7: for a ring homomorphism `R → S`, the elements of `S` that are integral over
`R` form an `R`-subalgebra of `S`. In mathlib this canonical subalgebra is `integralClosure R S`.
-/
recall integralClosure

/- Companion recall: membership in `integralClosure R S` is exactly integrality over `R`. This is
the single-step bridge from the source set-theoretic phrasing to the canonical subalgebra API. -/
recall mem_integralClosure_iff
