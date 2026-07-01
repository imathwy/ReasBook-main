import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

variable (s : ℕ → ℚ)

/- Definition 1.2.1: for a rational sequence `s`, the textbook notion of a `ℚ`-Cauchy sequence is
the canonical mathlib predicate `CauchySeq s`. -/
#check CauchySeq s

/- The textbook condition that the tails of the sequence have arbitrarily small radius is expressed
in mathlib by the standard metric characterization of Cauchy sequences: sufficiently far out in the
sequence, any two terms are arbitrarily close. -/
#check (Metric.cauchySeq_iff :
  CauchySeq s ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (s m) (s n) < ε)
