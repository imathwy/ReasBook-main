import Mathlib
import BauschkeLean.Chap03.Definition_3_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

-- Proof sketch: for each `x`, discard the uniqueness part of the Chebyshev hypothesis and keep
-- the realizing best approximation.
/-- Proposition 3.15.1: a Chebyshev set is proximinal. -/
theorem isProximinalIn_of_isChebyshev {X : Type u} [PseudoMetricSpace X] {C : Set X}
    (hC : IsChebyshev C) :
    IsProximinalIn C := by
  intro x
  exact ExistsUnique.exists (hC x)
