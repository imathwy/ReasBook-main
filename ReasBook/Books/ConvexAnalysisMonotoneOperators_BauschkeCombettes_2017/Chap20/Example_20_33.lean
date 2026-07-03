import Mathlib
import BauschkeLean.Chap03.Proposition_3_12
import BauschkeLean.Chap20.Corollary_20_28
import BauschkeLean.Chap20.Example_20_12

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

section

variable {C : Set H}

-- Proof sketch: Example 20.12 gives monotonicity of the source-facing projector `P[C]`. The
-- owner theorem `setValuedProjector_eq_singleton_projectionPoint` identifies each value of `P[C]`
-- with the singleton induced by `P[C, hC]`, hence with `(P[C, hC]).toSetValuedOperator`; the
-- continuity of `P[C, hC]` comes from Proposition 3.12, and Corollary 20.28 yields maximal
-- monotonicity.
/-- Example 20.33: in a finite-dimensional real Hilbert space, the set-valued projector `P[C]`
onto a Chebyshev set is maximally monotone. -/
theorem setValuedProjector_isMaximallyMonotone_of_isChebyshev (hC : IsChebyshev C) :
    Maximal SetValuedOperator.IsMonotone (P[C]) := by
  have hP : P[C] = (P[C, hC]).toSetValuedOperator := by
    ext x p
    rw [setValuedProjector_eq_singleton_projectionPoint C hC x, Function.toSetValuedOperator_apply]
  rw [hP]
  exact Function.toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
    (P[C, hC])
    (by
      rw [← hP]
      exact setValuedProjector_isMonotone C)
    (continuous_projectionPoint_of_isChebyshev hC)

end
