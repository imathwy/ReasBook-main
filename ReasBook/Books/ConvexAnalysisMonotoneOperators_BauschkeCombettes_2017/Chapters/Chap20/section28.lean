import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_20_28 (from Chap20) -/
open scoped InnerProductSpace

universe u

namespace Function

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

-- Proof sketch: continuity of `A` implies continuity of each affine slice
-- `α ↦ A (x + α • y)`, and composing with the continuous inner-product pairing against `z`
-- yields the required right-continuity on `Set.Ioi 0`.
/-- A continuous single-valued operator on a real Hilbert space is hemicontinuous. -/
theorem _root_.Continuous.isHemicontinuous {A : H → H} (hA_cont : Continuous A) :
    A.IsHemicontinuous := by
  intro x y z
  have hline : Continuous (fun α : ℝ ↦ x + α • y) := by
    exact continuous_const.add (continuous_id.smul continuous_const)
  have hslice : Continuous (fun α : ℝ ↦ ⟪z, A (x + α • y)⟫_ℝ) := by
    exact continuous_const.inner (hA_cont.comp hline)
  exact hslice.continuousWithinAt

-- Proof sketch: a continuous operator is hemicontinuous by
-- `Continuous.isHemicontinuous`, so Proposition 20.27 applies to the associated
-- singleton-valued set-valued operator.
/-- Corollary 20.28: a monotone continuous single-valued operator on a real Hilbert space is
maximally monotone when regarded as its associated singleton-valued set-valued operator. -/
theorem toSetValuedOperator_isMaximallyMonotone_of_monotone_continuous
    (A : H → H) (hA_mono : A.toSetValuedOperator.IsMonotone) (hA_cont : Continuous A) :
    Maximal SetValuedOperator.IsMonotone A.toSetValuedOperator :=
  toSetValuedOperator_isMaximallyMonotone_of_monotone_hemicontinuous A hA_mono
    hA_cont.isHemicontinuous

end Function
