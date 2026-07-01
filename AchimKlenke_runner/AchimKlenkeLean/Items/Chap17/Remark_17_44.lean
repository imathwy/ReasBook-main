import AchimKlenkeLean.Items.Chap17.Definition_17_42
import AchimKlenkeLean.Items.Chap17.Definition_17_43
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

variable {E : Type u} [MeasurableSpace E] [DiscreteMeasurableSpace E]

-- Proof sketch: combine `Kernel.Invariant (discreteMatrixKernel p) μ` with
-- `comp_discreteMatrixKernel_apply_singleton_eq_tsum` for the source-facing action `μ ⋆ₘ p`, then use
-- `Measure.ext_of_singleton` on the countable discrete state space to pass between equality of
-- measures and equality of all singleton masses.
/-- Remark 17.44 (1): on a countable discrete state space, an invariant measure for the canonical
discrete kernel `discreteMatrixKernel p` is exactly a left eigenvector of the transition matrix
`p` for the eigenvalue `1`, written on the singleton mass function `x ↦ μ {x}`. -/
theorem kernelInvariant_iff_leftEigenvectorAtOne [Countable E]
    (p : E → E → ℝ≥0∞) (μ : Measure E) :
    Kernel.Invariant (discreteMatrixKernel p) μ ↔
      ∀ x : E, ∑' y : E, μ {y} * p y x = μ {x} := sorry

-- Proof sketch: unfold `IsHarmonic`, rewrite the kernel integral with
-- `integral_discreteMatrixKernel_eq_tsum` for the source-facing action `p ⋆ᶠ f`, and use the
-- summability part as the needed integrability witness for each row.
/-- Remark 17.44 (2): a harmonic function for the canonical discrete kernel `discreteMatrixKernel
p` is exactly a right eigenvector of the stochastic transition matrix `p` for the eigenvalue `1`,
with the required summability of the row action recorded explicitly. -/
theorem isHarmonic_iff_rightEigenvectorAtOne
    (p : E → E → ℝ≥0∞) (hp : IsStochasticMatrix p) (f : E → ℝ) :
    IsHarmonic (discreteMatrixKernel p) f ↔
      ∀ x : E, Summable (fun y : E ↦ (p x y).toReal * f y) ∧
        (p ⋆ᶠ f) x = f x := sorry

end ProbabilityTheory
