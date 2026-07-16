import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap15.Corollary_15_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open MeasureTheory ProbabilityTheory

namespace MeasureTheory.FiniteMeasure

/-
Theorem 15.6 is `source-facing`: its public content is uniqueness of finite measures on `[0, ∞)`
from their Laplace transforms.

The owner abstractions are:
* `ProbabilityTheory.mgf` for the transform itself;
* `finiteMeasure_eq_of_forall_mem_integral_eq_of_separating_boundedContinuousFamily` from
  Chapter 15 for uniqueness from a separating bounded-continuous family.

Accordingly, the local API stays thin: `laplaceTransform_def` is only the bridge from the textbook
kernel `x ↦ exp (-t x)` to `mgf`, while the main theorem remains the source statement.
-/

/-- The canonical owner `ProbabilityTheory.mgf ((↑) : NNReal → ℝ)` at the parameter `-(t : ℝ)` is
the textbook Laplace-transform integral against `x ↦ exp (-t x)` on `[0, ∞)`. -/
theorem laplaceTransform_def (μ : FiniteMeasure NNReal) (t : NNReal) :
    mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
      ∫ x, Real.exp (-((t : ℝ) * (x : ℝ))) ∂(μ : Measure NNReal) := by
  simp [ProbabilityTheory.mgf, neg_mul]

-- Proof sketch: the forward direction is immediate from equality of measures. For the converse,
-- pass to the one-point compactification of `[0, ∞)`, observe that the functions
-- `x ↦ exp (-λ x)` for `λ ≥ 0` form a multiplicatively closed separating class containing the
-- constants, and apply the separating-class uniqueness theorem from Corollary 15.3.
/-- Theorem 15.6: two finite measures on `[0, ∞)` are equal exactly when their Laplace transforms
agree at every nonnegative parameter. -/
theorem ext_iff_laplaceTransform_eq (μ ν : FiniteMeasure NNReal) :
    μ = ν ↔
      ∀ t : NNReal,
        mgf ((↑) : NNReal → ℝ) (μ : Measure NNReal) (-(t : ℝ)) =
          mgf ((↑) : NNReal → ℝ) (ν : Measure NNReal) (-(t : ℝ)) := sorry

end MeasureTheory.FiniteMeasure
