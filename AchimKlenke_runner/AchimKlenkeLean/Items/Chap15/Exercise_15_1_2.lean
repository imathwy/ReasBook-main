import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

noncomputable section

variable {d : ℕ}
variable {μ ν : Measure (EuclideanSpace ℝ (Fin d))}
variable [IsFiniteMeasure μ] [IsFiniteMeasure ν]

-- Exercise 15.1.2 is a `bridge/view` statement: the textbook Laplace transform on the
-- nonnegative orthant is expressed through the owner `mgf` applied to the linear functional
-- `x ↦ -⟪t, x⟫`, and uniqueness is then reduced to `Measure.ext_of_charFun`.
-- Proof sketch: for each nonnegative `t`, push `μ` and `ν` forward along the linear functional
-- `x ↦ ⟪t, x⟫` and rewrite the hypothesis as equality of the corresponding one-dimensional MGFs.
-- Equality on the nonnegative orthant yields equality of the associated characteristic functions,
-- and `Measure.ext_of_charFun` then identifies the measures.
/-- Exercise 15.1.2: finite measures on `[0, ∞)^d` are determined by their Laplace transforms. If
two finite measures on `ℝ^d` are supported on the nonnegative orthant and have the same Laplace
transform at every nonnegative vector `t`, then the measures are equal. -/
theorem eq_of_laplaceTransform_eq_on_nonnegativeOrthant
    (hμ_nonneg : ∀ᵐ x ∂μ, ∀ i, 0 ≤ x i)
    (hν_nonneg : ∀ᵐ x ∂ν, ∀ i, 0 ≤ x i)
    (hL :
      ∀ t : EuclideanSpace ℝ (Fin d),
        (∀ i, 0 ≤ t i) → mgf (fun x ↦ -inner ℝ t x) μ 1 = mgf (fun x ↦ -inner ℝ t x) ν 1) :
    μ = ν := sorry
