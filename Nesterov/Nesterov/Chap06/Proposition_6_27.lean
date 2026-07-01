import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {X : Type u} {U : Type v}

-- Proof sketch: substitute the defining formulas for `μ₁` and `μ₂` into the assumed duality-gap
-- bound, use `D₁ > 0` and `D₂ > 0` to simplify
-- `Real.sqrt (D₂ / D₁) * D₁ = Real.sqrt (D₁ * D₂)` and
-- `Real.sqrt (D₁ / D₂) * D₂ = Real.sqrt (D₁ * D₂)`, and then factor the common term
-- `opNorm12 * Real.sqrt (D₁ * D₂)`.
/-- Proposition 6.27 [Chapter6_1.json:79]: if
`μ₁ = λ₁ ‖A‖_{1,2} √(D₂ / D₁)` and `μ₂ = λ₂ ‖A‖_{1,2} √(D₁ / D₂)`,
then the assumed duality-gap bound
`f(x̄) - φ(ū) ≤ μ₁ D₁ + μ₂ D₂`
implies the symmetric estimate
`f(x̄) - φ(ū) ≤ (λ₁ + λ₂) ‖A‖_{1,2} √(D₁ D₂)`. The positivity assumptions
`λ₁, λ₂ > 0` and `μ₁, μ₂ > 0` from the source are omitted because they are redundant
for the inequality statement itself. -/
theorem duality_gap_le_symmetric_bound_of_parametrized_smoothing_parameters
    {f : X → ℝ} {φ : U → ℝ} {xBar : X} {uBar : U}
    {D₁ D₂ lambda₁ lambda₂ μ₁ μ₂ opNorm12 : ℝ}
    (hD₁ : 0 < D₁) (hD₂ : 0 < D₂)
    (hμ₁ : μ₁ = lambda₁ * opNorm12 * Real.sqrt (D₂ / D₁))
    (hμ₂ : μ₂ = lambda₂ * opNorm12 * Real.sqrt (D₁ / D₂))
    (hgap : f xBar - φ uBar ≤ μ₁ * D₁ + μ₂ * D₂) :
    f xBar - φ uBar ≤ (lambda₁ + lambda₂) * opNorm12 * Real.sqrt (D₁ * D₂) := sorry

end
