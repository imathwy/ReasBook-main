import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: identify the event `{ω | X ω < Y ω}` with the region below the diagonal for the
-- joint law of `(X, Y)`, use independence and the two exponential marginals to factor the joint
-- density, integrate over `{(x, y) | 0 ≤ x ∧ x < y}`, and simplify the resulting elementary
-- integral.
/-- Exercise 2.2.1: if `X` and `Y` are independent real random variables with exponential laws of
rates `θ` and `ρ`, then the probability that `X < Y` is `θ / (θ + ρ)`. -/
theorem indep_exponential_lt_probability
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ} {θ ρ : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hY : HasLaw Y (expMeasure ρ) P)
    (hXY : X ⟂ᵢ[P] Y)
    (hθ : 0 < θ) (hρ : 0 < ρ) :
    P.real {ω | X ω < Y ω} = θ / (θ + ρ) := sorry
