import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open Set
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]
variable {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ}

-- Proof sketch: for the forward implication, use `cdf_expMeasure_eq` to identify the survival
-- function of `expMeasure θ` as `exp (-θ t)` and then derive the multiplicative tail identity
-- `P[X > t + s] = P[X > t] * P[X > s]`. For the reverse implication, show that this tail identity
-- forces the survival function `t ↦ P {ω | t < X ω}` to solve the multiplicative Cauchy equation
-- on `ℝ≥0`; positivity and measurability then identify it with `exp (-θ t)` for some `θ > 0`,
-- yielding `HasLaw X (expMeasure θ) P`.
/-- Exercise 8.1.1: a strictly positive real random variable on a probability space is
exponentially distributed for some rate if and only if its tail probabilities are memoryless,
equivalently `P[X > t + s] = P[X > t] * P[X > s]` for all `s, t ≥ 0`. -/
theorem strictly_positive_has_exponential_law_iff_memoryless
    (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    (∃ θ > 0, HasLaw X (expMeasure θ) P) ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = P (X ⁻¹' Ioi t) * P (X ⁻¹' Ioi s) := sorry

-- Proof sketch: rewrite the law statement as the fixed-rate multiplicative tail identity
-- `P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]`. This keeps the main characterization in
-- canonical `HasLaw`/measure form and avoids conditioning on null tail events.
/-- A strictly positive real random variable has law `expMeasure θ` with `θ > 0` exactly when its
tail probabilities satisfy the fixed-rate memoryless identity
`P[X > t + s] = expMeasure θ (Ioi t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_expMeasure_tail_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) = expMeasure θ (Ioi t) * P (X ⁻¹' Ioi s) := sorry

-- Proof sketch: combine the canonical tail characterization with the explicit exponential tail
-- formula `expMeasure θ (Ioi t) = exp (-θ t)` for `t ≥ 0`, obtained from `cdf_expMeasure_eq`.
/-- A strictly positive real random variable has exponential law of rate `θ > 0` exactly when its
tail probabilities satisfy the explicit fixed-rate identity
`P[X > t + s] = exp (-θ t) * P[X > s]` for all `s, t ≥ 0`. -/
theorem hasLaw_expMeasure_iff_tail_eq_exp_mul_tail
    {θ : ℝ} (hθ : 0 < θ) (hX_meas : Measurable X) (hX_pos : ∀ᵐ ω ∂P, 0 < X ω) :
    HasLaw X (expMeasure θ) P ↔
      ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
        P (X ⁻¹' Ioi (t + s)) =
          ENNReal.ofReal (Real.exp (-(θ * t))) * P (X ⁻¹' Ioi s) := sorry
