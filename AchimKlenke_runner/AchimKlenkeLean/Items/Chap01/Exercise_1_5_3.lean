import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

-- Proof sketch: combine the canonical scaling law `gaussianReal_const_mul` with the translation
-- law `gaussianReal_add_const`; the hypothesis `a ≠ 0` matches the textbook formulation coming
-- from the transformation formula.
/-- Scaling and translating a Gaussian random variable preserves Gaussianity, with the expected
transformed mean and variance. -/
theorem hasLaw_gaussian_affine
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := sorry

/-- Exercise 1.5.3 (1): If a real random variable `X` has Gaussian law `N(μ, σ^2)`, then the
affine transform `aX + b` has Gaussian law `N(aμ + b, a^2σ^2)` for `a ≠ 0`. -/
theorem gaussian_affine_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {μ σ a b : ℝ}
    (hX : HasLaw X (gaussianReal μ ⟨σ ^ 2, sq_nonneg σ⟩) P)
    (_ha : a ≠ 0) :
    HasLaw (fun ω ↦ a * X ω + b)
      (gaussianReal (a * μ + b) ⟨(a * σ) ^ 2, sq_nonneg (a * σ)⟩) P := by
  simpa using hasLaw_gaussian_affine hX

-- Proof sketch: apply the one-dimensional transformation formula to the density defining
-- `expMeasure θ` under the measurable equivalence `x ↦ a * x`, using `a > 0` to preserve the
-- support on `[0, ∞)` and to rewrite the transformed density as the exponential density with rate
-- `θ / a`.
/-- Multiplying an exponentially distributed random variable by a positive scalar divides its rate
by that scalar. -/
theorem hasLaw_exponential_pos_mul
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ) (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := sorry

/-- Exercise 1.5.3 (2): If a real random variable `X` has exponential law with rate `θ` and
`a > 0`, then the scaled variable `aX` has exponential law with rate `θ / a`. -/
theorem exponential_pos_mul_hasLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}
    {θ a : ℝ}
    (hX : HasLaw X (expMeasure θ) P)
    (hθ : 0 < θ)
    (ha : 0 < a) :
    HasLaw (fun ω ↦ a * X ω) (expMeasure (θ / a)) P := by
  exact hasLaw_exponential_pos_mul hX hθ ha
