import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_21_11 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

namespace IsBrownianMotion

/-- Every Brownian motion is a Gaussian process. -/
theorem isGaussianProcess
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) :
    IsGaussianProcess X μ := sorry

/-- Every marginal of a Brownian motion has mean zero. -/
theorem mean_zero
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) (t : NNReal) :
    ∫ ω, X t ω ∂μ = 0 := sorry

/-- The covariance kernel of a Brownian motion is `s ∧ t`. -/
theorem covariance_eq
    {μ : Measure Ω} {X : NNReal → Ω → ℝ} (hX : IsBrownianMotion μ X) (s t : NNReal) :
    cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ) := sorry

end IsBrownianMotion

-- Proof sketch: this is the law-level characterization of Brownian motion started at `0`. For the
-- forward direction, combine the Brownian-motion-started-at-zero axioms with the preceding
-- Gaussianity, centeredness, and covariance lemmas together with the `continuous_paths` field.
-- For the reverse direction, use
-- the centered Gaussian-process characterization from the previous remark: covariance `s ∧ t`
-- yields the Brownian finite-dimensional laws, while the continuity assumption gives the path
-- regularity clause.
/-- A process is Brownian motion started from `0` in the almost-sure sense exactly when it is a
continuous centered Gaussian process with covariance kernel `s ∧ t`. -/
theorem isBrownianMotionStartedAt_zero_iff_isCenteredGaussianProcessWithBrownianCovariance
    (μ : Measure Ω) (X : NNReal → Ω → ℝ) :
    IsBrownianMotionStartedAt μ X 0 ↔
      IsGaussianProcess X μ ∧
        (∀ t : NNReal, ∫ ω, X t ω ∂μ = 0) ∧
        (∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) ∧
        HasAlmostSurelyContinuousPaths μ X := sorry

-- Proof sketch: combine the previous almost-sure-start characterization with the additional
-- pointwise initial-value clause `X 0 = 0` required by the standard `IsBrownianMotion` owner.
/-- Theorem 21.11: for a real-valued stochastic process on `[0,∞)`, standard Brownian motion is
equivalent to being a continuous centered Gaussian process with covariance kernel `s ∧ t` together
with the pointwise initial condition `X 0 = 0`. -/
theorem isBrownianMotion_iff_isCenteredGaussianProcessWithBrownianCovariance
    (μ : Measure Ω) (X : NNReal → Ω → ℝ) :
    IsBrownianMotion μ X ↔
      X 0 = 0 ∧
        IsGaussianProcess X μ ∧
          (∀ t : NNReal, ∫ ω, X t ω ∂μ = 0) ∧
          (∀ s t : NNReal, cov[X s, X t; μ] = ((s ⊓ t : NNReal) : ℝ)) ∧
          HasAlmostSurelyContinuousPaths μ X := sorry

end ProbabilityTheory
