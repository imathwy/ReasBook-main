import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- The Brownian bridge is indexed by times in the unit interval `[0,1]`. -/
abbrev BrownianBridgeTime := Set.Icc (0 : NNReal) 1

/-- The covariance kernel of the Brownian bridge on `[0,1]`. -/
def brownianBridgeCovariance (s t : BrownianBridgeTime) : ℝ :=
  (((s : NNReal) ⊓ (t : NNReal)) : ℝ) - (s : ℝ) * (t : ℝ)

/-- Example 21.13: the Brownian bridge associated to a Brownian motion `B` on `[0,1]` is the
process `X_t = B_t - t B_1`, indexed by `t ∈ [0,1]`. -/
def brownianBridge (B : NNReal → Ω → ℝ) : BrownianBridgeTime → Ω → ℝ :=
  fun t ω ↦ B t ω - (t : ℝ) * B 1 ω

/-- Evaluating the Brownian bridge gives the defining formula `B_t - t B_1`. -/
@[simp] theorem brownianBridge_apply (B : NNReal → Ω → ℝ) (t : BrownianBridgeTime) (ω : Ω) :
    brownianBridge B t ω = B t ω - (t : ℝ) * B 1 ω :=
  rfl

variable [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

-- Proof sketch: Brownian motion is a Gaussian process, and for each `t ∈ [0,1]` the variable
-- `B_t - t B_1` is a linear combination of the Gaussian vector `(B_t, B_1)`. Finite-dimensional
-- laws of the bridge are therefore Gaussian by stability of Gaussian laws under linear maps.
/-- The Brownian bridge associated to a Brownian motion is a Gaussian process on `[0,1]`. -/
theorem brownianBridge_isGaussianProcess
    (hB : IsBrownianMotion μ B) :
    IsGaussianProcess (brownianBridge B) μ := sorry

-- Proof sketch: almost every Brownian sample path is continuous on `NNReal`, and
-- `t ↦ (t : ℝ) * B 1 ω` is continuous on `[0,1]`; subtracting these two continuous functions gives
-- a continuous bridge path.
/-- The Brownian bridge associated to a Brownian motion has almost surely continuous paths on
`[0,1]`. -/
theorem brownianBridge_hasAlmostSurelyContinuousPaths
    (hB : IsBrownianMotion μ B) :
    HasAlmostSurelyContinuousPaths μ (brownianBridge B) := sorry

-- Proof sketch: Brownian motion marginals are centered Gaussians, so `B_t` and `B_1` both have
-- mean `0`. Linearity of expectation then gives `E[B_t - t B_1] = 0`.
/-- Every time marginal of the Brownian bridge associated to a Brownian motion is centered. -/
theorem brownianBridge_mean_zero
    (hB : IsBrownianMotion μ B) (t : BrownianBridgeTime) :
    ∫ ω, brownianBridge B t ω ∂μ = 0 := sorry

-- Proof sketch: expand the covariance of
-- `(B_s - s B_1, B_t - t B_1)`, use bilinearity of covariance, and substitute the Brownian-motion
-- covariance identities `cov[B_s, B_t] = s ∧ t`, `cov[B_s, B_1] = s`, `cov[B_1, B_t] = t`, and
-- `cov[B_1, B_1] = 1`. Since `s, t ∈ [0,1]`, this simplifies to `min(s,t) - st`.
/-- The covariance kernel of the Brownian bridge is `Γ(s,t) = min(s,t) - st`. -/
theorem brownianBridge_covariance_eq
    (hB : IsBrownianMotion μ B) (s t : BrownianBridgeTime) :
    cov[brownianBridge B s, brownianBridge B t; μ] = brownianBridgeCovariance s t := sorry

/-- A Brownian bridge on `[0,1]` is a centered Gaussian process with covariance kernel
`Γ(s,t) = min(s,t) - st` and almost surely continuous sample paths. -/
class IsBrownianBridge (μ : Measure Ω) (Y : BrownianBridgeTime → Ω → ℝ) : Prop
    extends IsGaussianProcess Y μ where
  /-- Every marginal of a Brownian bridge has mean `0`. -/
  mean_zero : ∀ t : BrownianBridgeTime, ∫ ω, Y t ω ∂μ = 0
  /-- The covariance kernel of a Brownian bridge is `Γ(s,t) = min(s,t) - st`. -/
  covariance_eq :
    ∀ s t : BrownianBridgeTime, cov[Y s, Y t; μ] = brownianBridgeCovariance s t
  /-- Brownian bridges have almost surely continuous sample paths on `[0,1]`. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ Y

/-- The canonical bridge associated to a Brownian motion is a Brownian bridge. -/
instance {μ : Measure Ω} {B : NNReal → Ω → ℝ} [IsBrownianMotion μ B] :
    IsBrownianBridge μ (brownianBridge B) :=
  ⟨brownianBridge_isGaussianProcess ‹IsBrownianMotion μ B›,
    brownianBridge_mean_zero ‹IsBrownianMotion μ B›,
    brownianBridge_covariance_eq ‹IsBrownianMotion μ B›,
    brownianBridge_hasAlmostSurelyContinuousPaths ‹IsBrownianMotion μ B›⟩

end ProbabilityTheory
