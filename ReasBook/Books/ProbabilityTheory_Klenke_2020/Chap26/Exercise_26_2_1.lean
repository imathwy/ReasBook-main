import ProbabilityTheory_Klenke_2020.Chap17.Exercise_17_6_2
import ProbabilityTheory_Klenke_2020.Chap26.Example_26_11
import ProbabilityTheory_Klenke_2020.Chap26.Theorem_26_10
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

noncomputable section

universe u

namespace ProbabilityTheory

section SemigroupRealizations

local notation "State" => Fin 1 → ℝ
local notation "PathSpace" => EuclideanPathSpace 1

/-- A weak solution of the one-dimensional SDE with coefficients `σ` and `b`, started from the
deterministic state `x`. -/
abbrev OneDimensionalWeakSolution (x : ℝ) (σ b : NNReal → ℝ → ℝ) :=
  @GeneralizedWeakSDESolution 1 1
    (Measure.dirac (oneDimensionalState x))
    inferInstance
    (oneDimensionalDiffusion σ)
    (oneDimensionalDrift b)

/-- A kernel family on `ℝ` is the transition semigroup of a one-dimensional diffusion with
coefficients `σ` and `b` if its scalar transition probabilities come from a time-homogeneous
strong Markov family on the chapter's one-dimensional state space, and the corresponding path
kernel rows are exactly the path laws of weak solutions unique in law for each deterministic
initial state. -/
def HasOneDimensionalDiffusionSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (σ b : NNReal → ℝ → ℝ) : Prop :=
  ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω)
    (X : NNReal → Ω → State) (P : State → @ProbabilityMeasure Ω mΩ)
    (pathKernel : Kernel State (NNReal → State)),
      let _ : MeasurableSpace Ω := mΩ
      IsTimeHomogeneousMarkovProcess X P pathKernel ∧
      HasStrongMarkovProperty P X pathKernel ∧
    (∀ x : ℝ,
      ∃ L : OneDimensionalWeakSolution.{u} x σ b,
        L.IsWeaklyUnique ∧
          pathKernel (oneDimensionalState x) =
            L.statePathLaw.map ((↑) : PathSpace → NNReal → State)) ∧
    ∀ x : ℝ, ∀ t : NNReal,
      (transitionKernel pathKernel t (oneDimensionalState x)).map
          (fun y ↦ y 0) =
        κ t x

/-- Time-homogeneous one-dimensional diffusion coefficients induce the corresponding source-facing
transition-semigroup predicate. -/
abbrev HasAutonomousOneDimensionalDiffusionSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (σ b : ℝ → ℝ) : Prop :=
  HasOneDimensionalDiffusionSemigroup.{u} κ (fun _ x ↦ σ x) (fun _ x ↦ b x)

/-- A kernel family on `ℝ` is the Ornstein--Uhlenbeck transition semigroup if it is the
time-homogeneous semigroup of the autonomous diffusion with constant diffusion coefficient `σ` and
linear drift `x ↦ b x`. -/
abbrev HasOrnsteinUhlenbeckSemigroup
    (κ : NNReal → Kernel ℝ ℝ) (b σ : ℝ) : Prop :=
  HasAutonomousOneDimensionalDiffusionSemigroup.{u} κ (fun _ ↦ σ) (fun x ↦ b * x)

end SemigroupRealizations

section OneDimensionalDiffusion

variable (C x₀ : ℝ) (σ b : ℝ → ℝ)

/-- The textbook candidate stationary density for a one-dimensional time-homogeneous diffusion
with drift `b`, diffusion coefficient `σ`, reference point `x₀`, and normalizing constant `C`.
-/
def oneDimensionalDiffusionStationaryDensity
    : ℝ → ℝ :=
  fun x ↦
    (1 / C) * (1 / (σ x) ^ 2) *
      Real.exp (∫ r in x₀..x, (2 * b r) / (σ r) ^ 2)

/-- Evaluating the candidate stationary density gives the textbook formula
`C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)`. -/
@[simp]
theorem oneDimensionalDiffusionStationaryDensity_apply
    (x : ℝ) :
    oneDimensionalDiffusionStationaryDensity C x₀ σ b x =
      (1 / C) * (1 / (σ x) ^ 2) *
        Real.exp (∫ r in x₀..x, (2 * b r) / (σ r) ^ 2) :=
  rfl

/-- The measure on `ℝ` with the textbook stationary density for the one-dimensional diffusion. -/
def oneDimensionalDiffusionStationaryMeasure
    : Measure ℝ :=
  volume.withDensity
    (fun x ↦ ENNReal.ofReal (oneDimensionalDiffusionStationaryDensity C x₀ σ b x))

variable {C x₀ : ℝ} {σ b : ℝ → ℝ}

-- Proof sketch: integrate the displayed density over `ℝ`, use the normalization identity
-- `∫ σ(x)⁻² exp (...) dx = C`, and divide by `C`.
/-- The textbook normalizing constant turns the candidate stationary measure into a probability
measure. -/
theorem oneDimensionalDiffusionStationaryMeasure_isProbabilityMeasure
    (hC : 0 < C)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    IsProbabilityMeasure (oneDimensionalDiffusionStationaryMeasure C x₀ σ b) := sorry

/-- The normalized stationary distribution attached to the textbook speed density. -/
abbrev oneDimensionalDiffusionStationaryDistribution
    (C x₀ : ℝ) (σ b : ℝ → ℝ) (hC : 0 < C)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    ProbabilityMeasure ℝ :=
  ⟨oneDimensionalDiffusionStationaryMeasure C x₀ σ b,
    oneDimensionalDiffusionStationaryMeasure_isProbabilityMeasure hC hCeq⟩

end OneDimensionalDiffusion

section OrnsteinUhlenbeck

/-- The stationary variance `σ^2 / (-2b)` of the Ornstein--Uhlenbeck diffusion in the regime
`b < 0`. -/
def ornsteinUhlenbeckStationaryVariance (b σ : ℝ) (hb : b < 0) : NNReal :=
  ⟨σ ^ 2 / (-2 * b), by
    have hden : 0 ≤ -2 * b := by
      nlinarith
    exact div_nonneg (sq_nonneg σ) hden⟩

end OrnsteinUhlenbeck

section CIR

variable (a b γ : ℝ)

-- Proof sketch: positivity of the Gamma shape parameter follows from positivity of `a`, `b`,
-- and `γ`.
/-- The Gamma shape parameter of the CIR stationary law is positive under the natural positivity
assumptions. -/
theorem cirStationaryShape_pos (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ) :
    0 < (2 * a * b) / γ := sorry

-- Proof sketch: positivity of the Gamma rate parameter follows from positivity of `a` and `γ`.
/-- The Gamma rate parameter of the CIR stationary law is positive under the natural positivity
assumptions. -/
theorem cirStationaryRate_pos (ha : 0 < a) (hγ : 0 < γ) :
    0 < (2 * a) / γ := sorry

end CIR

section Jacobi

variable (γ c θ : ℝ)

-- Proof sketch: positivity of the left Beta shape parameter follows from positivity of `c`,
-- `γ`, and `θ`.
/-- The left Beta shape parameter in the Jacobi stationary law is positive. -/
theorem jacobiStationaryLeftShape_pos
    (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1) :
    0 < (2 * c * θ) / γ := sorry

-- Proof sketch: positivity of the right Beta shape parameter follows from positivity of `c`,
-- `γ`, and `1 - θ`, where `0 < 1 - θ` comes from `0 < θ < 1`.
/-- The right Beta shape parameter in the Jacobi stationary law is positive. -/
theorem jacobiStationaryRightShape_pos
    (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1) :
    0 < (2 * c * (1 - θ)) / γ := sorry

end Jacobi

-- Proof sketch: verify the adjoint stationary equation for the density
-- `C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)` and then use the normalization theorem above to
-- view the resulting measure as a probability measure invariant under every time slice `κ t`.
/-- Exercise 26.2.1 (1): for the transition semigroup `κ` of the one-dimensional diffusion
`dX_t = σ(X_t) dW_t + b(X_t) dt`, the normalized density
`C⁻¹ σ(x)⁻² exp (∫_{x₀}^x 2 b(r) / σ(r)^2 dr)` defines an invariant distribution. -/
theorem oneDimensionalDiffusion_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    {C x₀ : ℝ} {σ b : ℝ → ℝ} (hC : 0 < C)
    (hκ : HasAutonomousOneDimensionalDiffusionSemigroup κ σ b)
    (hCeq : ∫ x, oneDimensionalDiffusionStationaryDensity C x₀ σ b x = C) :
    IsInvariantDistributionForSemigroup κ
      (oneDimensionalDiffusionStationaryDistribution C x₀ σ b hC hCeq) := sorry

-- Proof sketch: compute the stationary density of the Ornstein--Uhlenbeck semigroup from the
-- general speed-density formula; for the nondegenerate Ornstein--Uhlenbeck diffusion with
-- `σ > 0`, integrability at infinity is equivalent to the quadratic exponent being negative,
-- which is exactly the condition `b < 0`.
/-- Exercise 26.2.1 (2): for the Ornstein--Uhlenbeck diffusion with `σ > 0`, the transition
semigroup has an invariant distribution if and only if the drift coefficient satisfies `b < 0`. -/
theorem ornsteinUhlenbeck_hasInvariantDistribution_iff
    (κ : NNReal → Kernel ℝ ℝ) (b σ : ℝ) (hσ : 0 < σ)
    (hκ : HasOrnsteinUhlenbeckSemigroup κ b σ) :
    (∃ π : ProbabilityMeasure ℝ, IsInvariantDistributionForSemigroup κ π) ↔ b < 0 := sorry

-- Proof sketch: specialize the general stationary-density formula to constant diffusion
-- coefficient `σ` and linear drift `x ↦ b x`, obtaining the centered Gaussian density with
-- variance `σ^2 / (-2 b)`.
/-- Exercise 26.2.1 (3): when `b < 0`, the invariant distribution of the Ornstein--Uhlenbeck
semigroup is the centered Gaussian law with variance `σ^2 / (-2 b)`. -/
theorem ornsteinUhlenbeck_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (b σ : ℝ) (hb : b < 0)
    (hκ : HasOrnsteinUhlenbeckSemigroup κ b σ) :
    IsInvariantDistributionForSemigroup κ
      (⟨gaussianReal 0 (ornsteinUhlenbeckStationaryVariance b σ hb), inferInstance⟩ :
        ProbabilityMeasure ℝ) := sorry

-- Proof sketch: specialize the stationary-density formula to the CIR coefficients
-- `cirDiffusionCoeff` and `cirDriftCoeff` from Example 26.11, then identify the resulting
-- normalized density with the Gamma density having shape `2ab / γ` and rate `2a / γ`.
/-- Exercise 26.2.1 (4): the invariant distribution of the Cox--Ingersoll--Ross diffusion is the
Gamma distribution with shape `2ab / γ` and rate `2a / γ`. -/
theorem cir_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (a b γ : ℝ) (ha : 0 < a) (hb : 0 < b) (hγ : 0 < γ)
    (hκ :
      HasOneDimensionalDiffusionSemigroup κ
        (cirDiffusionCoeff (Real.toNNReal γ))
        (cirDriftCoeff (Real.toNNReal a) (Real.toNNReal b))) :
    IsInvariantDistributionForSemigroup κ
      (⟨gammaMeasure ((2 * a * b) / γ) ((2 * a) / γ),
        isProbabilityMeasure_gammaMeasure
          (cirStationaryShape_pos a b γ ha hb hγ)
          (cirStationaryRate_pos a γ ha hγ)⟩ : ProbabilityMeasure ℝ) := sorry

-- Proof sketch: apply the one-dimensional stationary-density formula on `(0, 1)` to the Jacobi
-- coefficients `σ(x) = sqrt (γ x (1 - x))` and `b(x) = c (θ - x)`, then identify the normalized
-- density with the displayed Beta law.
/-- Exercise 26.2.1 (5): for the diffusion on `[0,1]` with coefficients
`σ(x) = sqrt (γ x (1 - x))` and `b(x) = c (θ - x)`, the invariant distribution is the Beta law
`β_(2 c θ / γ, 2 c (1 - θ) / γ)`. -/
theorem jacobi_stationaryDistribution_isInvariant
    (κ : NNReal → Kernel ℝ ℝ)
    (γ c θ : ℝ) (hγ : 0 < γ) (hc : 0 < c) (hθ : θ ∈ Set.Ioo 0 1)
    (hκ :
      HasAutonomousOneDimensionalDiffusionSemigroup κ
        (fun x ↦ Real.sqrt (γ * x * (1 - x)))
        (fun x ↦ c * (θ - x))) :
    IsInvariantDistributionForSemigroup κ
      (⟨betaMeasure ((2 * c * θ) / γ) ((2 * c * (1 - θ)) / γ),
        isProbabilityMeasureBeta
          (jacobiStationaryLeftShape_pos γ c θ hγ hc hθ)
          (jacobiStationaryRightShape_pos γ c θ hγ hc hθ)⟩ : ProbabilityMeasure ℝ) := sorry

end ProbabilityTheory
