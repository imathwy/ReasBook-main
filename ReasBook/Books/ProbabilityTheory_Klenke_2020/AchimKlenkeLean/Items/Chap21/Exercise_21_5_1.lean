import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_35
import ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω} {B : NNReal → Ω → ℝ}

/- Recalled clause (1): the Brownian bridge `Y_t = W_t - t W_1` associated to a Brownian motion
has almost surely continuous sample paths on `[0,1]`. -/
recall brownianBridge_hasAlmostSurelyContinuousPaths

/- Recalled clause (2): the Brownian bridge associated to a Brownian motion is a Gaussian process
on `[0,1]`. -/
recall brownianBridge_isGaussianProcess

/- Recalled clause (3): the covariance kernel of the Brownian bridge is
`Cov[Y_t, Y_s] = (s ∧ t) - st`. -/
recall brownianBridge_covariance_eq

/-- The conditioning event `{ω | B 1 ω ∈ (-ε, ε)}` used in Exercise 21.5.1. -/
def brownianEndpointWindow (B : NNReal → Ω → ℝ) (ε : ℝ) : Set Ω :=
  {ω | B 1 ω ∈ Set.Ioo (-ε) ε}

theorem measurable_brownianFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Measurable (finiteDimensionalEvaluation B fun i ↦ (times i : NNReal)) :=
  measurable_pi_lambda _ fun i ↦ (hB.stronglyMeasurable (times i)).measurable

theorem measurable_brownianBridgeFiniteDimensionalCoordinates
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Measurable (fun ω i ↦ brownianBridge B (times i) ω) := by
  refine measurable_pi_lambda _ ?_
  intro i
  have hB1_meas : Measurable (B 1) := (hB.stronglyMeasurable 1).measurable
  simpa [brownianBridge] using
    ((hB.stronglyMeasurable (times i)).measurable.sub (measurable_const.mul hB1_meas))

theorem brownianEndpointWindow_measure_ne_zero
    (hB : IsBrownianMotion μ B) {ε : ℝ} (hε : 0 < ε) :
    μ (brownianEndpointWindow B ε) ≠ 0 := by
  have hB1 : HasLaw (B 1) (gaussianReal 0 1) μ :=
    hB.gaussian_marginal (by positivity)
  have hB1_meas : Measurable (B 1) := (hB.stronglyMeasurable 1).measurable
  have hgauss_ne : gaussianReal 0 1 (Set.Ioo (-ε) ε) ≠ 0 := by
    intro hzero
    have hvol_zero : (volume : Measure ℝ) (Set.Ioo (-ε) ε) = 0 :=
      gaussianReal_absolutelyContinuous' 0 one_ne_zero hzero
    have hvol_pos : (0 : ENNReal) < (volume : Measure ℝ) (Set.Ioo (-ε) ε) := by
      rw [Real.volume_Ioo, ENNReal.ofReal_pos]
      linarith
    exact hvol_pos.ne' hvol_zero
  have hμeq :
      μ (brownianEndpointWindow B ε) = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
    calc
      μ (brownianEndpointWindow B ε) = μ ((B 1) ⁻¹' Set.Ioo (-ε) ε) := by
        rfl
      _ = Measure.map (B 1) μ (Set.Ioo (-ε) ε) := by
        rw [Measure.map_apply hB1_meas measurableSet_Ioo]
      _ = gaussianReal 0 1 (Set.Ioo (-ε) ε) := by
        rw [hB1.map_eq]
  rw [hμeq]
  exact hgauss_ne

/- For this item:
- `source-facing`: the conditioned finite-dimensional Brownian coordinate law and the matching
  Brownian-bridge finite-dimensional law.
- `core/canonical`: both are `ProbabilityMeasure (Fin (n + 1) → ℝ)` owners.
- `bridge/view`: the conditioning event and the coordinate pushforwards; the Brownian side uses
  the chapter owner `finiteDimensionalEvaluation`, and the right-limit is expressed directly on
  the positive parameter space `Set.Ioi 0` rather than through a second public law family.
-/

/-- The Brownian-bridge finite-dimensional law at the time tuple `times`. -/
def brownianBridgeFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map ⟨μ, hB.isProbabilityMeasure⟩
    (measurable_brownianBridgeFiniteDimensionalCoordinates hB times).aemeasurable

/-- The finite-dimensional law of the Brownian coordinates at `times`, conditioned on the endpoint
event `B₁ ∈ (-ε, ε)` for a positive window radius `ε`. -/
def conditionedBrownianFiniteDimensionalLaw
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) (ε : Set.Ioi (0 : ℝ)) :
    ProbabilityMeasure (Fin (n + 1) → ℝ) :=
  ProbabilityMeasure.map
    ⟨μ[|brownianEndpointWindow B ε], by
      letI : IsProbabilityMeasure μ := hB.isProbabilityMeasure
      exact cond_isProbabilityMeasure (brownianEndpointWindow_measure_ne_zero hB ε.2)⟩
    (measurable_brownianFiniteDimensionalCoordinates hB times).aemeasurable

-- Proof sketch: for each fixed finite tuple of times in `[0,1]`, compute the conditioned Gaussian
-- law of `(W_{t₀}, …, W_{tₙ})` given `W₁ ∈ (-ε, ε)` and let `ε ↓ 0`. The limiting centered
-- Gaussian vector has covariance matrix `((tᵢ : NNReal) ⊓ (tⱼ : NNReal)) - tᵢ tⱼ`, which is the
-- finite-dimensional law of the Brownian bridge from the recalled Gaussianity and covariance
-- statements above.
/-- Exercise 21.5.1: for every finite tuple of times in `[0,1]`, the event-conditioned law of the
Brownian coordinates given `B₁ ∈ (-ε, ε)` converges, as `ε ↓ 0`, to the corresponding
Brownian-bridge finite-dimensional law. -/
theorem conditioned_brownian_finiteDimensionalDistributions_tendsto_brownianBridge
    (hB : IsBrownianMotion μ B) {n : ℕ}
    (times : Fin (n + 1) → BrownianBridgeTime) :
    Tendsto (fun ε : Set.Ioi (0 : ℝ) ↦ conditionedBrownianFiniteDimensionalLaw hB times ε)
      (Filter.comap (Subtype.val : Set.Ioi (0 : ℝ) → ℝ) (𝓝[>] (0 : ℝ)))
      (𝓝 (brownianBridgeFiniteDimensionalLaw hB times)) := sorry

end ProbabilityTheory
