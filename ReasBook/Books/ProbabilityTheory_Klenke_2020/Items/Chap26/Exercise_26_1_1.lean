import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_8
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_13
import ProbabilityTheory_Klenke_2020.Items.Chap26.Theorem_26_10

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "Process" => NNReal → Ω → ℝ
local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)

/- Domain-style sampling for Exercise 26.1.1:
* primary domain: one-dimensional Brownian-bridge SDEs and their bridge-process realizations on
  the closed unit interval;
* sampled owner declarations in this domain: `brownianBridge`, `IsBrownianBridge`,
  `HasPathwiseStrongOneDimensionalSolutionRealization`, and `HasUniqueStrongSolution`;
* owner abstraction: the SDE side is organized around the Chapter 26 owners
  `HasPathwiseStrongOneDimensionalSolutionRealization` and `HasUniqueStrongSolution`, while the
  bridge side is organized around the Chapter 21 owner `IsBrownianBridge`;
* primitive data kept here: the source-facing centered process, the closed-interval bridge
  process, the explicit strong-solution candidate, and the scalar drift/diffusion coefficients;
* derived API kept here: the strong-solution realization statement, the unique-strong-solution
  owner theorem, and the Brownian-bridge owner theorem with its companion projections.

Layer triage:
* source-facing: `brownianBridgeSDECenteredProcess`, `brownianBridgeSDEBridgeProcess`,
  `brownianBridgeSDESolutionCandidate`, `brownianBridgeSDEDriftCoeff`, and
  `brownianBridgeSDEDiffusionCoeff`;
* core/canonical: `HasUniqueStrongSolution` and `IsBrownianBridge`;
* bridge/view: the explicit dyadic `limUnder` formula used only to define the candidate and the
  scalar-to-`Fin 1` bridges from Chapter 26. -/

/-- The centered process `Y_t = X_t - a - t (b - a)` attached to a real-valued process `X`. -/
def brownianBridgeSDECenteredProcess (X : Process) (a b : ℝ) : Process :=
  fun t ω ↦ X t ω - a - (t : ℝ) * (b - a)

-- Proof sketch: unfold `brownianBridgeSDECenteredProcess`; the value at `(t, ω)` is exactly the
-- affine recentering `X_t(ω) - a - t (b - a)`.
/-- Evaluating the centered process subtracts the affine interpolation between `a` and `b`. -/
theorem brownianBridgeSDECenteredProcess_apply
    (X : Process) (a b : ℝ) (t : NNReal) (ω : Ω) :
    brownianBridgeSDECenteredProcess X a b t ω =
      X t ω - a - (t : ℝ) * (b - a) := sorry

/-- The unit-interval version of the centered bridge process, with value `0` forced at time `1`.
This is the closed-interval process compared with the Brownian-bridge API of Chapter 21. -/
def brownianBridgeSDEBridgeProcess (X : Process) (a b : ℝ) :
    BrownianBridgeTime → Ω → ℝ :=
  fun t ω ↦
    if (t : NNReal) < 1 then
      brownianBridgeSDECenteredProcess X a b t ω
    else
      0

-- Proof sketch: unfold `brownianBridgeSDEBridgeProcess`; on the branch `(t : NNReal) < 1`, the
-- definition is exactly the centered process.
/-- Away from the endpoint `t = 1`, the closed-interval bridge process agrees with the centered
process `X_t - a - t (b - a)`. -/
theorem brownianBridgeSDEBridgeProcess_of_lt_one
    (X : Process) (a b : ℝ) (t : BrownianBridgeTime) (ht : (t : NNReal) < 1) :
    brownianBridgeSDEBridgeProcess X a b t =
      brownianBridgeSDECenteredProcess X a b t := sorry

-- Proof sketch: unfold `brownianBridgeSDEBridgeProcess`; at the endpoint `t = 1`, the `if`-test
-- fails and the definition returns `0`.
/-- The closed-interval bridge process is pinned at `0` at time `1`. -/
theorem brownianBridgeSDEBridgeProcess_one (X : Process) (a b : ℝ) :
    brownianBridgeSDEBridgeProcess X a b ⟨1, by simp⟩ = 0 := sorry

private def brownianBridgeSDEDyadicBridgeTerm
    (W : Process) (t : Set.Iio (1 : NNReal)) (n : ℕ) : Ω → ℝ :=
  fun ω ↦
    Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n (t : NNReal))) fun k ↦
      (((1 : ℝ) - (t : ℝ)) / ((1 : ℝ) - (dyadicPartitionSequence n k : ℝ))) *
        (W (partitionNextPointUpTo dyadicPartitionSequence n k (t : NNReal)) ω -
          W (dyadicPartitionSequence n k) ω)

/-- The canonical candidate for the solution of
`dX_t = ((b - X_t)/(1 - t)) dt + dW_t`, obtained by adding the affine interpolation from `a` to
`b` to the explicit dyadic-limit bridge term and extending the process by the endpoint value `b`
at time `1` and beyond. -/
def brownianBridgeSDESolutionCandidate (a b : ℝ) (W : Process) : Process :=
  fun t ω ↦
    if ht : t < 1 then
      a + (t : ℝ) * (b - a) +
        limUnder atTop (fun n ↦ brownianBridgeSDEDyadicBridgeTerm W ⟨t, ht⟩ n ω)
    else
      b

-- Proof sketch: unfold `brownianBridgeSDESolutionCandidate`; on the interval `t < 1`, the
-- candidate is exactly the affine term plus the dyadic-limit bridge sum.
/-- For `t < 1`, the canonical bridge-SDE candidate is the affine interpolation from `a` to `b`
plus the explicit dyadic-limit bridge term. -/
theorem brownianBridgeSDESolutionCandidate_of_lt_one
    (a b : ℝ) (W : Process) {t : NNReal} (ht : t < 1) :
    brownianBridgeSDESolutionCandidate a b W t =
      fun ω ↦
        a + (t : ℝ) * (b - a) +
          limUnder atTop
            (fun n ↦
              Finset.sum
                (Finset.range (partitionBoundIndex dyadicPartitionSequence n t)) fun k ↦
                  (((1 : ℝ) - (t : ℝ)) / ((1 : ℝ) - (dyadicPartitionSequence n k : ℝ))) *
                    (W (partitionNextPointUpTo dyadicPartitionSequence n k t) ω -
                      W (dyadicPartitionSequence n k) ω)) :=
  sorry

-- Proof sketch: unfold `brownianBridgeSDESolutionCandidate`; when `1 ≤ t`, the defining `if`
-- returns the endpoint value `b`.
/-- For `t ≥ 1`, the canonical bridge-SDE candidate is frozen at the boundary value `b`. -/
theorem brownianBridgeSDESolutionCandidate_of_one_le
    (a b : ℝ) (W : Process) {t : NNReal} (ht : 1 ≤ t) :
    brownianBridgeSDESolutionCandidate a b W t = fun _ ↦ b := sorry

/-- The one-dimensional drift coefficient for the Brownian-bridge SDE. It agrees with
`(b - x) / (1 - t)` on `[0,1)` and vanishes afterwards, matching the frozen continuation of the
explicit solution candidate. -/
def brownianBridgeSDEDriftCoeff (b : ℝ) : NNReal → ℝ → ℝ :=
  fun t x ↦
    if t < 1 then
      (b - x) / ((1 : ℝ) - t)
    else
      0

/-- The one-dimensional diffusion coefficient for the Brownian-bridge SDE. It is `1` on `[0,1)`
and `0` after time `1`, so the chapter's global strong-solution owner matches the stopped source
equation. -/
def brownianBridgeSDEDiffusionCoeff : NNReal → ℝ → ℝ :=
  fun t _ ↦ if t < 1 then 1 else 0

/-- On the source interval `[0,1)`, the drift coefficient is the singular textbook drift
`(b - x) / (1 - t)`. -/
theorem brownianBridgeSDEDriftCoeff_of_lt_one (b x : ℝ) {t : NNReal} (ht : t < 1) :
    brownianBridgeSDEDriftCoeff b t x = (b - x) / ((1 : ℝ) - t) := by
  simp [brownianBridgeSDEDriftCoeff, ht]

/-- On the source interval `[0,1)`, the diffusion coefficient is the constant value `1`. -/
theorem brownianBridgeSDEDiffusionCoeff_of_lt_one {t : NNReal} (ht : t < 1) (x : ℝ) :
    brownianBridgeSDEDiffusionCoeff t x = 1 := by
  simp [brownianBridgeSDEDiffusionCoeff, ht]

section BrownianBridgeStrongSolutions

variable {ℱ : TimeFiltration} {μ : Measure Ω} [IsProbabilityMeasure μ]

-- Proof sketch: substitute the explicit dyadic-limit formula for the candidate process into the
-- cutoff coefficients agree with the textbook Brownian-bridge SDE on `[0,1)` and freeze the
-- process after time `1`.
/-- Exercise 26.1.1 (1): the canonical process built from the affine term and the dyadic-limit
bridge term is a pathwise strong-solution realization, in the sense of
`HasPathwiseStrongOneDimensionalSolutionRealization`, of the Brownian-bridge SDE with
coefficients `σ(t, x) = 1_[0,1)(t)` and
`b(t, x) = 1_[0,1)(t) (b - x) / (1 - t)`. On the source interval `[0,1)`, this is exactly
`dX_t = ((b - X_t)/(1 - t)) dt + dW_t` with initial value `X_0 = a`. -/
theorem brownianBridgeSDESolutionCandidate_isStrongSolution
    {W : Process}
    (hW : IsOneDimensionalBrownianMotionWithFiltration ℱ μ W)
    (a b : ℝ) :
    HasPathwiseStrongOneDimensionalSolutionRealization
      ℱ μ
      (brownianBridgeSDEDriftCoeff b) brownianBridgeSDEDiffusionCoeff
      (fun _ ↦ a)
      W
      (brownianBridgeSDESolutionCandidate a b W) :=
  sorry

-- Proof sketch: the explicit candidate from part (1) gives existence on every Brownian input,
-- and the same integrating-factor argument as in the fixed-space uniqueness proof upgrades to the
-- Chapter 26 owner `HasUniqueStrongSolution` for the Dirac law at `a`.
/-- Exercise 26.1.1 (2): the Brownian-bridge SDE has a unique strong solution in the canonical
Chapter 26 sense for the deterministic initial law `δ_a`. -/
theorem brownianBridgeSDE_hasUniqueStrongSolution (a b : ℝ) :
    HasUniqueStrongSolution
      GeneralizedSDEBrownianMotion
      (SolvesStrongGeneralizedSDE
        (oneDimensionalDiffusion brownianBridgeSDEDiffusionCoeff)
        (oneDimensionalDrift (brownianBridgeSDEDriftCoeff b)))
      (Measure.dirac (oneDimensionalState a)) := sorry

end BrownianBridgeStrongSolutions

-- Proof sketch: rewrite the candidate as `a + t (b - a) + Y_t`, where the bridge term `Y_t`
-- tends to `0` almost surely as `t ↑ 1`; the affine part tends to `b`, so the full solution tends
-- to `b`.
/-- Exercise 26.1.1 (3): the canonical strong solution satisfies
`X_1 := lim_{t \uparrow 1} X_t = b` almost surely. -/
theorem brownianBridgeSDESolutionCandidate_tendsto_b_ae
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    ∀ᵐ ω ∂μ,
      Tendsto
        (fun t : Set.Iio (1 : NNReal) ↦ brownianBridgeSDESolutionCandidate a b W t ω)
        atTop
        (𝓝 b) := sorry

-- Proof sketch: the centered process of the explicit strong solution has the Brownian-bridge
-- Gaussian law and covariance from the standard Itô-kernel computation, and part (3) provides the
-- endpoint pinning needed to extend the continuity to all of `[0,1]`.
/-- Exercise 26.1.1 (4): the centered bridge process of the canonical strong solution is a
Brownian bridge in the Chapter 21 owner sense. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    IsBrownianBridge μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b) := sorry

/-- Companion to Exercise 26.1.1 (4): the centered bridge process of the canonical strong
solution is Gaussian. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_isGaussianProcess
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    IsGaussianProcess
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b)
      μ := by
  exact
    (brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW a b).toIsGaussianProcess

/-- Companion to Exercise 26.1.1 (4): every marginal of the centered bridge process has mean
`0`. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_mean_zero
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ)
    (t : BrownianBridgeTime) :
    ∫ ω,
      brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b t ω ∂μ = 0 :=
  (brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW a b).mean_zero t

/-- Companion to Exercise 26.1.1 (4): the centered bridge process has the canonical
Brownian-bridge covariance kernel. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_covariance_eq
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ)
    (s t : BrownianBridgeTime) :
    cov[
      brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b s,
      brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b t;
      μ] = brownianBridgeCovariance s t :=
  (brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW a b).covariance_eq s t

/-- Companion to Exercise 26.1.1 (4): the centered bridge process has almost surely continuous
sample paths on `[0,1]`. -/
theorem brownianBridgeSDESolutionCandidate_bridgeProcess_hasAlmostSurelyContinuousPaths
    {μ : Measure Ω} {W : Process} (hW : IsBrownianMotion μ W) (a b : ℝ) :
    HasAlmostSurelyContinuousPaths
      μ
      (brownianBridgeSDEBridgeProcess (brownianBridgeSDESolutionCandidate a b W) a b) :=
  (brownianBridgeSDESolutionCandidate_bridgeProcess_isBrownianBridge hW a b).continuous_paths

end ProbabilityTheory
