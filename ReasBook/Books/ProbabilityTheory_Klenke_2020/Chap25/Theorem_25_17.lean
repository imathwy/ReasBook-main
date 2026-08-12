import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Chap09.Definition_9_7
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_4
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_10
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_14
import ProbabilityTheory_Klenke_2020.Chap25.Definition_25_16
import ProbabilityTheory_Klenke_2020.Chap25.Lemma_25_15
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_4

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- A process `I` is the Brownian local Itô integral of `H` against `W` if `H` is locally
square-integrable, `W` is Brownian, `I` starts from `0`, `I` has almost surely continuous sample
paths, and `I` is obtained along some stopping-time approximation to `∞`, together with cutoff
integrands in the canonical closure of the predictable step processes, as the almost-sure
pointwise limit of the canonical Brownian Itô processes coming from a terminal Brownian Itô map in
the sense of Definition 25.10. This keeps Theorem 25.17 tied to the canonical upstream Brownian-
Itô API rather than to an unconstrained process-level realization operator. -/
class IsBrownianLocalItoIntegral
    (ℱ : TimeFiltration) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W H I : Process) : Prop where
  /-- The integrand `H` belongs to `\mathcal E_{\mathrm{loc}}`. -/
  locally_square_integrable : IsLocallySquareIntegrableProcess ℱ μ H
  /-- The driver `W` is a Brownian motion. -/
  brownian_motion : IsBrownianMotion μ W
  /-- A Brownian local Itô integral starts from `0`. -/
  zero : I 0 = 0
  /-- The realized local Itô integral process has almost surely continuous sample paths. -/
  continuous_paths : HasAlmostSurelyContinuousPaths μ I
  /-- Along some Itô localizing sequence for `H`, the canonical Brownian Itô processes of the
  cutoff integrands converge almost surely at each deterministic time to `I`. -/
  canonical_local_integral :
    ∃ hIto : BrownianItoIntegral μ ℱ W,
      ∃ τSeq : ℕ → Ω → ENNReal,
        IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ ∞) ∧
          ∃ hτClosure : ∀ n : ℕ,
            MemPredictableStepProcessClosure ℱ μ
              (processBeforeStoppingTime H (τSeq n)),
            ∀ t : NNReal,
              ∀ᵐ ω ∂μ,
                Tendsto
                  (fun n ↦
                    hIto.toContinuousLinearMap
                      (PredictableSimpleProcessL2Closure.cutoffBefore t
                        (MeasureTheory.MemPredictableStepProcessClosure.toClosure
                          (hτClosure n))) ω)
                  atTop
                  (𝓝 (I t ω))

namespace BrownianLocalItoIntegral

/-- Any canonical Brownian local Itô realization also satisfies the source-facing Definition 25.16
relation. This keeps Definition 25.16 available only as a thin bridge, not as the theorem-facing
owner. -/
theorem isBrownianLocalItoIntegralProcess_of_isBrownianLocalItoIntegral
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ] {W H I : Process}
    (hI : _root_.ProbabilityTheory.IsBrownianLocalItoIntegral ℱ μ W H I) :
    _root_.ProbabilityTheory.IsBrownianLocalItoIntegralProcess ℱ μ W H I := by
  exact
    { locally_square_integrable := hI.locally_square_integrable
      zero := hI.zero
      canonical_local_integral := hI.canonical_local_integral }

end BrownianLocalItoIntegral

-- Proof sketch: use Lemma 25.15 to choose a localizing sequence for `H`. For each deterministic
-- time `t`, Lemma 25.13(ii) shows that the stopped integral processes agree on the events
-- `{t ≤ τₙ}`; since these events exhaust almost all sample points, Definition 25.16 yields a
-- well-defined limit relation, and Theorem 25.11 gives continuity of the resulting realization.
-- Uniqueness follows by comparing two continuous realizations against the same localizing
-- sequence.
/-- Theorem 25.17 (1): for `H ∈ \mathcal E_{\mathrm{loc}}`, there exists a Brownian local Itô
integral process `I_t = \int_0^t H_s dW_s` with almost surely continuous sample paths, and any two
such continuous realizations are modifications of one another. -/
theorem exists_unique_localBrownianIntegralProcess_of_isLocallySquareIntegrableProcess
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ] {W H : Process}
    (hW : IsBrownianMotion μ W)
    (hH : IsLocallySquareIntegrableProcess ℱ μ H) :
    ∃ I : Process,
      IsBrownianLocalItoIntegral ℱ μ W H I ∧
        ∀ J : Process,
          IsBrownianLocalItoIntegral ℱ μ W H J →
            AreModifications μ I J := sorry

-- Proof sketch: the assumption `E[∫₀^τ H_s² ds] < ∞` makes the cutoff integrand `H^(τ)`
-- globally square-integrable. Apply the global Itô-integral result to `H^(τ)` and identify the
-- stopped local integral `t ↦ ∫₀^{τ∧t} H_s dW_s` with the integral of `H^(τ)`.
/-- Theorem 25.17 (2): if `τ` is a stopping time and `H` has finite stopped second moment on
`[0, τ]`, then the stopped process of any almost surely continuous Brownian local Itô realization
of Definition 25.16 is a continuous `𝓕`-martingale that is uniformly bounded in `L²(μ)`. -/
theorem stopped_localBrownianIntegral_isL2BoundedContinuousMartingale
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ] {W H I : Process} {τ : Ω → ENNReal}
    (hI : IsBrownianLocalItoIntegral ℱ μ W H I)
    (hτ : IsStoppingTime ℱ τ)
    (hfinite : HasFiniteStoppedSecondMoment μ H τ) :
    Martingale (stoppedProcess I τ) ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ (stoppedProcess I τ) ∧
      ∃ C : ℝ≥0,
        ∀ t : NNReal,
          eLpNorm (stoppedProcess I τ t) 2 μ ≤ (C : ℝ≥0∞) := sorry

-- Proof sketch: apply part (2) to the deterministic stopping times `τ(ω) = T`, so each stopped
-- process on `[0, T]` is an `L²`-bounded continuous martingale. Letting `T` vary yields the
-- martingale property, almost-sure continuity, and square integrability of every time marginal of
-- the full local Itô integral process.
/-- Theorem 25.17 (3): if `E[\int_0^T H_s^2 ds] < \infty` for every `T > 0`, then the Brownian
local Itô integral process `t ↦ \int_0^t H_s dW_s` is a square-integrable continuous martingale. -/
theorem localBrownianIntegral_isSquareIntegrableContinuousMartingale
    {ℱ : TimeFiltration} [IsProbabilityMeasure μ] {W H I : Process}
    (hI : IsBrownianLocalItoIntegral ℱ μ W H I)
    (hfinite :
      ∀ T : NNReal, 0 < T → HasFiniteStoppedSecondMoment μ H fun _ ↦ (T : ENNReal)) :
    Martingale I ℱ μ ∧
      HasAlmostSurelyContinuousPaths μ I ∧
      IsSquareIntegrableProcess I μ := sorry

end ProbabilityTheory
