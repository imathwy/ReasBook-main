import Mathlib
import AchimKlenkeLean.Items.Chap21.Remark_21_67
import AchimKlenkeLean.Items.Chap25.Definition_25_10
import AchimKlenkeLean.Items.Chap25.Definition_25_14

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory
open scoped ENNReal Topology

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {μ : Measure Ω}

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

variable {ℱ : TimeFiltration} {H : Process}

/-- A process has finite stopped second moment up to `τ` if the expected square integral on the
random interval `[0, τ]` is finite. -/
def HasFiniteStoppedSecondMoment
    (μ : Measure Ω) (H : Process) (τ : Ω → ENNReal) : Prop :=
  ∫⁻ ω,
      (∫⁻ s, ENNReal.ofReal ((H s.toNNReal ω) ^ 2)
        ∂(volume.restrict {s : ℝ | 0 ≤ s ∧ ENNReal.ofReal s ≤ τ ω}))
    ∂μ <
    ∞

/-- Lemma 25.15: every process in `\mathcal E_{\mathrm{loc}}` admits a sequence of stopping times
increasing almost surely to `∞` such that the expected stopped second moment of `H` on
`[0, τₙ]` is finite at every stage. -/
theorem exists_localizingSequenceToInfinity_of_isLocallySquareIntegrableProcess
    (hH : IsLocallySquareIntegrableProcess ℱ μ H) :
    ∃ τSeq : ℕ → Ω → ENNReal,
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ ∞) ∧
        ∀ n : ℕ, HasFiniteStoppedSecondMoment μ H (τSeq n) := by
  sorry

-- Proof sketch: progressive measurability of `H` and the stopping-time cutoff construction give
-- progressive measurability of `H·1_{[0,τ]}`, while the finite stopped second-moment hypothesis
-- gives the global `L²(μ ⊗ dt)` bound needed for Theorem 25.9.
/-- A progressively measurable process with finite stopped second moment up to `τ` yields a cutoff
integrand `H·1_{[0,τ]}` in the canonical closure of the predictable step processes. -/
theorem memPredictableStepProcessClosure_processBeforeStoppingTime_of_progMeasurable
    (hH : ProgMeasurable ℱ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ)
    (hfinite : HasFiniteStoppedSecondMoment μ H τ) :
    MemPredictableStepProcessClosure ℱ μ
      (processBeforeStoppingTime H τ) := sorry

/-- Derived bridge for later Brownian Itô constructions: the stopping-time approximation from
Lemma 25.15 yields cutoff integrands lying in the canonical closure
`\overline{\mathcal E}`. -/
theorem exists_cutoffClosureSequenceToInfinity_of_isLocallySquareIntegrableProcess
    (hH : IsLocallySquareIntegrableProcess ℱ μ H) :
    ∃ τSeq : ℕ → Ω → ENNReal,
      IsStoppingTimeApproximationUpTo ℱ μ τSeq (fun _ ↦ ∞) ∧
        ∀ n : ℕ,
          MemPredictableStepProcessClosure ℱ μ
            (processBeforeStoppingTime H (τSeq n)) := by
  sorry

namespace MeasureTheory.MemPredictableStepProcessClosure

/-- A globally admissible integrand remains in the canonical closure after cutoff at a stopping
time. -/
theorem processBeforeStoppingTime
    {ℱ : TimeFiltration} {μ : Measure Ω} {H : Process}
    (hH : MemPredictableStepProcessClosure ℱ μ H)
    {τ : Ω → ENNReal}
    (hτ : IsStoppingTime ℱ τ) :
    MemPredictableStepProcessClosure ℱ μ (ProbabilityTheory.processBeforeStoppingTime H τ) := by
  sorry

end MeasureTheory.MemPredictableStepProcessClosure

end ProbabilityTheory
