import Mathlib
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Theorem_25_4
import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap25.Theorem_25_9

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 25.2: the textbook vector space `𝓔` of predictable simple integrands is the
canonical submodule `MeasureTheory.predictableSimpleProcesses`. Definition 25.10 below uses the
actual `L²(μ ⊗ dt)` image of this source-facing owner and its closure from Theorem 25.9. -/
recall MeasureTheory.predictableSimpleProcesses

open Filter MeasureTheory
open scoped ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal mΩ
local notation "Process" => NNReal → Ω → ℝ

private def predictableSimpleProcessL2ToClosure
    {ℱ : TimeFiltration} {μ : Measure Ω}
    (H : MeasureTheory.predictableSimpleProcessL2 ℱ μ) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  ⟨(H : Lp ℝ 2 (MeasureTheory.processMeasure μ)),
    Submodule.le_topologicalClosure (MeasureTheory.predictableSimpleProcessL2 ℱ μ) H.2⟩

private def processLpCutoffSet (t : NNReal) : Set (Ω × ℝ) :=
  {x | x.2 ≤ (t : ℝ)}

private theorem measurableSet_processLpCutoffSet (t : NNReal) :
    MeasurableSet (processLpCutoffSet (Ω := Ω) t) := by
  simpa [processLpCutoffSet] using measurableSet_le measurable_snd measurable_const

/-- The ambient `L²(μ ⊗ dt)` cutoff operator corresponding to the textbook integrand truncation
`H^(t) = H · 1_[0,t]`. -/
private theorem memLp_processLpCutoffBefore
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    MemLp
      (Set.indicator (processLpCutoffSet (Ω := Ω) t) fun x ↦ f x)
      (2 : ℝ≥0∞) (MeasureTheory.processMeasure μ) :=
  (Lp.memLp f).indicator (measurableSet_processLpCutoffSet (Ω := Ω) t)

private noncomputable def processLpCutoffBeforeFun
    (μ : Measure Ω) (t : NNReal)
    (f : Lp ℝ 2 (MeasureTheory.processMeasure μ)) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) :=
  (memLp_processLpCutoffBefore μ t f).toLp
    (Set.indicator (processLpCutoffSet (Ω := Ω) t) fun x ↦ f x)

private noncomputable def processLpCutoffBefore (μ : Measure Ω) (t : NNReal) :
    Lp ℝ 2 (MeasureTheory.processMeasure μ) →L[ℝ] Lp ℝ 2 (MeasureTheory.processMeasure μ) where
  toLinearMap :=
    { toFun := fun f ↦
        processLpCutoffBeforeFun μ t f
      map_add' := by
        sorry
      map_smul' := by
        sorry
    }
  cont := by
    sorry

private theorem processLpCutoffBefore_mapsTo_closure
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal) :
    Set.MapsTo (processLpCutoffBefore μ t)
      (PredictableSimpleProcessL2Closure ℱ μ : Set (Lp ℝ 2 (processMeasure μ)))
      (PredictableSimpleProcessL2Closure ℱ μ) := by
  have hsimple :
      Set.MapsTo (processLpCutoffBefore μ t)
        (predictableSimpleProcessL2 ℱ μ : Set (Lp ℝ 2 (processMeasure μ)))
        (PredictableSimpleProcessL2Closure ℱ μ) := by
    intro H hH
    sorry
  intro H hH
  have hclosure :
      Set.MapsTo (processLpCutoffBefore μ t)
        (closure (predictableSimpleProcessL2 ℱ μ : Set (Lp ℝ 2 (processMeasure μ))))
        (closure (PredictableSimpleProcessL2Closure ℱ μ :
          Set (Lp ℝ 2 (processMeasure μ)))) :=
    Set.MapsTo.closure hsimple (processLpCutoffBefore μ t).continuous
  have hH' :
      H ∈ closure (predictableSimpleProcessL2 ℱ μ : Set (Lp ℝ 2 (processMeasure μ))) :=
    by
      rw [← Submodule.topologicalClosure_coe]
      exact hH
  have hImage :
      processLpCutoffBefore μ t H ∈
        closure (PredictableSimpleProcessL2Closure ℱ μ :
          Set (Lp ℝ 2 (processMeasure μ))) :=
    hclosure hH'
  have hclosed :
      closure (PredictableSimpleProcessL2Closure ℱ μ :
        Set (Lp ℝ 2 (processMeasure μ))) =
        (PredictableSimpleProcessL2Closure ℱ μ :
          Set (Lp ℝ 2 (processMeasure μ))) :=
    by
      rw [PredictableSimpleProcessL2Closure, Submodule.topologicalClosure_coe]
      exact (Submodule.isClosed_topologicalClosure (predictableSimpleProcessL2 ℱ μ)).closure_eq
  exact hclosed ▸ hImage

private theorem processLpCutoffBefore_mem_closure
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    processLpCutoffBefore μ t H ∈ PredictableSimpleProcessL2Closure ℱ μ :=
  processLpCutoffBefore_mapsTo_closure t H.2

/-- The canonical deterministic cutoff operator `H ↦ H^(t)` on the realized closure
`\overline{\mathcal E} ⊆ L²(μ ⊗ dt)`. -/
noncomputable def _root_.MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal) :
    PredictableSimpleProcessL2Closure ℱ μ →L[ℝ]
      PredictableSimpleProcessL2Closure ℱ μ :=
  ((processLpCutoffBefore μ t).comp (PredictableSimpleProcessL2Closure ℱ μ).subtypeL).codRestrict
    (PredictableSimpleProcessL2Closure ℱ μ)
    (processLpCutoffBefore_mem_closure t)

/-- Coercing the canonical cutoff operator on the closure to ambient `L²(μ ⊗ dt)` gives the
actual time-indicator cutoff `H · 1_[0,t]`. -/
theorem _root_.MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore_coeFn
    {ℱ : TimeFiltration} {μ : Measure Ω} (t : NNReal)
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    (((MeasureTheory.PredictableSimpleProcessL2Closure.cutoffBefore t H :
          PredictableSimpleProcessL2Closure ℱ μ) :
        Lp ℝ 2 (processMeasure μ)) : Ω × ℝ → ℝ) =ᵐ[processMeasure μ]
      Set.indicator {x : Ω × ℝ | x.2 ≤ (t : ℝ)} fun x ↦
        (((H : PredictableSimpleProcessL2Closure ℱ μ) : Lp ℝ 2 (processMeasure μ)) x) := by
  sorry

/-- Definition 25.10: a Brownian Itô integral is the canonical terminal continuous linear map on
`\overline{\mathcal E}` extending the terminal Brownian elementary integral from Definition 25.3
on globally square-integrable predictable simple processes. -/
class BrownianItoIntegral
    (μ : Measure Ω) (ℱ : TimeFiltration) (W : Process)
    extends PredictableSimpleProcessL2Closure ℱ μ →L[ℝ] Lp ℝ 2 μ where
  /-- On an actual globally square-integrable predictable simple process, the closure-side
  terminal map agrees almost everywhere with the Brownian elementary integral from
  Definition 25.3. -/
  ae_eq_brownianElementaryIntegralAtInfinity
      (H : MeasureTheory.PredictableSimpleProcess ℱ)
      (hH : MemLp (MeasureTheory.processToTimeSpaceFun (H : Process)) (2 : ℝ≥0∞)
        (MeasureTheory.processMeasure μ)) :
      ((toContinuousLinearMap
        (predictableSimpleProcessL2ToClosure
          (predictableSimpleProcessToL2 H hH))) :
        Ω → ℝ) =ᵐ[μ]
      MeasureTheory.brownianElementaryIntegralAtInfinity W H

section ItoIntegral

variable {μ : Measure Ω}

/-- Source-facing bridge for Definition 25.10: if a sequence of globally square-integrable
predictable simple processes converges in the canonical closure of
`MeasureTheory.predictableSimpleProcessL2 ℱ μ`, then their terminal Brownian integrals converge
to the Brownian Itô integral of the limit closure point. -/
theorem brownianItoIntegral_tendsto_of_closureApproximation
    {ℱ : TimeFiltration} {W : Process}
    [hIto : BrownianItoIntegral μ ℱ W]
    {Hbar : PredictableSimpleProcessL2Closure ℱ μ}
    {Hs : ℕ → MeasureTheory.PredictableSimpleProcess ℱ}
    {hHs_mem :
      ∀ n,
        MemLp (MeasureTheory.processToTimeSpaceFun ((Hs n : Process))) (2 : ℝ≥0∞)
          (MeasureTheory.processMeasure μ)}
    (hHs :
      Tendsto
        (fun n ↦
          predictableSimpleProcessL2ToClosure
            (predictableSimpleProcessToL2 (Hs n) (hHs_mem n)))
        atTop (nhds Hbar)) :
    Tendsto
      (fun n ↦
        hIto.toContinuousLinearMap
          (predictableSimpleProcessL2ToClosure
            (predictableSimpleProcessToL2 (Hs n) (hHs_mem n))))
      atTop (nhds (hIto.toContinuousLinearMap Hbar)) :=
  (hIto.toContinuousLinearMap.continuous.tendsto Hbar).comp hHs

/-- The textbook process `\tilde I^W(H)` on the canonical closure, defined by
`\tilde I_t^W(H) = I_∞^W(H^(t))`. -/
noncomputable def brownianItoIntegralTruncatedProcess
    {ℱ : TimeFiltration} (W : Process)
    [hIto : BrownianItoIntegral μ ℱ W]
    (H : PredictableSimpleProcessL2Closure ℱ μ) :
    NNReal → Ω → ℝ :=
  fun t ↦ hIto.toContinuousLinearMap
    (PredictableSimpleProcessL2Closure.cutoffBefore t H)

/-- The truncation `H^(τ)` of a process `H` before a stopping time `τ`, given by
`H_t 1_{ {t ≤ τ} }`. This is not the stopped process `t ↦ H (min t τ)`. -/
def processBeforeStoppingTime (H : NNReal → Ω → ℝ) (τ : Ω → ENNReal) :
    NNReal → Ω → ℝ :=
  fun t ↦ Set.indicator {ω | (t : ENNReal) ≤ τ ω} (H t)

omit mΩ in
/-- Evaluating `processBeforeStoppingTime H τ` gives the textbook truncation formula
`H_t 1_{ {t ≤ τ} }`. -/
theorem processBeforeStoppingTime_apply (H : NNReal → Ω → ℝ) (τ : Ω → ENNReal)
    (t : NNReal) (ω : Ω) :
    processBeforeStoppingTime H τ t ω = if (t : ENNReal) ≤ τ ω then H t ω else 0 := by
  by_cases h : (t : ENNReal) ≤ τ ω
  · simp [processBeforeStoppingTime, h]
  · simp [processBeforeStoppingTime, h]

omit mΩ in
/-- If two processes agree at all times up to the stopping time `τ`, then their cutoff
integrands before `τ` coincide. -/
theorem processBeforeStoppingTime_congr
    {H G : NNReal → Ω → ℝ} {τ : Ω → ENNReal}
    (hEq : ∀ (t : NNReal) ω, (t : ENNReal) ≤ τ ω → H t ω = G t ω) :
    processBeforeStoppingTime H τ = processBeforeStoppingTime G τ := by
  funext t ω
  by_cases h : (t : ENNReal) ≤ τ ω
  · simp [processBeforeStoppingTime, h, hEq t ω h]
  · simp [processBeforeStoppingTime, h]

end ItoIntegral

end ProbabilityTheory
