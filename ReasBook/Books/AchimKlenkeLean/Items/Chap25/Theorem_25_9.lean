import Mathlib
import AchimKlenkeLean.Items.Chap25.Definition_25_2

-- Declarations for this item will be appended below by the statement pipeline.

/- Definition 25.2: the textbook vector space `𝓔` of predictable simple integrands is the
canonical submodule `MeasureTheory.predictableSimpleProcesses`, and its canonical image inside
`L²(μ ⊗ dt)` is `MeasureTheory.predictableSimpleProcessL2`. Theorem 25.9 concerns the closure of
that canonical subspace. -/
recall MeasureTheory.predictableSimpleProcesses

open scoped ENNReal NNReal

noncomputable section

namespace MeasureTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "ContinuousFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "Process" => NNReal → Ω → ℝ

/-- The closed submodule `Submodule.topologicalClosure (predictableSimpleProcessL2 ℱ μ)`
realizing the textbook closure `\overline{\mathcal E}` inside `L²(μ ⊗ dt)`. -/
abbrev PredictableSimpleProcessL2Closure (ℱ : ContinuousFiltration) (μ : Measure Ω) :=
  Submodule.topologicalClosure (predictableSimpleProcessL2 ℱ μ)

namespace predictableSimpleProcessL2

variable {ℱ : ContinuousFiltration} {μ : Measure Ω}

/-- The canonical inclusion of `predictableSimpleProcessL2 ℱ μ` into its realized closure
`PredictableSimpleProcessL2Closure ℱ μ`. -/
noncomputable def toClosure (H : predictableSimpleProcessL2 ℱ μ) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  ⟨(H : Lp ℝ 2 (processMeasure μ)),
    Submodule.le_topologicalClosure (predictableSimpleProcessL2 ℱ μ) H.2⟩

/-- Coercing `H.toClosure` to ambient `L²(μ ⊗ dt)` recovers `H`. -/
@[simp] theorem coe_toClosure (H : predictableSimpleProcessL2 ℱ μ) :
    ((H.toClosure : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      (H : Lp ℝ 2 (processMeasure μ)) :=
  rfl

end predictableSimpleProcessL2

/-- A progressively measurable process belongs to the canonical `L²(μ ⊗ dt)` closure of the
predictable simple integrands if its `Lp` class lies in `PredictableSimpleProcessL2Closure ℱ
μ`. -/
def MemPredictableStepProcessClosure (ℱ : ContinuousFiltration) (μ : Measure Ω)
    (H : Process) : Prop :=
  ∃ hH : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ),
    hH.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ

namespace MemPredictableStepProcessClosure

variable {ℱ : ContinuousFiltration} {μ : Measure Ω} {H : Process}

/-- A process in the canonical closure of the predictable simple integrands is globally
square-integrable on `Ω × [0, ∞)`. -/
theorem memLp (hH : MemPredictableStepProcessClosure ℱ μ H) :
    MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ) :=
  Exists.elim hH fun hH_memLp _ ↦ hH_memLp

/-- The `Lp` class of a process in the canonical closure belongs to the realized closure. -/
theorem toLp_mem_closure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    hH.memLp.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨_, hhH⟩ => hhH

/-- A process in the canonical `L²(μ ⊗ dt)` closure of the predictable simple integrands defines
the corresponding point of the realized closure. -/
noncomputable def toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    PredictableSimpleProcessL2Closure ℱ μ :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => ⟨hH_memLp.toLp (processToTimeSpaceFun H), hhH⟩

/-- Coercing `hH.toClosure` to ambient `L²(μ ⊗ dt)` recovers the `Lp` class represented by
`H`. -/
@[simp] theorem coe_toClosure (hH : MemPredictableStepProcessClosure ℱ μ H) :
    ((hH.toClosure : PredictableSimpleProcessL2Closure ℱ μ) :
      Lp ℝ 2 (processMeasure μ)) =
      hH.memLp.toLp (processToTimeSpaceFun H) :=
  match hH with
  | ⟨hH_memLp, hhH⟩ => rfl

end MemPredictableStepProcessClosure

-- Proof sketch: on each finite horizon, first approximate a bounded progressively measurable
-- process by time-averaged continuous adapted processes, then approximate those by predictable
-- simple step processes; finally truncate a general `L²` progressively measurable process and use
-- the global `MemLp` hypothesis to control the truncation error.
/-- Theorem 25.9, core/canonical form: the `Lp` class of a progressively measurable
square-integrable process belongs to the realized closure
`PredictableSimpleProcessL2Closure ℱ μ = \overline{\mathcal E}`. -/
theorem progMeasurable_toLp_mem_predictableSimpleProcessL2_closure
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    hH_memLp.toLp (processToTimeSpaceFun H) ∈ PredictableSimpleProcessL2Closure ℱ μ := sorry

/-- Source-facing bridge form of Theorem 25.9: every progressively measurable real-valued process
with finite `L²(μ ⊗ dt)` norm belongs to the canonical closure predicate
`MemPredictableStepProcessClosure ℱ μ`. -/
theorem progMeasurable_memPredictableStepProcessClosure
    (ℱ : ContinuousFiltration) (μ : Measure Ω) {H : Process}
    (hH_prog : ProgMeasurable ℱ H)
    (hH_memLp : MemLp (processToTimeSpaceFun H) (2 : ℝ≥0∞) (processMeasure μ)) :
    MemPredictableStepProcessClosure ℱ μ H :=
  ⟨hH_memLp, progMeasurable_toLp_mem_predictableSimpleProcessL2_closure ℱ μ hH_prog hH_memLp⟩

end MeasureTheory
