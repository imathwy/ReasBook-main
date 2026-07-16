import ProbabilityTheory_Klenke_2020.AchimKlenkeLean.Items.Chap20.Definition_20_34
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/-- A finite measurable partition generates the ambient σ-algebra if that σ-algebra is generated
by all backward iterates of its atoms. -/
def is_generator (τ : Ω → Ω) (part : MeasurableFinpartition Ω) : Prop :=
  MeasurableSpace.generateFrom
      (⋃ n : ℕ,
        Set.range fun A : part.parts ↦
          (τ^[n]) ⁻¹' ((A.1 : Subtype (MeasurableSet : Set Ω → Prop)) : Set Ω)) =
    ‹MeasurableSpace Ω›

-- Proof sketch: this is the Kolmogorov--Sinai theorem stated directly for the chapter owner
-- `kolmogorov_sinai_entropy` and the canonical partition entropy
-- `MeasurableFinpartition.dynamicalEntropy`.
/-- Theorem 20.35: if the backward iterates of a finite measurable partition `part` under `τ`
generate the ambient σ-algebra, then the entropy `h(P, τ)` equals the partition entropy
`h(P, τ; part)`. -/
theorem kolmogorov_sinai_of_generator
    (P : Measure Ω) [IsProbabilityMeasure P] {τ : Ω → Ω}
    (hτ : MeasurePreserving τ P P) (part : MeasurableFinpartition Ω)
    (hgen : is_generator τ part) :
    h(P, τ, hτ.measurable) = h(P, τ, hτ.measurable; part) := sorry
