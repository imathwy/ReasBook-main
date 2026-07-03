import Mathlib
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1
import ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory
open ProbabilityTheory
open scoped Topology NNReal ENNReal

noncomputable section

universe u

namespace MeasureTheory

variable {Ω : Type u} [MeasurableSpace Ω]

local notation "TimeFiltration" => Filtration NNReal (inferInstance : MeasurableSpace Ω)
local notation "RealProcess" => NNReal → Ω → ℝ

namespace Adapted

-- Proof sketch: treat the right-continuous and left-continuous cases separately. In the
-- right-continuous case, use the standard approximation of each strip `[0, t] × Ω` by step
-- processes built from times below `t`; in the left-continuous case, use the analogous
-- approximation from the left.
/-- Theorem 25.8 (1): if an adapted real-valued process is right continuous or left continuous,
then it is progressively measurable. -/
theorem progMeasurable_of_left_or_right_continuous
    {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_cont :
      HasRightContinuousPaths H ∨
      ∀ ω : Ω, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ProgMeasurable ℱ H := by
  rcases hH_cont with hH_right | hH_left
  · exact hH_adapted.progMeasurable_of_rightContinuous hH_right
  · sorry

-- Proof sketch: in the almost-surely right-continuous or left-continuous case, modify the process
-- on a measurable null set so that all paths satisfy the corresponding one-sided continuity
-- property, keep the same timewise almost-everywhere values, and apply the previous theorem to
-- the resulting version.
/-- Theorem 25.8 (2): if an adapted real-valued process is almost surely right continuous or
almost surely left continuous, then it admits a progressively measurable version. -/
theorem exists_progMeasurable_modification_of_ae_left_or_right_continuous
    {μ : Measure Ω} {ℱ : TimeFiltration} {H : RealProcess}
    (hH_adapted : Adapted ℱ H)
    (hH_ae_cont :
      (∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Ici t) t) ∨
      ∀ᵐ ω ∂μ, ∀ t : NNReal,
        ContinuousWithinAt (fun s : NNReal ↦ H s ω) (Set.Iic t) t) :
    ∃ H' : RealProcess, ProgMeasurable ℱ H' ∧ AreModifications μ H H' := sorry

end Adapted
end MeasureTheory

/- Theorem 25.8 (3): in particular, every predictable process is progressively measurable. This is
exactly the canonical theorem `MeasureTheory.IsPredictable.progMeasurable`. -/
recall IsPredictable.progMeasurable
