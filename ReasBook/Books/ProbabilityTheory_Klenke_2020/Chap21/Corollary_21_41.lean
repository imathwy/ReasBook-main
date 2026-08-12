import Mathlib
import ProbabilityTheory_Klenke_2020.Chap21.Theorem_21_42

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

universe u v

local notation "PathSpace" => ContinuousMap NNReal ℝ

local instance : MeasurableSpace PathSpace := borel PathSpace
local instance : BorelSpace PathSpace := ⟨rfl⟩

variable {I : Type v}

-- Proof sketch: apply the preceding tightness criterion on `C([0, ∞))`. The bounds needed there
-- for the family `X i + Y i` follow from the triangle inequality, both for uniform suprema on
-- compact time intervals and for the modulus-of-continuity terms.
/-- Corollary 21.41: if the laws of two families of continuous real-valued random variables on
`[0, ∞)` are tight, then the laws of their pointwise sums are tight. -/
theorem laws_of_sum_of_tight_continuous_process_families_are_tight
    {Ω : I → Type u} [∀ i, MeasurableSpace (Ω i)]
    (P : (i : I) → ProbabilityMeasure (Ω i))
    (X Y : (i : I) → Ω i → PathSpace)
    (hX : ∀ i, AEMeasurable (X i) (P i))
    (hY : ∀ i, AEMeasurable (Y i) (P i))
    (h_tight_X : IsTightMeasureSet (Set.range fun i ↦ ((P i).map (hX i) : Measure PathSpace)))
    (h_tight_Y : IsTightMeasureSet (Set.range fun i ↦ ((P i).map (hY i) : Measure PathSpace))) :
    IsTightMeasureSet
      (Set.range fun i ↦
        ((P i).map
          (show AEMeasurable (fun ω ↦ X i ω + Y i ω) (P i) from by
            simpa using (hX i).add (hY i)) : Measure PathSpace)) := sorry
