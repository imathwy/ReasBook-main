import Mathlib
import ProbabilityTheory_Klenke_2020.Chap17.Definition_17_12
import ProbabilityTheory_Klenke_2020.Chap21.Definition_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E]

-- Proof sketch: take the union of the null disagreement events over the countable index set.
/-- Lemma 21.5, countable-index case: if two processes indexed by a countable type are
modifications of one another, then they are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_countable
    {I : Type*} (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) [Countable I] :
    AreIndistinguishable μ X Y := sorry

variable {I : Set ℝ}

-- Proof sketch: pass to a countable dense subset of the interval `I`, obtain a common null set
-- there, and then use almost sure right continuity and uniqueness of right limits in the
-- Hausdorff codomain to extend equality from the dense subset to every time.
/-- Lemma 21.5, interval/right-continuous case: if two processes indexed by an interval `I ⊆ ℝ`
are modifications of one another and both sample paths are almost surely right continuous on `I`,
then the processes are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
    [T2Space E]
    (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) (hI : I.OrdConnected)
    (hX_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t)
    (hY_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t) :
    AreIndistinguishable μ X Y := sorry

end ProbabilityTheory
