import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_9_17 (from Items/Chap09) -/
open MeasureTheory

noncomputable section

universe u v

variable {ι : Type u} [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι] [Countable ι]
variable {Ω : Type v} {m : MeasurableSpace Ω}
variable {E : Type*} [MeasurableSpace E]
variable {ℱ : Filtration ι m} {X : ι → Ω → E}

/-- Example 9.17: for a countable discrete time index with initial time `⊥`, the first entrance
time of an adapted process into a measurable set is a stopping time. -/
theorem hittingAfter_bot_isStoppingTime
    (hX : Adapted ℱ X) {K : Set E} (hK : MeasurableSet K) :
    IsStoppingTime ℱ (hittingAfter X K ⊥) := by
  simpa using Adapted.isStoppingTime_hittingAfter hX hK

/-- The last visit time of a discrete-time process to the set `K`, written as the supremum of the
visit times and taking values in `WithTop ℕ` so that infinitely many visits yield `⊤`. -/
def lastVisitTime (X : ℕ → Ω → E) (K : Set E) : Ω → WithTop ℕ :=
  fun ω ↦ sSup ((fun n : ℕ ↦ (n : WithTop ℕ)) '' {n | X n ω ∈ K})

/-- Example 9.17: the last visit time `sup {t | X_t ∈ K}` of an adapted discrete-time process into
a measurable set need not be a stopping time in general. -/
theorem exists_lastVisitTime_not_isStoppingTime :
    ∃ (Ω : Type u) (m : MeasurableSpace Ω) (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ) (K : Set ℝ),
      Adapted ℱ X ∧ MeasurableSet K ∧ ¬ IsStoppingTime ℱ (lastVisitTime X K) := by
  sorry
