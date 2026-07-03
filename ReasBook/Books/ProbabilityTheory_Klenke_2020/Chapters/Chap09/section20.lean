import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_9_20 (from Items/Chap09) -/
open MeasureTheory TopologicalSpace

noncomputable section

universe u

variable {ι : Type u} [ConditionallyCompleteLinearOrderBot ι] [WellFoundedLT ι] [Countable ι]
variable {Ω : Type*} {m : MeasurableSpace Ω}
variable {ℱ : Filtration ι m} {X : ι → Ω → ℝ}

-- Proof sketch: apply `Adapted.isStoppingTime_hittingAfter` to the measurable half-line `[K, ∞)`,
-- with initial time `⊥`, and let the target `IsStoppingTime` type determine the implicit set and
-- starting index.
/-- The first entrance time of an adapted process into `[K, ∞)` is a stopping time. -/
theorem leastGE_isStoppingTime
    (hX : Adapted ℱ X) (K : ℝ) :
    IsStoppingTime ℱ (leastGE X K) := by
  simpa [leastGE] using Adapted.isStoppingTime_hittingAfter hX measurableSet_Ici

-- Proof sketch: let `τ` be the first entrance time of `X` into `[K, ∞)`, which is a stopping
-- time by the discrete hitting-time theorem. The event `{ω | ∃ i, K - 5 < X i ω}` is globally
-- measurable as a countable union of measurable coordinate events, and on each slice `{τ ≤ t}` it
-- contains that slice because `X` has already reached the higher level `K`.
/-- Example 9.20: in the discrete/right-discrete setting formalized by mathlib's hitting-time API,
if `τ` is the first entrance time of an adapted real-valued process `X` into `[K, ∞)`, then the
event that `X` exceeds `K - 5` at some time belongs to the stopping-time `σ`-algebra `F_τ`. -/
theorem ever_above_sub_five_measurable_at_first_entrance
    (hX : Adapted ℱ X) (K : ℝ) :
    MeasurableSet[(leastGE_isStoppingTime hX K).measurableSpace]
      {ω | ∃ i, K - 5 < X i ω} := sorry

/-- A concrete process that hits the level `0` immediately and only reveals a possible later jump
above `5` after time `0`. -/
def firstEntranceCounterexampleProcess : ℕ → ℝ → ℝ
  | 0, _ => 0
  | _ + 1, x => if x ≤ 0 then 0 else 10

-- Proof sketch: each time marginal is either constant or a two-valued measurable function defined
-- by the Borel half-line `(0, ∞)`.
/-- Every time slice of the counterexample process is strongly measurable. -/
theorem firstEntranceCounterexampleProcess_stronglyMeasurable :
    ∀ n, StronglyMeasurable (firstEntranceCounterexampleProcess n) := sorry

-- Proof sketch: apply the discrete hitting-time theorem to the adapted counterexample process and
-- the measurable closed half-line `[0, ∞)`.
/-- The counterexample first-entrance time is a stopping time. -/
theorem firstEntranceCounterexampleTime_isStoppingTime :
    IsStoppingTime
      (Filtration.natural firstEntranceCounterexampleProcess
        firstEntranceCounterexampleProcess_stronglyMeasurable)
      (leastGE firstEntranceCounterexampleProcess 0) := by
  simpa [leastGE] using Adapted.isStoppingTime_hittingAfter
    (Filtration.stronglyAdapted_natural firstEntranceCounterexampleProcess_stronglyMeasurable).adapted
    measurableSet_Ici

-- Proof sketch: the stopping time is identically `0`, so `F_τ = F_0`, which is the trivial
-- `σ`-algebra because the time-`0` coordinate of the process is constant. The event that the
-- process ever exceeds `5` is `{x | 0 < x}`, which is not measurable in that trivial
-- `σ`-algebra.
/-- A concrete counterexample showing that the later event of ever exceeding `5` need not belong to
the stopping-time `σ`-algebra at the first entrance time. -/
theorem ever_above_five_not_measurable_at_first_entrance_counterexample :
    ¬ MeasurableSet[firstEntranceCounterexampleTime_isStoppingTime.measurableSpace]
      {x | ∃ n, (5 : ℝ) < firstEntranceCounterexampleProcess n x} := sorry
