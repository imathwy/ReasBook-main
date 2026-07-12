import Mathlib

open MeasureTheory

-- Declarations for this item will be appended below by the statement pipeline.

/-- Exercise 1.4.5: Lusin's theorem for a Borel measurable map `f : ℝ → ℝ`, asserting that for
every `ε > 0` there is a closed set `C` with `volume Cᶜ < ENNReal.ofReal ε` such that `f` is
continuous on `C` in the relative topology. -/
-- Proof sketch: First prove the claim for indicator functions using inner regularity of Lebesgue
-- measure. Then approximate `f` by simple functions and choose a closed set on which the
-- approximations converge uniformly, so the limit is continuous there.
theorem Measurable.exists_isClosed_continuousOn_compl_lt_of_pos {f : ℝ → ℝ} (hf : Measurable f)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : Set ℝ, IsClosed C ∧ ContinuousOn f C ∧ volume Cᶜ < ENNReal.ofReal ε := sorry
