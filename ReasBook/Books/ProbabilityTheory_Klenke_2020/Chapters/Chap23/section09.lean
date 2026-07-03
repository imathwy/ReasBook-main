import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Lemma_23_9 (from Items/Chap23) -/
open Filter
open scoped Topology BigOperators ENNReal

namespace ENNReal

/-- The upper small-noise exponential growth of `u`, namely `limsup_{ε→0+} ε log u(ε)`. This is
the `ε ↓ 0` analogue of `ExpGrowth.expGrowthSup`. -/
noncomputable def smallNoiseExpGrowthSup (u : ℝ → ℝ≥0∞) : EReal :=
  limsup (fun ε : ℝ ↦ (ε : EReal) * log (u ε)) (𝓝[>] (0 : ℝ))

/-- Unfolding `smallNoiseExpGrowthSup` gives the scaled logarithmic `limsup`. -/
theorem smallNoiseExpGrowthSup_def (u : ℝ → ℝ≥0∞) :
    smallNoiseExpGrowthSup u =
      limsup (fun ε : ℝ ↦ (ε : EReal) * log (u ε)) (𝓝[>] (0 : ℝ)) := rfl

/-- For a finite family of nonnegative functions of `ε`, the upper small-noise exponential growth
of the pointwise sum over a `Finset` is the supremum of the corresponding upper small-noise
exponential growths. This is the owner-facing finite-aggregation API for
`smallNoiseExpGrowthSup`, mirroring `ExpGrowth.expGrowthSup_sum`. -/
theorem smallNoiseExpGrowthSup_sum {α : Type*} (u : α → ℝ → ℝ≥0∞) (s : Finset α) :
    smallNoiseExpGrowthSup (∑ x ∈ s, u x) = ⨆ x ∈ s, smallNoiseExpGrowthSup (u x) := sorry

end ENNReal

-- Proof sketch: in the nonempty case compare the pointwise finite sum with the finite supremum:
-- `Finset.univ.sup (fun i ↦ a i ε) ≤ ∑ i, a i ε ≤ Fintype.card ι * Finset.univ.sup (fun i ↦ a i ε)`.
-- Applying `log`, multiplying by `ε`, and taking the `limsup` along `𝓝[>] 0` yields the claim
-- because the additive error `ε * log (Fintype.card ι)` tends to `0`; the empty-index case is
-- immediate.
/-- Lemma 23.9: for a finite family of nonnegative functions of `ε`, the upper small-noise
exponential growth of the pointwise sum equals the supremum of the upper small-noise exponential
growths of the summands. The public API is stated for an arbitrary finite index type, treating the
textbook's `N + 1`-tuple as a concrete model of a finite family rather than as primitive data. -/
theorem limsup_zero_right_mul_log_sum_eq_iSup {ι : Type*} [Fintype ι] (a : ι → ℝ → ℝ≥0∞) :
    ENNReal.smallNoiseExpGrowthSup (∑ i, a i) =
      ⨆ i : ι, ENNReal.smallNoiseExpGrowthSup (a i) := by
  simpa using ENNReal.smallNoiseExpGrowthSup_sum a Finset.univ
