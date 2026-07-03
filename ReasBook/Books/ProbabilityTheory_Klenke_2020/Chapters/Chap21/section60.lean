import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_60 (from Items/Chap21) -/
open Filter
open scoped BigOperators ENNReal Topology

noncomputable section

/-- The dyadic first-variation approximation on `[0, T]`, obtained by summing the absolute
increments of `G` along the truncated dyadic mesh of order `n`. -/
def dyadicVariationSumUpTo (G : C(NNReal, ℝ)) (T : NNReal) (n : ℕ) : ℝ≥0∞ :=
  Finset.sum (Finset.range (Nat.ceil ((T : ℝ) * (2 : ℝ) ^ n))) fun k ↦
    ENNReal.ofReal
      |G (min T (((k + 1 : ℕ) : NNReal) / (2 : NNReal) ^ n)) -
        G (min T ((k : NNReal) / (2 : NNReal) ^ n))|

-- Proof sketch: each interval of the order-`n` truncated dyadic partition is split into two
-- consecutive subintervals at level `n + 1`; apply the triangle inequality to the corresponding
-- increment of `G` and sum over all coarse intervals.
/-- Refining the truncated dyadic partition can only increase the first-variation sum. -/
theorem dyadicVariationSumUpTo_monotone (G : C(NNReal, ℝ)) (T : NNReal) :
    Monotone (dyadicVariationSumUpTo G T) := sorry

-- Proof sketch: the preceding monotonicity gives existence of the limit in `ℝ≥0∞`, and the
-- characterization of total variation as the supremum over partition sums identifies that limit
-- with `variationUpTo G T`.
/-- Remark 21.60: for a continuous path `G` on `[0, ∞)`, the first-variation sums along the
truncated dyadic partitions of `[0, T]` converge to the total variation `eVariationOn G (Set.Icc
0 T)`, i.e. the `V¹` quantity from Definition 21.52; hence the `p = 1` partition limit is
independent of the chosen dyadic approximation. -/
theorem dyadicVariationSumUpTo_tendsto_eVariationOn_Icc (G : C(NNReal, ℝ)) (T : NNReal) :
    Tendsto (fun n ↦ dyadicVariationSumUpTo G T n) atTop (𝓝 (eVariationOn G (Set.Icc 0 T))) :=
  sorry
