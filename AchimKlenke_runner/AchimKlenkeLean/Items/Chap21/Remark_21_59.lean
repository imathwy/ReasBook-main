import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped ENNReal Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)

/-- The textbook `p`-variation `V_T^p(G)` of a continuous real-valued path on `[0, T]`, defined as
the supremum of the partition sums of `|ΔG|^p` over monotone partitions of `Icc 0 T`. -/
def pVariationUpTo (p : ℝ) (G : PathSpace) (T : NNReal) : ℝ≥0∞ :=
  ⨆ q : ℕ × {u : ℕ → NNReal // Monotone u ∧ ∀ i, u i ∈ Icc 0 T},
    ∑ i ∈ Finset.range q.1,
      (ENNReal.ofReal |G (q.2.1 (i + 1)) - G (q.2.1 i)|) ^ p

-- Proof sketch: for real-valued paths, the `p = 1` partition sums are exactly the sums of the
-- increment distances used in `eVariationOn`; compare the two suprema over monotone partitions of
-- `Icc 0 T`.
/-- The textbook first variation on `[0, T]` agrees with mathlib's total variation
`eVariationOn G (Icc 0 T)`. -/
theorem oneVariationUpTo_eq_eVariationOn_Icc (G : PathSpace) (T : NNReal) :
    pVariationUpTo 1 G T = eVariationOn G (Icc 0 T) := sorry

-- Proof sketch: along any partition of `[0, T]`, one has
-- `∑ |ΔG|^{p'} ≤ (sup |ΔG|^{p' - p}) * ∑ |ΔG|^p`; for a continuous path the mesh-refined maximal
-- increment tends to `0`, so finiteness of the `p`-variation forces the `p'`-variation to vanish.
/-- Remark 21.59 (1): if `0 < p < p'` and the textbook `p`-variation `V_T^p(G)` is finite, then
the `p'`-variation `V_T^{p'}(G)` is zero. -/
theorem pVariationUpTo_eq_zero_of_lt_exponent_of_ne_top
    {p p' : ℝ} (hp : 0 < p) (hpp' : p < p') {G : PathSpace} {T : NNReal}
    (hG : pVariationUpTo p G T ≠ ∞) :
    pVariationUpTo p' G T = 0 := sorry

-- Proof sketch: by Definition 21.52, local finite variation is canonically
-- `LocallyBoundedVariationOn G univ`. This gives finite first variation on every interval `[0, T]`;
-- identify this with `pVariationUpTo 1 G T` via `oneVariationUpTo_eq_eVariationOn_Icc`, then apply
-- `pVariationUpTo_eq_zero_of_lt_exponent_of_ne_top` with `p = 1` and `p' = 2` for each `T`.
/-- Remark 21.59 (2): if `G` has locally finite variation, then the textbook quadratic-variation
path `t ↦ V_t^2(G)` is identically zero. -/
theorem pVariationUpTo_two_eq_zero_of_locallyBoundedVariationOn
    {G : PathSpace} (hG : LocallyBoundedVariationOn G univ) :
    pVariationUpTo 2 G = 0 := sorry
