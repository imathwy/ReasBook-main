module

public import Mathlib.Topology.Instances.Real.Lemmas
public import Topology_Munkres_2000.Book.Definition_26_4.Tube

open Set

public section

/-- The region in `ℝ × ℝ` whose horizontal width shrinks as the second coordinate
moves away from zero. -/
def shrinkingTubeRegion : Set (ℝ × ℝ) :=
  {p | |p.1| < 1 / (p.2 ^ 2 + 1)}

/-- Membership in `shrinkingTubeRegion` is the defining coordinate inequality. -/
theorem mem_shrinkingTubeRegion (p : ℝ × ℝ) :
    p ∈ shrinkingTubeRegion ↔ |p.1| < 1 / (p.2 ^ 2 + 1) :=
  Iff.rfl

/-- Helper for Example 26.7: a real square plus one is nonzero. -/
private lemma sqAddOneNeZero (y : ℝ) : y ^ 2 + 1 ≠ 0 := by
  -- Strict positivity rules out the only possible zero denominator.
  positivity

/-- Helper for Example 26.7: adding one to a nonnegative real gives a number
strictly smaller than its square plus one. -/
private lemma addOneLtSqAddOneOfNonneg {z : ℝ} (hz : 0 ≤ z) :
    z + 1 < (z + 1) ^ 2 + 1 := by
  -- Expanding the square leaves only nonnegative terms and a positive constant.
  nlinarith [sq_nonneg z]

/-- The first assertion of Example 26.7: the shrinking region is open in `ℝ × ℝ`. -/
theorem shrinkingTubeRegion_isOpen : IsOpen shrinkingTubeRegion := by
  -- Express the defining inequality using continuous coordinate functions.
  rw [shrinkingTubeRegion]
  have hdenominator : ∀ p : ℝ × ℝ, p.2 ^ 2 + 1 ≠ 0 :=
    fun p ↦ sqAddOneNeZero p.2
  have hwidth : Continuous (fun p : ℝ × ℝ ↦ 1 / (p.2 ^ 2 + 1)) :=
    continuous_const.div ((continuous_snd.pow 2).add continuous_const) hdenominator
  -- A strict inequality of continuous real-valued functions defines an open set.
  exact isOpen_lt continuous_fst.abs hwidth

/-- The second assertion of Example 26.7: the shrinking region contains the vertical slice
`({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ)`. -/
theorem verticalSlice_subset_shrinkingTubeRegion :
    ({0} : Set ℝ) ×ˢ (univ : Set ℝ) ⊆ shrinkingTubeRegion := by
  -- On the vertical slice the absolute value of the first coordinate is zero.
  intro p hp
  have hpfirst : p.1 = 0 := Set.mem_singleton_iff.mp hp.1
  rw [mem_shrinkingTubeRegion, hpfirst, abs_zero]
  -- Every width `1 / (y ^ 2 + 1)` is strictly positive.
  positivity

/-- Helper for Example 26.7: the widths `1 / (y ^ 2 + 1)` become smaller
than every positive real number. -/
private lemma existsOneDivSqAddOneLt {x : ℝ} (hx : 0 < x) :
    ∃ y : ℝ, 1 / (y ^ 2 + 1) < x := by
  -- First choose a reciprocal of a positive natural successor below `x`.
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
  have hsuccessorPos : 0 < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  have hnaturalNonneg : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hsuccessorLtSq : (n : ℝ) + 1 < ((n : ℝ) + 1) ^ 2 + 1 :=
    addOneLtSqAddOneOfNonneg hnaturalNonneg
  -- Enlarging the positive denominator makes its reciprocal still smaller.
  have hreciprocalLt :
      1 / (((n : ℝ) + 1) ^ 2 + 1) < 1 / ((n : ℝ) + 1) :=
    one_div_lt_one_div_of_lt hsuccessorPos hsuccessorLtSq
  have hwidthLt : 1 / (((n : ℝ) + 1) ^ 2 + 1) < x :=
    hreciprocalLt.trans hn
  exact ⟨(n : ℝ) + 1, hwidthLt⟩

/-- Example 26.7 (3): The shrinking region contains no open tube about the vertical
slice through zero. -/
theorem shrinkingTubeRegion_contains_no_tube (T : Set (ℝ × ℝ))
    (hT : Set.IsTubeAbout 0 T) : ¬ T ⊆ shrinkingTubeRegion := by
  -- Write the tube as an open horizontal neighborhood times the whole vertical axis.
  intro hsubset
  obtain ⟨W, hWOpen, hzeroW, hTProduct⟩ := Set.isTubeAbout_iff.mp hT
  obtain ⟨a, b, hzeroIoo, hIooW⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hWOpen.mem_nhds hzeroW)
  -- The midpoint between zero and the positive right endpoint lies in `W`.
  have hxPos : 0 < b / 2 := half_pos hzeroIoo.2
  have hxLtB : b / 2 < b := half_lt_self hzeroIoo.2
  have haLtX : a < b / 2 := hzeroIoo.1.trans hxPos
  have hxIoo : b / 2 ∈ Ioo a b := ⟨haLtX, hxLtB⟩
  have hxW : b / 2 ∈ W := hIooW hxIoo
  -- Far enough along the vertical axis, the region is narrower than this midpoint.
  obtain ⟨y, hyWidth⟩ := existsOneDivSqAddOneLt hxPos
  have hpointProduct : (b / 2, y) ∈ W ×ˢ (univ : Set ℝ) :=
    ⟨hxW, mem_univ y⟩
  have hpointTube : (b / 2, y) ∈ T := hTProduct.symm ▸ hpointProduct
  have hpointRegion : (b / 2, y) ∈ shrinkingTubeRegion := hsubset hpointTube
  have hregionInequality : |b / 2| < 1 / (y ^ 2 + 1) :=
    (mem_shrinkingTubeRegion _).mp hpointRegion
  -- Positivity removes the absolute value, yielding the opposite strict inequalities.
  have habs : |b / 2| = b / 2 := abs_of_pos hxPos
  have hxLtWidth : b / 2 < 1 / (y ^ 2 + 1) := habs ▸ hregionInequality
  exact (lt_asymm hxLtWidth hyWidth)

end
