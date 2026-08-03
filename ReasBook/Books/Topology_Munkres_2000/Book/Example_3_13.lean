module

public import Topology_Munkres_2000.Book.Definition_3_17.BoundsProperty
public import Mathlib.Data.PNat.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.Interval.Set.Defs

public section

open Set

/-- The punctured open interval `(-1, 0) ∪ (0, 1)` used as the ordered set `B`
in Example 3.13. -/
def puncturedOpenUnitInterval : Set ℝ :=
  Set.Ioo (-1) 0 ∪ Set.Ioo 0 1

/-- The sequence `n ↦ -1 / (2 * n)` from Example 3.13. -/
@[expose]
noncomputable def reciprocalEvenNegative (n : ℕ+) : ℝ :=
  -1 / (2 * (n : ℝ))

/-- The sequence `reciprocalEvenNegative` has the formula from Example 3.13. -/
@[simp]
theorem reciprocalEvenNegative_apply (n : ℕ+) :
    reciprocalEvenNegative n = -1 / (2 * (n : ℝ)) := rfl

/-- The set `{ -1 / (2 * n) | n : ℕ+ }` from Example 3.13. -/
def reciprocalEvenNegatives : Set ℝ :=
  Set.range reciprocalEvenNegative

/-- Each term of `reciprocalEvenNegative` belongs to `Set.Ioo (-1 : ℝ) 1`. -/
theorem reciprocalEvenNegative_mem_openUnitInterval (n : ℕ+) :
    reciprocalEvenNegative n ∈ Set.Ioo (-1 : ℝ) 1 := by
  -- The denominator is greater than one, so its reciprocal lies strictly between zero and one.
  have hn : (0 : ℝ) < n := by
    exact_mod_cast n.property
  have hone_le_n : (1 : ℝ) ≤ n := by
    exact_mod_cast n.property
  have hden : (0 : ℝ) < 2 * n := by
    positivity
  have hone_lt_den : (1 : ℝ) < 2 * n := by
    linarith
  have hinv_lt_one : (2 * (n : ℝ))⁻¹ < 1 := by
    exact (inv_lt_one₀ hden).2 hone_lt_den
  constructor
  · rw [reciprocalEvenNegative_apply, div_eq_mul_inv]
    linarith
  · have hnegative : -1 / (2 * (n : ℝ)) < 0 := by
      exact div_neg_of_neg_of_pos (by norm_num) hden
    rw [reciprocalEvenNegative_apply]
    exact hnegative.trans (by norm_num)

/-- Helper for Example 3.13: every term of the negative reciprocal sequence is
strictly negative. -/
lemma reciprocalEvenNegative_neg (n : ℕ+) : reciprocalEvenNegative n < 0 := by
  -- The numerator is negative and the denominator is positive.
  have hn : (0 : ℝ) < n := by
    exact_mod_cast n.property
  have hden : (0 : ℝ) < 2 * n := by
    positivity
  rw [reciprocalEvenNegative_apply]
  exact div_neg_of_neg_of_pos (by norm_num) hden

/-- Each term of `reciprocalEvenNegative` belongs to
`puncturedOpenUnitInterval`. -/
theorem reciprocalEvenNegative_mem_puncturedOpenUnitInterval (n : ℕ+) :
    reciprocalEvenNegative n ∈ puncturedOpenUnitInterval := by
  -- Every sequence term is negative, so it lies in the negative component of the union.
  left
  have hinterval := reciprocalEvenNegative_mem_openUnitInterval n
  exact ⟨hinterval.1, reciprocalEvenNegative_neg n⟩

/-- The restriction of `reciprocalEvenNegatives` to `Set.Ioo (-1 : ℝ) 1`. -/
def reciprocalEvenNegativesInOpenUnitInterval : Set (Set.Ioo (-1 : ℝ) 1) :=
  Subtype.val ⁻¹' reciprocalEvenNegatives

/-- The restriction of `reciprocalEvenNegatives` to
`puncturedOpenUnitInterval`. -/
def reciprocalEvenNegativesInPuncturedInterval : Set puncturedOpenUnitInterval :=
  Subtype.val ⁻¹' reciprocalEvenNegatives

/-- The real number `0` belongs to `Set.Ioo (-1 : ℝ) 1`. -/
theorem zero_mem_openUnitInterval : (0 : ℝ) ∈ Set.Ioo (-1 : ℝ) 1 := by
  -- Both endpoint inequalities are numerical.
  norm_num

/-- Helper for Example 3.13: an ambient least upper bound of the image of a
subtype set is a least upper bound in the subtype order. -/
lemma isLUB_subtype_of_isLUB_image {α : Type*} [Preorder α] {p : α → Prop}
    {s : Set {x // p x}} {a : {x // p x}} (h : IsLUB (Subtype.val '' s) a.1) :
    IsLUB s a := by
  -- Upper-bound comparisons pass directly through the subtype coercion.
  constructor
  · intro x hx
    exact h.1 ⟨x, hx, rfl⟩
  · intro b hb
    have hbImage : b.1 ∈ upperBounds (Subtype.val '' s) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      exact hb hy
    exact h.2 hbImage

/-- The first assertion of Example 3.13: the ordered set `Set.Ioo (-1 : ℝ) 1` has the least upper
bound property. -/
theorem openUnitInterval_leastUpperBoundProperty :
    LeastUpperBoundProperty (Set.Ioo (-1 : ℝ) 1) := by
  -- Take the real least upper bound of the coerced set and show it remains inside the interval.
  apply LeastUpperBoundProperty.of_exists_isLUB
  intro s hs hb
  obtain ⟨x, hx⟩ := hs
  obtain ⟨u, hu⟩ := hb
  have hImageNonempty : (Subtype.val '' s).Nonempty := by
    exact ⟨x.1, x, hx, rfl⟩
  have huImage : u.1 ∈ upperBounds (Subtype.val '' s) := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact hu hz
  have hImageBounded : BddAbove (Subtype.val '' s) := by
    exact ⟨u.1, huImage⟩
  obtain ⟨a, ha⟩ := Real.exists_isLUB hImageNonempty hImageBounded
  have hx_le_a : x.1 ≤ a := by
    exact ha.1 ⟨x, hx, rfl⟩
  have ha_le_u : a ≤ u.1 := by
    exact ha.2 huImage
  have ha_mem : a ∈ Set.Ioo (-1 : ℝ) 1 := by
    constructor
    · exact x.property.1.trans_le hx_le_a
    · exact ha_le_u.trans_lt u.property.2
  let aInterval : Set.Ioo (-1 : ℝ) 1 := ⟨a, ha_mem⟩
  exact ⟨aInterval, isLUB_subtype_of_isLUB_image ha⟩

/-- Helper for Example 3.13: the negative reciprocal sequence is cofinal among
the negative real numbers below `0`. -/
lemma exists_reciprocalEvenNegative_gt_of_neg {x : ℝ} (hx : x < 0) :
    ∃ n : ℕ+, x < reciprocalEvenNegative n := by
  -- Apply the Archimedean reciprocal estimate to `-x`, then enlarge the denominator to `2n`.
  obtain ⟨n, hn, hinv⟩ := Real.exists_nat_pos_inv_lt (neg_pos.mpr hx)
  have hnReal : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hdenComparison : (n : ℝ) < 2 * n := by
    linarith
  have hreciprocalComparison : 1 / (2 * (n : ℝ)) < 1 / n := by
    exact one_div_lt_one_div_of_lt hnReal hdenComparison
  refine ⟨⟨n, hn⟩, ?_⟩
  have hinv' : 1 / (n : ℝ) < -x := by
    simpa [one_div] using hinv
  have hsmall : 1 / (2 * (n : ℝ)) < -x := hreciprocalComparison.trans hinv'
  have hnegated := neg_lt_neg hsmall
  simpa [reciprocalEvenNegative_apply, div_eq_mul_inv] using hnegated

/-- The second assertion of Example 3.13: the set `{ -1 / (2 * n) | n : ℕ+ }` has no greatest
element in `Set.Ioo (-1 : ℝ) 1`. -/
theorem reciprocalEvenNegatives_noGreatest :
    ¬ ∃ x, IsGreatest reciprocalEvenNegativesInOpenUnitInterval x := by
  -- A represented term is negative, and cofinality supplies a strictly larger represented term.
  rintro ⟨x, hx⟩
  obtain ⟨m, hm⟩ := hx.1
  have hxValue : (x : ℝ) = reciprocalEvenNegative m := hm.symm
  have hxNeg : (x : ℝ) < 0 := by
    rw [hxValue]
    exact reciprocalEvenNegative_neg m
  obtain ⟨n, hn⟩ := exists_reciprocalEvenNegative_gt_of_neg hxNeg
  let y : Set.Ioo (-1 : ℝ) 1 :=
    ⟨reciprocalEvenNegative n, reciprocalEvenNegative_mem_openUnitInterval n⟩
  have hy : y ∈ reciprocalEvenNegativesInOpenUnitInterval := by
    exact ⟨n, rfl⟩
  have hy_le_x := hx.2 hy
  exact (not_le_of_gt hn) hy_le_x

/-- The third assertion of Example 3.13: the least upper bound in `Set.Ioo (-1 : ℝ) 1` of
`{ -1 / (2 * n) | n : ℕ+ }` is `0`. -/
theorem reciprocalEvenNegatives_isLUB_zero :
    IsLUB reciprocalEvenNegativesInOpenUnitInterval
      (⟨0, zero_mem_openUnitInterval⟩ : Set.Ioo (-1 : ℝ) 1) := by
  -- Zero bounds every negative term, and cofinality rules out every smaller upper bound.
  constructor
  · intro x hx
    obtain ⟨n, hn⟩ := hx
    have hxValue : (x : ℝ) = reciprocalEvenNegative n := hn.symm
    have hxNeg : (x : ℝ) < 0 := by
      rw [hxValue]
      exact reciprocalEvenNegative_neg n
    exact le_of_lt hxNeg
  · intro b hb
    by_contra hzero_le
    have hbNeg : (b : ℝ) < 0 := lt_of_not_ge hzero_le
    obtain ⟨n, hn⟩ := exists_reciprocalEvenNegative_gt_of_neg hbNeg
    let x : Set.Ioo (-1 : ℝ) 1 :=
      ⟨reciprocalEvenNegative n, reciprocalEvenNegative_mem_openUnitInterval n⟩
    have hx : x ∈ reciprocalEvenNegativesInOpenUnitInterval := by
      exact ⟨n, rfl⟩
    have hx_le_b := hb hx
    exact (not_le_of_gt hn) hx_le_b

/-- The fourth assertion of Example 3.13: every element of the positive component `(0, 1)` is an
upper bound in `puncturedOpenUnitInterval` for `{ -1 / (2 * n) | n : ℕ+ }`. -/
theorem positivePart_upperBound_reciprocalEvenNegatives
    (b : puncturedOpenUnitInterval) (hb : (b : ℝ) ∈ Set.Ioo 0 1) :
    b ∈ upperBounds reciprocalEvenNegativesInPuncturedInterval := by
  -- Every represented term is negative, while `b` is positive.
  intro x hx
  obtain ⟨n, hn⟩ := hx
  have hxValue : (x : ℝ) = reciprocalEvenNegative n := hn.symm
  have hxNeg : (x : ℝ) < 0 := by
    rw [hxValue]
    exact reciprocalEvenNegative_neg n
  exact le_of_lt (hxNeg.trans hb.1)

/-- Helper for Example 3.13: halving a point of `(0, 1)` gives a point of the
positive component of the punctured interval. -/
lemma half_mem_puncturedOpenUnitInterval_of_pos {x : ℝ} (hx : x ∈ Set.Ioo 0 1) :
    x / 2 ∈ puncturedOpenUnitInterval := by
  -- Halving preserves positivity and makes the upper endpoint inequality immediate.
  right
  constructor
  · exact div_pos hx.1 (by norm_num)
  · apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    linarith [hx.2]

/-- Helper for Example 3.13: `1 / 2` belongs to the positive component of the
punctured open unit interval. -/
lemma oneHalf_mem_puncturedOpenUnitInterval :
    (1 / 2 : ℝ) ∈ puncturedOpenUnitInterval := by
  -- The fixed midpoint lies strictly between zero and one.
  right
  norm_num

/-- The fifth assertion of Example 3.13: the set `{ -1 / (2 * n) | n : ℕ+ }` has no least upper
bound in `puncturedOpenUnitInterval`. -/
theorem reciprocalEvenNegatives_noLUB_inPuncturedInterval :
    ¬ ∃ b : puncturedOpenUnitInterval,
      IsLUB reciprocalEvenNegativesInPuncturedInterval b := by
  -- A negative candidate is not an upper bound.
  -- A positive candidate has a smaller positive upper bound.
  rintro ⟨b, hb⟩
  rcases b.property with hbNeg | hbPos
  · obtain ⟨n, hn⟩ := exists_reciprocalEvenNegative_gt_of_neg hbNeg.2
    let x : puncturedOpenUnitInterval :=
      ⟨reciprocalEvenNegative n, reciprocalEvenNegative_mem_puncturedOpenUnitInterval n⟩
    have hx : x ∈ reciprocalEvenNegativesInPuncturedInterval := by
      exact ⟨n, rfl⟩
    have hx_le_b := hb.1 hx
    exact (not_le_of_gt hn) hx_le_b
  · have hbHalfMem := half_mem_puncturedOpenUnitInterval_of_pos hbPos
    let bHalf : puncturedOpenUnitInterval := ⟨(b : ℝ) / 2, hbHalfMem⟩
    have hbHalfUpper :
        bHalf ∈ upperBounds reciprocalEvenNegativesInPuncturedInterval := by
      apply positivePart_upperBound_reciprocalEvenNegatives bHalf
      constructor
      · dsimp [bHalf]
        exact div_pos hbPos.1 (by norm_num)
      · dsimp [bHalf]
        apply (div_lt_iff₀ (by norm_num : (0 : ℝ) < 2)).2
        linarith [hbPos.2]
    have hb_le_half := hb.2 hbHalfUpper
    have hhalf_lt_b : (bHalf : ℝ) < b := by
      dsimp [bHalf]
      linarith [hbPos.1]
    exact (not_le_of_gt hhalf_lt_b) hb_le_half

/-- Example 3.13: The ordered set `puncturedOpenUnitInterval` does not have
the least upper bound property. -/
theorem puncturedOpenUnitInterval_not_leastUpperBoundProperty :
    ¬ LeastUpperBoundProperty puncturedOpenUnitInterval := by
  -- The reciprocal sequence is nonempty and bounded above by `1/2`, but has no LUB.
  intro hProperty
  let firstTerm : puncturedOpenUnitInterval :=
    ⟨reciprocalEvenNegative 1, reciprocalEvenNegative_mem_puncturedOpenUnitInterval 1⟩
  have hNonempty : reciprocalEvenNegativesInPuncturedInterval.Nonempty := by
    exact ⟨firstTerm, 1, rfl⟩
  let oneHalf : puncturedOpenUnitInterval :=
    ⟨1 / 2, oneHalf_mem_puncturedOpenUnitInterval⟩
  have hOneHalfPos : ((oneHalf : puncturedOpenUnitInterval) : ℝ) ∈ Set.Ioo 0 1 := by
    norm_num [oneHalf]
  have hBounded : BddAbove reciprocalEvenNegativesInPuncturedInterval := by
    exact ⟨oneHalf, positivePart_upperBound_reciprocalEvenNegatives oneHalf hOneHalfPos⟩
  obtain ⟨b, hb⟩ := hProperty.exists_isLUB
    reciprocalEvenNegativesInPuncturedInterval hNonempty hBounded
  exact reciprocalEvenNegatives_noLUB_inPuncturedInterval ⟨b, hb⟩
