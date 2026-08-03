module

public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Bounds.Basic

public section

/-- Helper for Example 10.3: a nonempty set with a smaller member below each of
its members prevents the ambient strict order from being well-founded. -/
private lemma notWellFoundedLTOfExistsSmaller {α : Type*} [Preorder α] (s : Set α)
    (hs : s.Nonempty) (hsmaller : ∀ x ∈ s, ∃ y ∈ s, y < x) :
    ¬ WellFoundedLT α := by
  -- A well-founded order would supply a minimal member of the descending set.
  intro hwellFounded
  obtain ⟨m, hm⟩ :=
    (WellFounded.wellFoundedLT_iff_exists_minimal.mp hwellFounded) s hs
  -- The stipulated smaller member contradicts that minimality.
  obtain ⟨y, hy, hym⟩ := hsmaller m hm.1
  exact (not_le_of_gt hym) (hm.2 hy hym.le)

/-- Helper for Example 10.3: a set with a smaller member below each of its
members has no least element. -/
private lemma notExistsIsLeastOfExistsSmaller {α : Type*} [Preorder α] (s : Set α)
    (hsmaller : ∀ x ∈ s, ∃ y ∈ s, y < x) :
    ¬ ∃ x, IsLeast s x := by
  -- A least member must lie below the smaller witness supplied for itself.
  rintro ⟨x, hx⟩
  obtain ⟨y, hy, hyx⟩ := hsmaller x hx.1
  exact (not_lt_of_ge (hx.2 hy)) hyx

/-- Helper for Example 10.3: every negative integer has a smaller negative
integer. -/
private lemma negativeIntExistsSmaller (z : ℤ) (hz : z < 0) :
    ∃ w : ℤ, w < 0 ∧ w < z := by
  -- Subtracting one strictly decreases `z` and preserves negativity.
  have hsub : z - 1 < z := sub_one_lt z
  exact ⟨z - 1, hsub.trans hz, hsub⟩

/-- Helper for Example 10.3: every positive real at most one has a smaller
member of the open unit interval. -/
private lemma positiveAtMostOneExistsSmaller (x : ℝ) (hx : 0 < x) (hxone : x ≤ 1) :
    ∃ y ∈ Set.Ioo (0 : ℝ) 1, y < x := by
  -- Halving gives a positive point strictly below `x`, hence still below one.
  have hpositive : 0 < x / 2 := div_pos hx zero_lt_two
  have hsmaller : x / 2 < x := half_lt_self hx
  have hbelowOne : x / 2 < 1 := hsmaller.trans_le hxone
  exact ⟨x / 2, ⟨hpositive, hbelowOne⟩, hsmaller⟩

/-- Helper for Example 10.3: every positive point of the closed unit interval
has a smaller positive point in that interval. -/
private lemma unitIntervalPositiveExistsSmaller (x : Set.Icc (0 : ℝ) 1)
    (hx : 0 < (x : ℝ)) :
    ∃ y : Set.Icc (0 : ℝ) 1, 0 < (y : ℝ) ∧ y < x := by
  -- First find the smaller point in the ambient open interval.
  obtain ⟨y, hy, hyx⟩ :=
    positiveAtMostOneExistsSmaller (x : ℝ) hx x.property.2
  -- Open-interval membership supplies the closed-interval subtype witness.
  have hyIcc : y ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hy
  exact ⟨⟨y, hyIcc⟩, hy.1, hyx⟩

/-- Example 10.3 (1): The usual strict order on the integers is not well-founded,
so it does not well-order `ℤ`. -/
theorem integersNotWellOrdered :
    ¬ WellFoundedLT ℤ := by
  -- The negative integers form a nonempty subset admitting perpetual descent.
  have hnegative : (-1 : ℤ) ∈ Set.Iio (0 : ℤ) := by
    norm_num
  have hnonempty : (Set.Iio (0 : ℤ)).Nonempty := ⟨-1, hnegative⟩
  refine notWellFoundedLTOfExistsSmaller (Set.Iio (0 : ℤ)) hnonempty ?_
  intro z hz
  obtain ⟨w, hwnegative, hwz⟩ := negativeIntExistsSmaller z hz
  exact ⟨w, hwnegative, hwz⟩

/-- Example 10.3 (2): The set of negative integers has no smallest element. -/
theorem negativeIntegersHaveNoLeast :
    ¬ ∃ z : ℤ, IsLeast (Set.Iio (0 : ℤ)) z := by
  -- Apply the same integer descent directly to an alleged least element.
  refine notExistsIsLeastOfExistsSmaller (Set.Iio (0 : ℤ)) ?_
  intro z hz
  obtain ⟨w, hwnegative, hwz⟩ := negativeIntExistsSmaller z hz
  exact ⟨w, hwnegative, hwz⟩

/-- Example 10.3 (3): The usual strict order on the real interval `[0, 1]` is not
well-founded, so it does not well-order that interval. -/
theorem unitIntervalNotWellOrdered :
    ¬ WellFoundedLT (Set.Icc (0 : ℝ) 1) := by
  -- Positive points of the closed interval form a nonempty descending subset.
  have honeIcc : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  let onePoint : Set.Icc (0 : ℝ) 1 := ⟨1, honeIcc⟩
  have honePositive : 0 < (onePoint : ℝ) := zero_lt_one
  have hnonempty : Set.Nonempty {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)} :=
    ⟨onePoint, honePositive⟩
  refine notWellFoundedLTOfExistsSmaller
    {x : Set.Icc (0 : ℝ) 1 | 0 < (x : ℝ)} hnonempty ?_
  intro x hx
  obtain ⟨y, hypositive, hyx⟩ := unitIntervalPositiveExistsSmaller x hx
  exact ⟨y, hypositive, hyx⟩

/-- Example 10.3 (4): The real open interval `(0, 1)` has no smallest element. -/
theorem openUnitIntervalHasNoLeast :
    ¬ ∃ x : ℝ, IsLeast (Set.Ioo (0 : ℝ) 1) x := by
  -- Halving supplies a smaller open-interval point below every candidate.
  refine notExistsIsLeastOfExistsSmaller (Set.Ioo (0 : ℝ) 1) ?_
  intro x hx
  exact positiveAtMostOneExistsSmaller x hx.1 hx.2.le

/- Example 10.3 (5): Although `(0, 1)` has no smallest element, `0` is its
greatest lower bound. -/
#check (isGLB_Ioo (zero_lt_one : (0 : ℝ) < 1) :
    IsGLB (Set.Ioo (0 : ℝ) 1) 0)
