module

public import Topology_Munkres_2000.Book.Exercise_13_8.RationalIntervals
public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Analysis.Real.Sqrt

public section

open scoped Topology

namespace RealTopology

/-- Helper for Exercise 17.17: the canonical lower-limit intervals form a basis on `ℝ`. -/
private lemma lowerLimitBasis_isTopologicalBasisOnReal :
    lowerLimit.IsTopologicalBasis lowerLimitBasis := by
  -- The Sorgenfrey carrier is definitionally the real line with this topology.
  exact SorgenfreyLine.isTopologicalBasis_lowerLimitBasis

/-- Helper for Exercise 17.17: the lower-limit closure of `(a, b)` is `[a, b)`. -/
private lemma closure_Ioo_lowerLimit {a b : ℝ} :
    closure[lowerLimit] (Set.Ioo a b) = Set.Ico a b := by
  -- Test closure membership against the canonical half-open basis intervals.
  ext x
  rw [@TopologicalSpace.IsTopologicalBasis.mem_closure_iff ℝ lowerLimit
    lowerLimitBasis lowerLimitBasis_isTopologicalBasisOnReal (Set.Ioo a b) x]
  simp only [Set.mem_Ico]
  constructor
  · intro hx
    have hax : a ≤ x := by
      by_contra hax
      have hxa : x < a := lt_of_not_ge hax
      have hBasis : Set.Ico x a ∈ lowerLimitBasis :=
        ⟨x, a, hxa, rfl⟩
      have hxBasis : x ∈ Set.Ico x a := ⟨le_rfl, hxa⟩
      obtain ⟨y, hyBasis, hyInterval⟩ := hx (Set.Ico x a) hBasis hxBasis
      exact (not_lt_of_ge hyInterval.1.le) hyBasis.2
    have hxb : x < b := by
      have hBasis : Set.Ico x (x + 1) ∈ lowerLimitBasis :=
        ⟨x, x + 1, lt_add_one x, rfl⟩
      have hxBasis : x ∈ Set.Ico x (x + 1) := ⟨le_rfl, lt_add_one x⟩
      obtain ⟨y, hyBasis, hyInterval⟩ := hx (Set.Ico x (x + 1)) hBasis hxBasis
      exact hyBasis.1.trans_lt hyInterval.2
    exact ⟨hax, hxb⟩
  · rintro ⟨hax, hxb⟩ o ho hxo
    obtain ⟨c, d, _, rfl⟩ := ho
    have hxUpper : x < min d b := lt_min hxo.2 hxb
    obtain ⟨y, hxy, hyUpper⟩ := exists_between hxUpper
    -- A point just to the right of `x` lies in both the basis interval and `(a, b)`.
    refine ⟨y, ⟨⟨hxo.1.trans hxy.le, hyUpper.trans_le (min_le_left d b)⟩, ?_⟩⟩
    exact ⟨hax.trans_lt hxy, hyUpper.trans_le (min_le_right d b)⟩

/-- Helper for Exercise 17.17: membership in the rational lower-limit closure of
`(a, b)` includes the right endpoint exactly when that endpoint is irrational. -/
private lemma mem_closure_Ioo_rationalLowerLimit_iff {a b x : ℝ} (hab : a < b) :
    x ∈ closure[rationalLowerLimit] (Set.Ioo a b) ↔
      a ≤ x ∧ (x < b ∨ (x = b ∧ Irrational b)) := by
  -- Reduce both directions to intersections with rational half-open basis intervals.
  rw [@TopologicalSpace.IsTopologicalBasis.mem_closure_iff ℝ rationalLowerLimit
    rationalLowerLimitBasis rationalLowerLimitBasis_isTopologicalBasis (Set.Ioo a b) x]
  constructor
  · intro hx
    have hax : a ≤ x := by
      by_contra hax
      have hxa : x < a := lt_of_not_ge hax
      obtain ⟨p, _, hpx⟩ := exists_rat_btwn (sub_lt_self x zero_lt_one)
      obtain ⟨q, hxq, hqa⟩ := exists_rat_btwn hxa
      have hpq : p < q := Rat.cast_lt.mp (hpx.trans hxq)
      have hBasis : Set.Ico (p : ℝ) (q : ℝ) ∈ rationalLowerLimitBasis :=
        (mem_rationalLowerLimitBasis _).mpr ⟨p, q, hpq, rfl⟩
      have hxBasis : x ∈ Set.Ico (p : ℝ) (q : ℝ) := ⟨hpx.le, hxq⟩
      obtain ⟨y, hyBasis, hyInterval⟩ := hx _ hBasis hxBasis
      exact (not_lt_of_ge hyInterval.1.le) (hyBasis.2.trans hqa)
    have hxb : x ≤ b := by
      by_contra hxb
      have hbx : b < x := lt_of_not_ge hxb
      obtain ⟨p, hbp, hpx⟩ := exists_rat_btwn hbx
      obtain ⟨q, hxq, _⟩ := exists_rat_btwn (lt_add_one x)
      have hpq : p < q := Rat.cast_lt.mp (hpx.trans hxq)
      have hBasis : Set.Ico (p : ℝ) (q : ℝ) ∈ rationalLowerLimitBasis :=
        (mem_rationalLowerLimitBasis _).mpr ⟨p, q, hpq, rfl⟩
      have hxBasis : x ∈ Set.Ico (p : ℝ) (q : ℝ) := ⟨hpx.le, hxq⟩
      obtain ⟨y, hyBasis, hyInterval⟩ := hx _ hBasis hxBasis
      exact (not_lt_of_ge (hbp.trans_le hyBasis.1).le) hyInterval.2
    rcases lt_or_eq_of_le hxb with hxb | hxb
    · exact ⟨hax, Or.inl hxb⟩
    · refine ⟨hax, Or.inr ⟨hxb, ?_⟩⟩
      by_contra hbIrrational
      obtain ⟨q, hbq⟩ := exists_rat_of_not_irrational hbIrrational
      have hqq : q < q + 1 := lt_add_one q
      have hBasis : Set.Ico (q : ℝ) ((q + 1 : ℚ) : ℝ) ∈ rationalLowerLimitBasis :=
        (mem_rationalLowerLimitBasis _).mpr ⟨q, q + 1, hqq, rfl⟩
      have hxBasis : x ∈ Set.Ico (q : ℝ) ((q + 1 : ℚ) : ℝ) := by
        constructor
        · rw [hxb, hbq]
        · rw [hxb, hbq]
          norm_num
      obtain ⟨y, hyBasis, hyInterval⟩ := hx _ hBasis hxBasis
      rw [hbq] at hyInterval
      exact (not_lt_of_ge hyBasis.1) hyInterval.2
  · rintro ⟨hax, hxb | ⟨hxb, hbIrrational⟩⟩ o ho hxo
    · obtain ⟨c, d, _, rfl⟩ := (mem_rationalLowerLimitBasis o).mp ho
      have hxUpper : x < min (d : ℝ) b := lt_min hxo.2 hxb
      obtain ⟨y, hxy, hyUpper⟩ := exists_between hxUpper
      -- Moving right from `x` supplies the required intersection point.
      refine ⟨y, ⟨⟨hxo.1.trans hxy.le, hyUpper.trans_le (min_le_left _ _)⟩, ?_⟩⟩
      exact ⟨hax.trans_lt hxy, hyUpper.trans_le (min_le_right _ _)⟩
    · obtain ⟨c, d, _, rfl⟩ := (mem_rationalLowerLimitBasis o).mp ho
      have hcb : (c : ℝ) < b := by
        have hcbLe : (c : ℝ) ≤ b := hxo.1.trans_eq hxb
        exact lt_of_le_of_ne hcbLe (hbIrrational.ne_rat c).symm
      have hmaxb : max a (c : ℝ) < b := max_lt hab hcb
      obtain ⟨y, hmaxy, hyb⟩ := exists_between hmaxb
      -- Irrationality makes the rational left endpoint strictly smaller than `b`.
      refine ⟨y, ⟨⟨(le_max_right a (c : ℝ)).trans hmaxy.le, ?_⟩, ?_⟩⟩
      · exact hyb.trans (hxb ▸ hxo.2)
      · exact ⟨(le_max_left a (c : ℝ)).trans_lt hmaxy, hyb⟩

/-- Helper for Exercise 17.17: an irrational right endpoint belongs to the rational
lower-limit closure of an open interval. -/
private lemma closure_Ioo_rationalLowerLimit_of_irrational_right {a b : ℝ}
    (hab : a < b) (hb : Irrational b) :
    closure[rationalLowerLimit] (Set.Ioo a b) = Set.Icc a b := by
  -- Normalize the general membership classification to closed-interval membership.
  ext x
  rw [mem_closure_Ioo_rationalLowerLimit_iff hab]
  simp only [Set.mem_Icc]
  constructor
  · rintro ⟨hax, hxb | ⟨hxb, _⟩⟩
    · exact ⟨hax, hxb.le⟩
    · exact ⟨hax, hxb.le⟩
  · rintro ⟨hax, hxb⟩
    rcases lt_or_eq_of_le hxb with hxb | hxb
    · exact ⟨hax, Or.inl hxb⟩
    · exact ⟨hax, Or.inr ⟨hxb, hb⟩⟩

/-- Helper for Exercise 17.17: a rational right endpoint is omitted from the rational
lower-limit closure of an open interval. -/
private lemma closure_Ioo_rationalLowerLimit_of_ratCast_right (a : ℝ) (q : ℚ)
    (haq : a < (q : ℝ)) :
    closure[rationalLowerLimit] (Set.Ioo a (q : ℝ)) = Set.Ico a (q : ℝ) := by
  -- The endpoint alternative is impossible because a rational cast is not irrational.
  ext x
  rw [mem_closure_Ioo_rationalLowerLimit_iff haq]
  simp only [Set.mem_Ico]
  constructor
  · rintro ⟨hax, hxq | ⟨_, hqIrrational⟩⟩
    · exact ⟨hax, hxq⟩
    · exact (Rat.not_irrational q hqIrrational).elim
  · rintro ⟨hax, hxq⟩
    exact ⟨hax, Or.inl hxq⟩

/-- Exercise 17.17 (1): In the lower-limit topology, the closure of `(0, √2)` is
`[0, √2)`. -/
theorem lowerLimitClosureIooZeroSqrtTwo :
    closure[lowerLimit] (Set.Ioo 0 (Real.sqrt 2)) = Set.Ico 0 (Real.sqrt 2) := by
  -- Specialize the general lower-limit closure computation to these endpoints.
  exact closure_Ioo_lowerLimit

/-- Exercise 17.17 (2): In the topology generated by half-open intervals with rational
endpoints, the closure of `(0, √2)` is `[0, √2]`. -/
theorem rationalLowerLimitClosureIooZeroSqrtTwo :
    closure[rationalLowerLimit] (Set.Ioo 0 (Real.sqrt 2)) = Set.Icc 0 (Real.sqrt 2) := by
  -- The irrational right endpoint remains in this closure.
  have hTwo : (0 : ℝ) < 2 := by
    norm_num
  have hSqrtTwo : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 hTwo
  exact closure_Ioo_rationalLowerLimit_of_irrational_right hSqrtTwo irrational_sqrt_two

/-- Exercise 17.17 (3): In the lower-limit topology, the closure of `(√2, 3)` is
`[√2, 3)`. -/
theorem lowerLimitClosureIooSqrtTwoThree :
    closure[lowerLimit] (Set.Ioo (Real.sqrt 2) 3) = Set.Ico (Real.sqrt 2) 3 := by
  -- Specialize the general lower-limit closure computation to these endpoints.
  exact closure_Ioo_lowerLimit

/-- Exercise 17.17 (4): In the topology generated by half-open intervals with rational
endpoints, the closure of `(√2, 3)` is `[√2, 3)`. -/
theorem rationalLowerLimitClosureIooSqrtTwoThree :
    closure[rationalLowerLimit] (Set.Ioo (Real.sqrt 2) 3) = Set.Ico (Real.sqrt 2) 3 := by
  -- The rational endpoint `3` is omitted by the rational half-open neighborhood at `3`.
  have hThree : (0 : ℝ) < 3 := by
    norm_num
  have hTwoLtNine : (2 : ℝ) < 3 ^ 2 := by
    norm_num
  have hSqrtTwoThree : Real.sqrt 2 < (3 : ℝ) :=
    (Real.sqrt_lt' hThree).2 hTwoLtNine
  simpa using
    closure_Ioo_rationalLowerLimit_of_ratCast_right (Real.sqrt 2) (3 : ℚ) hSqrtTwoThree

end RealTopology
