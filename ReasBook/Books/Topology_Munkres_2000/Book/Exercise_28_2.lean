module

public import Topology_Munkres_2000.Book.Definition_28_1.LimitPointCompact
public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine

public section

/-- Helper for Exercise 28.2: the Sorgenfrey line satisfies the `T₁` separation axiom. -/
private lemma sorgenfreyT1Space : T1Space SorgenfreyLine := by
  -- Separate distinct points by a basic half-open interval based at the first point.
  rw [t1Space_iff_exists_open]
  intro x y hxy
  have hxyReal : SorgenfreyLine.toReal x ≠ SorgenfreyLine.toReal y :=
    SorgenfreyLine.toReal.injective.ne hxy
  rcases lt_or_gt_of_ne hxyReal with hxyReal | hyxReal
  · refine ⟨Set.Ico (SorgenfreyLine.toReal x) (SorgenfreyLine.toReal y), ?_, ?_, ?_⟩
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨_, _, hxyReal, rfl⟩
    · exact Set.left_mem_Ico.mpr hxyReal
    · exact fun hy ↦ hy.2.false
  · refine ⟨Set.Ico (SorgenfreyLine.toReal x)
      (SorgenfreyLine.toReal x + (1 : ℝ)), ?_, ?_, ?_⟩
    · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨_, _, lt_add_one _, rfl⟩
    · exact Set.left_mem_Ico.mpr (lt_add_one (SorgenfreyLine.toReal x))
    · exact fun hy ↦ (not_le_of_gt hyxReal) hy.1

/-- Helper for Exercise 28.2: `toReal` preserves strict order against a real endpoint. -/
private lemma sorgenfreyToReal_lt_iff (x : SorgenfreyLine) (y : ℝ) :
    SorgenfreyLine.toReal x < y ↔ x < SorgenfreyLine.toReal.symm y := by
  -- Both orders are the real order on the common carrier.
  rfl

/-- Helper for Exercise 28.2: `toReal` preserves weak order against a real endpoint. -/
private lemma sorgenfreyToReal_le_iff (x : SorgenfreyLine) (y : ℝ) :
    SorgenfreyLine.toReal x ≤ y ↔ x ≤ SorgenfreyLine.toReal.symm y := by
  -- Both orders are the real order on the common carrier.
  rfl

/-- Helper for Exercise 28.2: `toReal` preserves lower bounds from real endpoints. -/
private lemma sorgenfreyReal_le_toReal_iff (x : SorgenfreyLine) (y : ℝ) :
    y ≤ SorgenfreyLine.toReal x ↔ SorgenfreyLine.toReal.symm y ≤ x := by
  -- Both orders are the real order on the common carrier.
  rfl

/-- Helper for Exercise 28.2: the inverse carrier equivalence preserves weak order. -/
private lemma sorgenfreySymm_le_symm_iff (x y : ℝ) :
    SorgenfreyLine.toReal.symm x ≤ SorgenfreyLine.toReal.symm y ↔ x ≤ y := by
  -- Both orders are the real order on the common carrier.
  rfl

/-- Helper for Exercise 28.2: the increasing open cover used on the Sorgenfrey interval. -/
private def sorgenfreyUnitIntervalCover (n : ℕ) :
    Set (Set.Icc (0 : SorgenfreyLine) 1) :=
  Subtype.val ⁻¹' (SorgenfreyLine.toReal ⁻¹'
    (Set.Iio (1 - 1 / (n + 1 : ℝ)) ∪ Set.Ico 1 2))

/-- Helper for Exercise 28.2: every member of the canonical interval cover is open. -/
private lemma isOpen_sorgenfreyUnitIntervalCover (n : ℕ) :
    IsOpen (sorgenfreyUnitIntervalCover n) := by
  -- Both ambient pieces are unions of basic half-open intervals, then pull back to the subtype.
  apply IsOpen.preimage continuous_subtype_val
  have hambient : SorgenfreyLine.toReal ⁻¹'
      (Set.Iio (1 - 1 / (n + 1 : ℝ)) ∪ Set.Ico 1 2) =
      Set.Iio (SorgenfreyLine.toReal.symm (1 - 1 / (n + 1 : ℝ))) ∪
        Set.Ico (1 : SorgenfreyLine) (SorgenfreyLine.toReal.symm 2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_union, Set.mem_Iio, Set.mem_Ico]
    rw [sorgenfreyToReal_lt_iff, sorgenfreyReal_le_toReal_iff,
      sorgenfreyToReal_lt_iff]
    have hone : SorgenfreyLine.toReal.symm 1 = (1 : SorgenfreyLine) := rfl
    rw [hone]
  rw [hambient]
  apply IsOpen.union
  · refine SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
    intro x hx
    refine ⟨Set.Ico (SorgenfreyLine.toReal x) (1 - 1 / (n + 1 : ℝ)), ?_, ?_, ?_⟩
    · exact ⟨_, _, hx, rfl⟩
    · exact Set.left_mem_Ico.mpr hx
    · exact fun _ hy ↦ hy.2
  · apply SorgenfreyLine.isTopologicalBasis_lowerLimitBasis.isOpen
    exact ⟨1, 2, by norm_num, rfl⟩

/-- Helper for Exercise 28.2: the cutoff points of the canonical cover lie in `[0, 1]`. -/
private lemma sorgenfreyUnitIntervalCutoff_mem (n : ℕ) :
    SorgenfreyLine.toReal.symm (1 - 1 / (n + 1 : ℝ)) ∈
      Set.Icc (0 : SorgenfreyLine) 1 := by
  -- The reciprocal lies in `(0, 1]`, so subtracting it from one stays in the interval.
  have hdenom : (1 : ℝ) ≤ n + 1 := by
    norm_num
  have hrecipNonneg : 0 ≤ 1 / (n + 1 : ℝ) := by
    positivity
  have hrecipLe : 1 / (n + 1 : ℝ) ≤ 1 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hdenom
  constructor
  · have hreal : (0 : ℝ) ≤ 1 - 1 / (n + 1 : ℝ) := by linarith
    have hzero : SorgenfreyLine.toReal.symm 0 = (0 : SorgenfreyLine) := rfl
    rw [← hzero]
    exact sorgenfreySymm_le_symm_iff _ _ |>.mpr hreal
  · have hreal : (1 - 1 / (n + 1 : ℝ)) ≤ 1 := by linarith
    have hone : SorgenfreyLine.toReal.symm 1 = (1 : SorgenfreyLine) := rfl
    rw [← hone]
    exact sorgenfreySymm_le_symm_iff _ _ |>.mpr hreal

/-- Helper for Exercise 28.2: the canonical interval cover is directed by inclusion. -/
private lemma directed_sorgenfreyUnitIntervalCover :
    Directed (· ⊆ ·) sorgenfreyUnitIntervalCover := by
  -- A larger index has a larger cutoff, so the corresponding cover member contains both.
  intro n m
  refine ⟨max n m, ?_, ?_⟩
  · intro x hx
    rcases hx with hx | hx
    · left
      have hcast : (n + 1 : ℝ) ≤ max n m + 1 := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_max_left n m) 1
      have hrecip := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < n + 1) hcast
      simpa only [sorgenfreyUnitIntervalCover, Set.mem_preimage, Set.mem_union,
        Set.mem_Iio] using lt_of_lt_of_le hx (sub_le_sub_left hrecip 1)
    · exact Or.inr hx
  · intro x hx
    rcases hx with hx | hx
    · left
      have hcast : (m + 1 : ℝ) ≤ max n m + 1 := by
        exact_mod_cast Nat.add_le_add_right (Nat.le_max_right n m) 1
      have hrecip := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < m + 1) hcast
      simpa only [sorgenfreyUnitIntervalCover, Set.mem_preimage, Set.mem_union,
        Set.mem_Iio] using lt_of_lt_of_le hx (sub_le_sub_left hrecip 1)
    · exact Or.inr hx

/-- Helper for Exercise 28.2: the canonical cover is exhaustive, but no member is exhaustive. -/
private lemma sorgenfreyUnitIntervalCover_covers_not_single :
    (Set.univ : Set (Set.Icc (0 : SorgenfreyLine) 1)) ⊆
        ⋃ n, sorgenfreyUnitIntervalCover n ∧
      ∀ n, ¬ (Set.univ : Set (Set.Icc (0 : SorgenfreyLine) 1)) ⊆
        sorgenfreyUnitIntervalCover n := by
  constructor
  · intro x _
    -- The endpoint is in the fixed right interval; smaller points eventually lie below a cutoff.
    have hxle : SorgenfreyLine.toReal x.1 ≤ 1 := by
      have hone : SorgenfreyLine.toReal.symm 1 = (1 : SorgenfreyLine) := rfl
      exact sorgenfreyToReal_le_iff _ _ |>.mpr (by simpa only [hone] using x.2.2)
    rcases hxle.eq_or_lt with hxone | hxlt
    · refine Set.mem_iUnion.mpr ⟨0, Or.inr ?_⟩
      constructor
      · exact hxone.ge
      · simpa only [hxone] using (show (1 : ℝ) < 2 by norm_num)
    · obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hxlt)
      refine Set.mem_iUnion.mpr ⟨n, Or.inl ?_⟩
      simpa only [sorgenfreyUnitIntervalCover, Set.mem_preimage, Set.mem_union,
        Set.mem_Iio] using (show
          SorgenfreyLine.toReal x.1 < 1 - 1 / (n + 1 : ℝ) by linarith)
  · intro n hsubset
    -- The cutoff point itself belongs to `[0,1]` but to neither piece of the `n`th cover member.
    let x : Set.Icc (0 : SorgenfreyLine) 1 :=
      ⟨SorgenfreyLine.toReal.symm (1 - 1 / (n + 1 : ℝ)),
        sorgenfreyUnitIntervalCutoff_mem n⟩
    have hx := hsubset (Set.mem_univ x)
    rcases hx with hx | hx
    · simp [x] at hx
    · have hpositive : 0 < 1 / (n + 1 : ℝ) := by positivity
      have hcutoff : 1 - 1 / (n + 1 : ℝ) < 1 := by linarith
      exact (not_le_of_gt hcutoff) (by simpa [x] using hx.1)

/-- Exercise 28.2: The closed interval `[0, 1]`, with the subspace topology inherited
from the Sorgenfrey line, is not limit point compact. -/
theorem sorgenfreyIcc_not_limitPointCompact :
    ¬ LimitPointCompactSpace (Set.Icc (0 : SorgenfreyLine) 1) := by
  intro hlimit
  -- Convert limit point compactness to countable compactness using the `T₁` property.
  letI : T1Space SorgenfreyLine := sorgenfreyT1Space
  letI : CountablyCompactSpace (Set.Icc (0 : SorgenfreyLine) 1) :=
    (limitPointCompactSpace_iff_countablyCompactSpace _).mp hlimit
  obtain ⟨hcovers, hproper⟩ := sorgenfreyUnitIntervalCover_covers_not_single
  -- Countable compactness would force one directed cover member to contain the whole interval.
  obtain ⟨n, hn⟩ := CountablyCompactSpace.isCountablyCompact_univ.elim_directed_cover
    sorgenfreyUnitIntervalCover isOpen_sorgenfreyUnitIntervalCover hcovers
      directed_sorgenfreyUnitIntervalCover
  exact hproper n hn
