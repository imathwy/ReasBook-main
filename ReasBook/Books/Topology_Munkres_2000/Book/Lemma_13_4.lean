module

public import Topology_Munkres_2000.Book.Definition_13_3.RealLine
public import Mathlib.Order.Comparable

public section

namespace RealTopology

/-- Helper for Lemma 13.4: the usual topology on the underlying real line. -/
abbrev standardRealTopology : TopologicalSpace ℝ :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace

/-- Helper for Lemma 13.4: a point of a standard-open set lies in a contained open interval. -/
lemma exists_Ioo_subset_of_standardOpen {u : Set ℝ}
    (hu : @IsOpen ℝ standardRealTopology u) {x : ℝ} (hx : x ∈ u) :
    ∃ a b : ℝ, x ∈ Set.Ioo a b ∧ Set.Ioo a b ⊆ u := by
  -- Use the canonical interval basis for neighborhoods in the standard real topology.
  exact mem_nhds_iff_exists_Ioo_subset.mp (hu.mem_nhds hx)

/-- Helper for Lemma 13.4: every standard open interval is open in the lower-limit topology. -/
lemma isOpen_Ioo_lowerLimit (a b : ℝ) :
    @IsOpen ℝ lowerLimit (Set.Ioo a b) := by
  -- Route correction: express the interval as a union of lower-limit generators.
  let S : Set (Set ℝ) := {s | ∃ x ∈ Set.Ioo a b, s = Set.Ico x b}
  have hUnion : ⋃₀ S = Set.Ioo a b := by
    apply Set.Subset.antisymm
    · intro y hy
      obtain ⟨s, hs, hys⟩ := Set.mem_sUnion.mp hy
      obtain ⟨x, hx, rfl⟩ := hs
      exact ⟨hx.1.trans_le hys.1, hys.2⟩
    · intro x hx
      apply Set.mem_sUnion.mpr
      exact ⟨Set.Ico x b, ⟨x, hx, rfl⟩, ⟨le_rfl, hx.2⟩⟩
  rw [← hUnion]
  rw [lowerLimit_eq_generateFrom]
  apply TopologicalSpace.GenerateOpen.sUnion
  intro s hs
  obtain ⟨x, hx, rfl⟩ := hs
  apply TopologicalSpace.GenerateOpen.basic
  unfold lowerLimitBasis
  exact ⟨x, b, hx.2, rfl⟩

/-- Helper for Lemma 13.4: a topology containing every ordinary open interval is
finer than the standard topology on `ℝ`. -/
lemma le_standard_of_isOpen_Ioo {t : TopologicalSpace ℝ}
    (hIoo : ∀ a b : ℝ, @IsOpen ℝ t (Set.Ioo a b)) :
    t ≤ standardRealTopology := by
  -- Transfer each standard interval neighborhood to the finer topology.
  intro u hu
  apply (@isOpen_iff_mem_nhds ℝ t u).mpr
  intro x hx
  obtain ⟨a, b, hxab, hab⟩ :=
    exists_Ioo_subset_of_standardOpen hu hx
  exact Filter.mem_of_superset
    (@IsOpen.mem_nhds ℝ t x (Set.Ioo a b) (hIoo a b) hxab) hab

/-- Helper for Lemma 13.4: every standard open interval is open in the `K`-topology. -/
lemma isOpen_Ioo_k (a b : ℝ) :
    @IsOpen ℝ k (Set.Ioo a b) := by
  -- A nonempty interval is a generator; otherwise it is the open empty set.
  by_cases hab : a < b
  · rw [k_eq_generateFrom]
    exact TopologicalSpace.isOpen_generateFrom_of_mem
      ((mem_kBasis_iff _).mpr ⟨a, b, hab, Or.inl rfl⟩)
  · rw [Set.Ioo_eq_empty hab]
    exact @isOpen_empty ℝ k

/-- Helper for Lemma 13.4: every member of `positiveReciprocals` is positive. -/
lemma positiveReciprocals_pos {x : ℝ} (hx : x ∈ positiveReciprocals) : 0 < x := by
  -- Unpack the reciprocal representation and use positivity of the natural index.
  obtain ⟨n, hn, rfl⟩ := (mem_positiveReciprocals x).mp hx
  exact inv_pos.mpr (Nat.cast_pos.mpr hn)

/-- Helper for Lemma 13.4: `positiveReciprocals` has elements arbitrarily close
to `0` from above. -/
lemma exists_positiveReciprocal_lt {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ positiveReciprocals, x < ε := by
  -- Choose a natural index larger than `ε⁻¹`, then invert the resulting inequality.
  obtain ⟨n, hn⟩ := exists_nat_gt ε⁻¹
  have hnReal : 0 < (n : ℝ) := by
    have hInv : 0 < ε⁻¹ := inv_pos.mpr hε
    exact hInv.trans hn
  have hnNat : 0 < n := Nat.cast_pos.mp hnReal
  refine ⟨(n : ℝ)⁻¹, (mem_positiveReciprocals _).mpr ⟨n, hnNat, rfl⟩, ?_⟩
  apply (inv_lt_iff_one_lt_mul₀ hnReal).mpr
  have hProduct : 1 < (n : ℝ) * ε := (inv_lt_iff_one_lt_mul₀ hε).mp hn
  simpa only [mul_comm] using hProduct

/-- Helper for Lemma 13.4: a lower-limit open neighborhood of `0` contains a right half-interval. -/
lemma exists_Ico_subset_of_lowerLimitOpen_zero {u : Set ℝ}
    (hu : @IsOpen ℝ lowerLimit u) (h0u : 0 ∈ u) :
    ∃ b : ℝ, 0 < b ∧ Set.Ico 0 b ⊆ u := by
  -- View lower-limit openness as generated openness and induct on its construction.
  rw [lowerLimit_eq_generateFrom] at hu
  induction hu with
  | basic s hs =>
      obtain ⟨a, b, hab, rfl⟩ := hs
      refine ⟨b, h0u.2, ?_⟩
      intro x hx
      exact ⟨h0u.1.trans hx.1, hx.2⟩
  | univ =>
      exact ⟨1, zero_lt_one, Set.subset_univ _⟩
  | inter s t hs ht ihs iht =>
      obtain ⟨b, hb, hbs⟩ := ihs h0u.1
      obtain ⟨c, hc, hct⟩ := iht h0u.2
      refine ⟨min b c, lt_min hb hc, ?_⟩
      intro x hx
      exact ⟨hbs ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩,
        hct ⟨hx.1, hx.2.trans_le (min_le_right _ _)⟩⟩
  | sUnion S hs ih =>
      obtain ⟨s, hsS, h0s⟩ := Set.mem_sUnion.mp h0u
      obtain ⟨b, hb, hbs⟩ := ih s hsS h0s
      exact ⟨b, hb, hbs.trans (Set.subset_sUnion_of_mem hsS)⟩

/-- Helper for Lemma 13.4: a `K`-open neighborhood of `0` contains a left open interval. -/
lemma exists_Ioo_subset_of_kOpen_zero {u : Set ℝ}
    (hu : @IsOpen ℝ k u) (h0u : 0 ∈ u) :
    ∃ a : ℝ, a < 0 ∧ Set.Ioo a 0 ⊆ u := by
  -- Induct through the generators; deleted reciprocal intervals still contain all nearby negatives.
  rw [k_eq_generateFrom] at hu
  induction hu with
  | basic s hs =>
      obtain ⟨a, b, hab, hs | hs⟩ := (mem_kBasis_iff s).mp hs
      · subst s
        refine ⟨a, h0u.1, ?_⟩
        intro x hx
        exact ⟨hx.1, hx.2.trans h0u.2⟩
      · subst s
        refine ⟨a, h0u.1.1, ?_⟩
        intro x hx
        refine ⟨⟨hx.1, hx.2.trans h0u.1.2⟩, ?_⟩
        intro hxReciprocal
        exact (not_lt_of_ge (positiveReciprocals_pos hxReciprocal).le) hx.2
  | univ =>
      exact ⟨-1, neg_lt_zero.mpr zero_lt_one, Set.subset_univ _⟩
  | inter s t hs ht ihs iht =>
      obtain ⟨a, ha, has⟩ := ihs h0u.1
      obtain ⟨c, hc, hct⟩ := iht h0u.2
      refine ⟨max a c, max_lt ha hc, ?_⟩
      intro x hx
      exact ⟨has ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩,
        hct ⟨(le_max_right _ _).trans_lt hx.1, hx.2⟩⟩
  | sUnion S hs ih =>
      obtain ⟨s, hsS, h0s⟩ := Set.mem_sUnion.mp h0u
      obtain ⟨a, ha, has⟩ := ih s hsS h0s
      exact ⟨a, ha, has.trans (Set.subset_sUnion_of_mem hsS)⟩

/-- Helper for Lemma 13.4: deleting `positiveReciprocals` from `(-1, 1)`
destroys lower-limit openness. -/
lemma deletedInterval_not_isOpen_lowerLimit :
    ¬ @IsOpen ℝ lowerLimit (Set.Ioo (-1) 1 \ positiveReciprocals) := by
  -- Any right half-neighborhood of zero contains a sufficiently small deleted reciprocal.
  intro hOpen
  have hZeroNotReciprocal : (0 : ℝ) ∉ positiveReciprocals := by
    intro hZero
    exact (lt_irrefl 0) (positiveReciprocals_pos hZero)
  have hNegOneZero : (-1 : ℝ) < 0 := by norm_num
  have hZeroOne : (0 : ℝ) < 1 := by norm_num
  have hZero : (0 : ℝ) ∈ Set.Ioo (-1) 1 \ positiveReciprocals := by
    exact ⟨⟨hNegOneZero, hZeroOne⟩, hZeroNotReciprocal⟩
  obtain ⟨b, hb, hbSubset⟩ := exists_Ico_subset_of_lowerLimitOpen_zero hOpen hZero
  obtain ⟨x, hxReciprocal, hx⟩ := exists_positiveReciprocal_lt (lt_min hb zero_lt_one)
  have hxPositive : 0 < x := positiveReciprocals_pos hxReciprocal
  have hxHalfInterval : x ∈ Set.Ico 0 b := by
    exact ⟨hxPositive.le, hx.trans_le (min_le_left _ _)⟩
  have hxDeleted := hbSubset hxHalfInterval
  exact hxDeleted.2 hxReciprocal

/-- Helper for Lemma 13.4: `[0, 1)` is not open in the `K`-topology. -/
lemma ico_zero_one_not_isOpen_k :
    ¬ @IsOpen ℝ k (Set.Ico 0 1) := by
  -- A `K`-open neighborhood of `0` would contain a negative point,
  -- contradicting the set's lower bound.
  intro hOpen
  obtain ⟨a, ha, haSubset⟩ := exists_Ioo_subset_of_kOpen_zero hOpen ⟨le_rfl, zero_lt_one⟩
  have hMid : a / 2 ∈ Set.Ioo a 0 := by
    constructor <;> linarith
  exact (not_lt_of_ge (haSubset hMid).1) hMid.2

/-- Lemma 13.4 (1). In Lean's reversed order on topologies, the lower-limit
topology on `ℝ` is strictly finer than the standard topology. -/
theorem lowerLimit_lt_standard :
    lowerLimit < (inferInstance : TopologicalSpace ℝ) := by
  -- Ordinary intervals give the non-strict comparison; `[0,1)` witnesses strictness.
  apply lt_of_le_not_ge (le_standard_of_isOpen_Ioo isOpen_Ioo_lowerLimit)
  intro hStandardLower
  have hLowerOpen : @IsOpen ℝ lowerLimit (Set.Ico 0 1) := by
    rw [lowerLimit_eq_generateFrom]
    apply TopologicalSpace.GenerateOpen.basic
    unfold lowerLimitBasis
    exact ⟨0, 1, zero_lt_one, rfl⟩
  have hStandardOpen : @IsOpen ℝ standardRealTopology (Set.Ico 0 1) :=
    hStandardLower _ hLowerOpen
  have hNeighborhood : Set.Ico 0 1 ∈ @nhds ℝ standardRealTopology 0 :=
    hStandardOpen.mem_nhds ⟨le_rfl, zero_lt_one⟩
  exact (lt_irrefl 0) (Ico_mem_nhds_iff.mp hNeighborhood).1

/-- Companion result for Lemma 13.4 (2). In Lean's reversed order on topologies, the `K`-topology
on `ℝ` is strictly finer than the standard topology. -/
theorem k_lt_standard :
    k < (inferInstance : TopologicalSpace ℝ) := by
  -- The deleted interval is `K`-open but cannot be standard-open, since standard openness transfers
  -- to lower-limit openness.
  apply lt_of_le_not_ge (le_standard_of_isOpen_Ioo isOpen_Ioo_k)
  intro hStandardK
  have hNegOneOne : (-1 : ℝ) < 1 := by norm_num
  have hKOpen : @IsOpen ℝ k (Set.Ioo (-1) 1 \ positiveReciprocals) := by
    rw [k_eq_generateFrom]
    exact TopologicalSpace.isOpen_generateFrom_of_mem
      ((mem_kBasis_iff _).mpr ⟨-1, 1, hNegOneOne, Or.inr rfl⟩)
  have hStandardOpen :
      @IsOpen ℝ standardRealTopology (Set.Ioo (-1) 1 \ positiveReciprocals) :=
    hStandardK _ hKOpen
  have hLowerOpen : @IsOpen ℝ lowerLimit (Set.Ioo (-1) 1 \ positiveReciprocals) :=
    le_standard_of_isOpen_Ioo isOpen_Ioo_lowerLimit _ hStandardOpen
  exact deletedInterval_not_isOpen_lowerLimit hLowerOpen

/-- Companion result for Lemma 13.4 (3). The lower-limit topology and the `K`-topology on `ℝ` are
incomparable. -/
theorem lowerLimit_k_incomparable :
    IncompRel (· ≤ ·) lowerLimit k := by
  -- Each failed comparison is witnessed by the canonical open set from the corresponding topology.
  constructor
  · intro hLowerK
    have hNegOneOne : (-1 : ℝ) < 1 := by norm_num
    have hKOpen : @IsOpen ℝ k (Set.Ioo (-1) 1 \ positiveReciprocals) := by
      rw [k_eq_generateFrom]
      exact TopologicalSpace.isOpen_generateFrom_of_mem
        ((mem_kBasis_iff _).mpr ⟨-1, 1, hNegOneOne, Or.inr rfl⟩)
    exact deletedInterval_not_isOpen_lowerLimit (hLowerK _ hKOpen)
  · intro hKLower
    have hLowerOpen : @IsOpen ℝ lowerLimit (Set.Ico 0 1) := by
      rw [lowerLimit_eq_generateFrom]
      apply TopologicalSpace.GenerateOpen.basic
      unfold lowerLimitBasis
      exact ⟨0, 1, zero_lt_one, rfl⟩
    exact ico_zero_one_not_isOpen_k (hKLower _ hLowerOpen)

end RealTopology
