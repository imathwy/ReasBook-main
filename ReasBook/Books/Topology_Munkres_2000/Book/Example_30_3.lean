module

public import Topology_Munkres_2000.Book.Exercise_21_4.Countability
public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Topology.Compactness.Lindelof

public section

open scoped Topology

namespace SorgenfreyLine

/-- The half-open intervals `[x, x + 1/(n+1))` form a countable neighborhood basis at
`x` in the Sorgenfrey line. -/
theorem nhdsBasis_Ico (x : SorgenfreyLine) :
    (𝓝 x).HasBasis (fun _ : ℕ ↦ True) fun n ↦
      toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1 / ((n : ℝ) + 1)) := by
  -- Refine each canonical half-open neighborhood by a sufficiently short reciprocal interval.
  refine isTopologicalBasis_lowerLimitBasis.nhds_hasBasis.to_hasBasis
    (p' := fun _ : ℕ ↦ True)
    (s' := fun n ↦ toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1 / ((n : ℝ) + 1))) ?_ ?_
  · rintro s ⟨⟨a, b, hab, rfl⟩, hxs⟩
    change toReal x ∈ Set.Ico a b at hxs
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hxs.2)
    refine ⟨n, trivial, ?_⟩
    intro y hy
    have hyReal : toReal y ∈ Set.Ico (toReal x) (toReal x + 1 / ((n : ℝ) + 1)) := hy
    have hright : toReal x + 1 / ((n : ℝ) + 1) < b := by
      linarith
    change toReal y ∈ Set.Ico a b
    exact ⟨hxs.1.trans hyReal.1, hyReal.2.trans hright⟩
  · intro n _
    have hpositive : 0 < 1 / ((n : ℝ) + 1) := by
      positivity
    have hendpoint : toReal x < toReal x + 1 / ((n : ℝ) + 1) :=
      lt_add_of_pos_right _ hpositive
    refine ⟨toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1 / ((n : ℝ) + 1)), ?_, Set.Subset.rfl⟩
    exact ⟨⟨toReal x, toReal x + 1 / ((n : ℝ) + 1), hendpoint, rfl⟩,
      Set.left_mem_Ico.mpr hendpoint⟩

/-- The rational points are dense in the Sorgenfrey line. -/
theorem dense_ratCast :
    Dense (Set.range (fun q : ℚ ↦ toReal.symm (q : ℝ))) := by
  -- Every nonempty canonical interval contains a rational point.
  refine isTopologicalBasis_lowerLimitBasis.dense_iff.mpr ?_
  rintro s ⟨a, b, hab, rfl⟩ ⟨x, hx⟩
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn hab
  refine ⟨toReal.symm (q : ℝ), ?_, Set.mem_range_self q⟩
  exact ⟨haq.le, hqb⟩

/-- The Sorgenfrey line is separable. -/
instance instSeparableSpace : TopologicalSpace.SeparableSpace SorgenfreyLine where
  -- The rational points form the required countable dense subset.
  exists_countable_dense :=
    ⟨Set.range (fun q : ℚ ↦ toReal.symm (q : ℝ)), Set.countable_range _, dense_ratCast⟩

/-- Every topological basis of the Sorgenfrey line is uncountable. -/
theorem isTopologicalBasis_not_countable
    (B : Set (Set SorgenfreyLine)) (hB : TopologicalSpace.IsTopologicalBasis B) :
    ¬ B.Countable := by
  classical
  -- Choose a basis element based at each point and contained in its unit half-open interval.
  have hchoice : ∀ x : SorgenfreyLine, ∃ U ∈ B,
      x ∈ U ∧ U ⊆ toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1) := by
    intro x
    have hopen : IsOpen (toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1)) := by
      apply isTopologicalBasis_lowerLimitBasis.isOpen
      exact ⟨toReal x, toReal x + 1, lt_add_one _, rfl⟩
    have hxInterval : x ∈ toReal ⁻¹' Set.Ico (toReal x) (toReal x + 1) :=
      Set.left_mem_Ico.mpr (lt_add_one (toReal x))
    exact hB.exists_subset_of_mem_open hxInterval hopen
  choose U hUB hxU hU using hchoice
  have hUinjective : Function.Injective U := by
    intro x y hxy
    have hyUx : y ∈ U x := by
      rw [hxy]
      exact hxU y
    have hxUy : x ∈ U y := by
      rw [← hxy]
      exact hxU x
    have hxy' : toReal x ≤ toReal y := ((hU x) hyUx).1
    have hyx : toReal y ≤ toReal x := ((hU y) hxUy).1
    exact toReal.injective (le_antisymm hxy' hyx)
  intro hBcountable
  -- Injecting the uncountable carrier into a countable basis gives the contradiction.
  have hRangeSubset : Set.range U ⊆ B := by
    intro V hV
    obtain ⟨x, hx⟩ := hV
    rw [← hx]
    exact hUB x
  have hRangeCountable : (Set.range U).Countable := hBcountable.mono hRangeSubset
  have hCountable : Countable SorgenfreyLine := by
    letI : Countable (Set.range U) := Set.countable_coe_iff.mpr hRangeCountable
    let rangeMap : SorgenfreyLine → Set.range U := fun x ↦ ⟨U x, Set.mem_range_self x⟩
    have hRangeMapInjective : Function.Injective rangeMap := by
      intro x y hxy
      apply hUinjective
      exact congrArg Subtype.val hxy
    exact hRangeMapInjective.countable
  have hUncountable : Uncountable SorgenfreyLine :=
    (toReal.uncountable_iff).mpr inferInstance
  exact hUncountable.not_countable hCountable

/-- The Sorgenfrey line is not second-countable. -/
theorem notSecondCountable : ¬ SecondCountableTopology SorgenfreyLine := by
  -- A second-countable topology would supply a forbidden countable basis.
  intro hSecondCountable
  letI : SecondCountableTopology SorgenfreyLine := hSecondCountable
  obtain ⟨B, hBcountable, _, hB⟩ := TopologicalSpace.exists_countable_basis SorgenfreyLine
  exact isTopologicalBasis_not_countable B hB hBcountable

/-- Helper for Example 30.3: the points outside the union of the interiors of a covering
family of half-open real intervals form a countable set. -/
private lemma countable_compl_iUnion_Ioo_of_iUnion_Ico_eq_univ
    {ι : Type*} (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hcover : (Set.univ : Set ℝ) ⊆ ⋃ i, Set.Ico (a i) (b i)) :
    ((⋃ i, Set.Ioo (a i) (b i))ᶜ).Countable := by
  classical
  let D : Set ℝ := (⋃ i, Set.Ioo (a i) (b i))ᶜ
  have hindex : ∀ x : D, ∃ i, x.1 ∈ Set.Ico (a i) (b i) := by
    intro x
    simpa only [Set.mem_iUnion] using hcover (Set.mem_univ x.1)
  choose index hindex using hindex
  have hleftEndpoint : ∀ x : D, x.1 = a (index x) := by
    intro x
    have hxNotInterior : x.1 ∉ Set.Ioo (a (index x)) (b (index x)) := by
      intro hxInterior
      exact x.2 (Set.mem_iUnion.mpr ⟨index x, hxInterior⟩)
    exact le_antisymm (le_of_not_gt fun hlt ↦ hxNotInterior ⟨hlt, (hindex x).2⟩) (hindex x).1
  have hrational : ∀ x : D, ∃ q : ℚ, x.1 < (q : ℝ) ∧ (q : ℝ) < b (index x) := by
    intro x
    rw [hleftEndpoint x]
    exact exists_rat_btwn (hab (index x))
  choose rational hxrational hrationalb using hrational
  have hstrictMono : ∀ {x y : D}, x.1 < y.1 → (rational x : ℝ) < rational y := by
    intro x y hxy
    by_contra hnot
    have hyInside : y.1 ∈ Set.Ioo (a (index x)) (b (index x)) := by
      constructor
      · rwa [← hleftEndpoint x]
      · exact (hxrational y).trans_le (le_of_not_gt hnot) |>.trans (hrationalb x)
    exact y.2 (Set.mem_iUnion.mpr ⟨index x, hyInside⟩)
  have hrationalInjective : Function.Injective rational := by
    intro x y hxy
    apply Subtype.ext
    apply le_antisymm
    · by_contra hnot
      have hyx : y.1 < x.1 := lt_of_not_ge hnot
      exact (hstrictMono hyx).ne (congrArg ((↑) : ℚ → ℝ) hxy).symm
    · by_contra hnot
      have hxy' : x.1 < y.1 := lt_of_not_ge hnot
      exact (hstrictMono hxy').ne (congrArg ((↑) : ℚ → ℝ) hxy)
  have hDCountable : Countable D := hrationalInjective.countable
  rw [Set.countable_coe_iff] at hDCountable
  exact hDCountable

/-- Helper for Example 30.3: every covering family of nonempty half-open real intervals
has a countable subfamily that still covers `ℝ`. -/
private lemma exists_countable_Ico_subcover
    {ι : Type*} (a b : ι → ℝ) (hab : ∀ i, a i < b i)
    (hcover : (Set.univ : Set ℝ) ⊆ ⋃ i, Set.Ico (a i) (b i)) :
    ∃ t : Set ι, t.Countable ∧
      (Set.univ : Set ℝ) ⊆ ⋃ i ∈ t, Set.Ico (a i) (b i) := by
  classical
  let C : Set ℝ := ⋃ i, Set.Ioo (a i) (b i)
  let D : Set ℝ := Cᶜ
  have hDCountable : D.Countable :=
    countable_compl_iUnion_Ioo_of_iUnion_Ico_eq_univ a b hab hcover
  have hDindex : ∀ x : D, ∃ i, x.1 ∈ Set.Ico (a i) (b i) := by
    intro x
    simpa only [Set.mem_iUnion] using hcover (Set.mem_univ x.1)
  choose boundaryIndex hboundary using hDindex
  have hBoundaryIndices : (Set.range boundaryIndex).Countable := by
    have hDTypeCountable : Countable D := Set.countable_coe_iff.mpr hDCountable
    exact Set.countable_range boundaryIndex
  have hCOpenCover : C ⊆ ⋃ i, Set.Ioo (a i) (b i) := Set.Subset.rfl
  obtain ⟨interiorIndices, hInteriorCountable, hInteriorCover⟩ :=
    (HereditarilyLindelofSpace.isLindelof C).elim_countable_subcover
      (fun i ↦ Set.Ioo (a i) (b i)) (fun _ ↦ isOpen_Ioo) hCOpenCover
  refine ⟨Set.range boundaryIndex ∪ interiorIndices,
    hBoundaryIndices.union hInteriorCountable, ?_⟩
  -- Points of `C` use the ordinary-open subcover; points of `D` use their chosen intervals.
  intro x _
  by_cases hxC : x ∈ C
  · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hInteriorCover hxC)
    obtain ⟨hiIndex, hxInterior⟩ := Set.mem_iUnion.mp hi
    refine Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Set.mem_union_right _ hiIndex, ?_⟩⟩
    exact ⟨hxInterior.1.le, hxInterior.2⟩
  · let xD : D := ⟨x, hxC⟩
    refine Set.mem_iUnion.mpr ⟨boundaryIndex xD,
      Set.mem_iUnion.mpr ⟨Set.mem_union_left _ (Set.mem_range_self xD), hboundary xD⟩⟩

/-- Helper for Example 30.3: the whole Sorgenfrey line is a Lindelöf subset of itself. -/
private lemma isLindelof_univ_sorgenfrey : IsLindelof (Set.univ : Set SorgenfreyLine) := by
  classical
  -- Refine an arbitrary Sorgenfrey-open cover to canonical half-open intervals.
  refine isLindelof_of_countable_subcover fun U hUOpen hUCover ↦ ?_
  have hcoverIndex : ∀ x : SorgenfreyLine, ∃ i, x ∈ U i := by
    intro x
    simpa only [Set.mem_iUnion] using hUCover (Set.mem_univ x)
  choose coverIndex hxCover using hcoverIndex
  have hinterval : ∀ x : SorgenfreyLine, ∃ a b : ℝ, a < b ∧
      x ∈ toReal ⁻¹' Set.Ico a b ∧ toReal ⁻¹' Set.Ico a b ⊆ U (coverIndex x) := by
    intro x
    obtain ⟨V, ⟨a, b, hab, rfl⟩, hxV, hVU⟩ :=
      isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open
        (hxCover x) (hUOpen (coverIndex x))
    exact ⟨a, b, hab, hxV, hVU⟩
  choose a b hab hxInterval hintervalSubset using hinterval
  have hRealCover : (Set.univ : Set ℝ) ⊆ ⋃ x, Set.Ico (a x) (b x) := by
    intro y _
    let x : SorgenfreyLine := toReal.symm y
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    have hxReal : toReal x ∈ Set.Ico (a x) (b x) := hxInterval x
    rwa [toReal.apply_symm_apply] at hxReal
  obtain ⟨points, hPointsCountable, hPointsCover⟩ :=
    exists_countable_Ico_subcover a b hab hRealCover
  refine ⟨coverIndex '' points, hPointsCountable.image coverIndex, ?_⟩
  -- Enlarge each chosen half-open interval back to its original cover member.
  intro x _
  have hxReal : toReal x ∈ Set.univ := Set.mem_univ _
  obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hPointsCover hxReal)
  obtain ⟨hyPoints, hxIntervalChosen⟩ := Set.mem_iUnion.mp hy
  have hyImage : coverIndex y ∈ coverIndex '' points :=
    Set.mem_image coverIndex points (coverIndex y) |>.mpr ⟨y, hyPoints, rfl⟩
  refine Set.mem_iUnion.mpr ⟨coverIndex y, Set.mem_iUnion.mpr ⟨hyImage, ?_⟩⟩
  exact hintervalSubset y hxIntervalChosen

/-- Example 30.3: The Sorgenfrey line is Lindelöf. -/
-- Assemble the standard space-level instance from the proved Lindelöfness of `Set.univ`.
instance instLindelofSpace : LindelofSpace SorgenfreyLine :=
  ⟨isLindelof_univ_sorgenfrey⟩

end SorgenfreyLine
