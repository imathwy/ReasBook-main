module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Topology.Separation.Regular

public section

namespace SorgenfreyLine

/-- Helper for Example 31.2: the complement of a singleton is open in the
Sorgenfrey line. -/
private lemma isOpen_compl_singleton_lowerLimit (x : SorgenfreyLine) :
    IsOpen (({x} : Set SorgenfreyLine)ᶜ) := by
  -- At every other point, choose a half-open interval that stays on its side of `x`.
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro y hy
  have hyx : y ≠ x := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hy
  have hyxReal : toReal y ≠ toReal x := toReal.injective.ne hyx
  rcases lt_or_gt_of_ne hyxReal with hyx | hxy
  · refine ⟨Set.Ico (toReal y) (toReal x), ?_, Set.left_mem_Ico.mpr hyx, ?_⟩
    · exact ⟨toReal y, toReal x, hyx, rfl⟩
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact ne_of_lt hz.2
  · refine ⟨Set.Ico (toReal y) (toReal y + (1 : ℝ)), ?_, ?_, ?_⟩
    · exact ⟨toReal y, toReal y + (1 : ℝ), lt_add_one (toReal y), rfl⟩
    · exact Set.left_mem_Ico.mpr (lt_add_one (toReal y))
    · intro z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hzx ↦ (not_le_of_gt hxy) (hzx ▸ hz.1)

/-- Helper for Example 31.2: every open neighborhood contains a half-open
interval whose left endpoint is the chosen point. -/
private lemma exists_Ico_subset_of_mem_open {U : Set SorgenfreyLine} {x : SorgenfreyLine}
    (hU : IsOpen U) (hxU : x ∈ U) :
    ∃ b : ℝ, toReal x < b ∧ Set.Ico (toReal x) b ⊆ U := by
  -- First refine to a basis interval, then move its left endpoint up to `x`.
  obtain ⟨v, ⟨a, b, hab, rfl⟩, hxv, hvU⟩ :=
    isTopologicalBasis_lowerLimitBasis.exists_subset_of_mem_open hxU hU
  refine ⟨b, hxv.2, ?_⟩
  intro y hy
  exact hvU ⟨hxv.1.trans hy.1, hy.2⟩

/-- Helper for Example 31.2: two unions of based half-open intervals are
disjoint when every interval avoids the opposite set of base points. -/
private lemma disjoint_iUnion_Ico_of_cross_subset_compl
    (A B : Set SorgenfreyLine) (r : A → ℝ) (s : B → ℝ)
    (hr : ∀ a : A, Set.Ico (toReal a) (r a) ⊆ Bᶜ)
    (hs : ∀ b : B, Set.Ico (toReal b) (s b) ⊆ Aᶜ) :
    Disjoint (⋃ a : A, Set.Ico (toReal a) (r a))
      (⋃ b : B, Set.Ico (toReal b) (s b)) := by
  -- An intersection point orders the two base points, forcing one into the other interval.
  refine Set.disjoint_left.mpr ?_
  intro x hxA hxB
  obtain ⟨a, hxa⟩ := Set.mem_iUnion.mp hxA
  obtain ⟨b, hxb⟩ := Set.mem_iUnion.mp hxB
  rcases le_total (toReal a) (toReal b) with hab | hba
  · have hbInterval : (b : SorgenfreyLine) ∈ Set.Ico (toReal a) (r a) :=
      ⟨hab, hxb.1.trans_lt hxa.2⟩
    exact (hr a hbInterval) b.property
  · have haInterval : (a : SorgenfreyLine) ∈ Set.Ico (toReal b) (s b) :=
      ⟨hba, hxa.1.trans_lt hxb.2⟩
    exact (hs b haInterval) a.property

/-- Example 31.2: The Sorgenfrey line is normal in the `T₄` convention. -/
instance instT4Space : T4Space SorgenfreyLine where
  t1 x := by
    -- Closed singletons follow from the explicitly open complements above.
    exact isOpen_compl_iff.mp (isOpen_compl_singleton_lowerLimit x)
  normal A B hA hB hAB := by
    classical
    -- Choose a based half-open interval around each point that avoids the opposite closed set.
    have hAIntervals : ∀ a : A,
        ∃ endpoint : ℝ, toReal a < endpoint ∧ Set.Ico (toReal a) endpoint ⊆ Bᶜ := by
      intro a
      apply exists_Ico_subset_of_mem_open hB.isOpen_compl
      exact fun haB ↦ Set.disjoint_left.mp hAB a.property haB
    have hBIntervals : ∀ b : B,
        ∃ endpoint : ℝ, toReal b < endpoint ∧ Set.Ico (toReal b) endpoint ⊆ Aᶜ := by
      intro b
      apply exists_Ico_subset_of_mem_open hA.isOpen_compl
      exact fun hbA ↦ Set.disjoint_left.mp hAB hbA b.property
    choose r hrlt hrAvoid using hAIntervals
    choose s hslt hsAvoid using hBIntervals
    refine ⟨⋃ a : A, Set.Ico (toReal a) (r a),
      ⋃ b : B, Set.Ico (toReal b) (s b), ?_, ?_, ?_, ?_, ?_⟩
    · -- Each chosen interval is a basis open, so their union is open.
      refine isOpen_iUnion fun a ↦ isTopologicalBasis_lowerLimitBasis.isOpen ?_
      exact ⟨toReal a, r a, hrlt a, rfl⟩
    · refine isOpen_iUnion fun b ↦ isTopologicalBasis_lowerLimitBasis.isOpen ?_
      exact ⟨toReal b, s b, hslt b, rfl⟩
    · -- Every base point belongs to its own chosen interval.
      intro a ha
      exact Set.mem_iUnion.mpr ⟨⟨a, ha⟩, Set.left_mem_Ico.mpr (hrlt ⟨a, ha⟩)⟩
    · intro b hb
      exact Set.mem_iUnion.mpr ⟨⟨b, hb⟩, Set.left_mem_Ico.mpr (hslt ⟨b, hb⟩)⟩
    · exact disjoint_iUnion_Ico_of_cross_subset_compl A B r s hrAvoid hsAvoid

end SorgenfreyLine
