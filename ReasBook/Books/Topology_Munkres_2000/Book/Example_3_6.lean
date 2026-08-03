module

public import Topology_Munkres_2000.Book.Definition_3_6
public import Mathlib.Algebra.Module.Prod
public import Mathlib.Data.Real.Basic
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic

public section

/-- The collection of all straight lines in the real plane. -/
def realPlaneLines : Set (Set (ℝ × ℝ)) :=
  {s | ∃ p q : ℝ × ℝ, p ≠ q ∧ s = (line[ℝ, p, q] : Set (ℝ × ℝ))}

/-- Membership in `realPlaneLines` means being the affine span of two distinct points. -/
@[simp]
theorem mem_realPlaneLines (s : Set (ℝ × ℝ)) :
    s ∈ realPlaneLines ↔
      ∃ p q : ℝ × ℝ, p ≠ q ∧ s = (line[ℝ, p, q] : Set (ℝ × ℝ)) :=
  Iff.rfl

/-- The affine span of two distinct points is a member of `realPlaneLines`. -/
theorem line_mem_realPlaneLines {p q : ℝ × ℝ} (h : p ≠ q) :
    (line[ℝ, p, q] : Set (ℝ × ℝ)) ∈ realPlaneLines :=
  ⟨p, q, h, rfl⟩

/-- Two distinct members of `realPlaneLines` can have a common point. -/
theorem exists_intersecting_realPlaneLines :
    ∃ l₁ ∈ realPlaneLines, ∃ l₂ ∈ realPlaneLines,
      l₁ ≠ l₂ ∧ (l₁ ∩ l₂).Nonempty := by
  -- Choose the horizontal and vertical coordinate axes.
  refine ⟨(line[ℝ, ((0, 0) : ℝ × ℝ), (1, 0)] : Set (ℝ × ℝ)), ?_,
    (line[ℝ, ((0, 0) : ℝ × ℝ), (0, 1)] : Set (ℝ × ℝ)), ?_, ?_, ?_⟩
  · exact line_mem_realPlaneLines (by norm_num)
  · exact line_mem_realPlaneLines (by norm_num)
  · -- The point `(1, 0)` distinguishes the two axes.
    intro hLines
    have hHorizontal :
        ((1, 0) : ℝ × ℝ) ∈
          (line[ℝ, ((0, 0) : ℝ × ℝ), (1, 0)] : Set (ℝ × ℝ)) :=
      right_mem_affineSpan_pair ℝ _ _
    have hVertical :
        ((1, 0) : ℝ × ℝ) ∈
          (line[ℝ, ((0, 0) : ℝ × ℝ), (0, 1)] : Set (ℝ × ℝ)) := by
      rw [← hLines]
      exact hHorizontal
    have hVerticalAffine :
        ((1, 0) : ℝ × ℝ) ∈ line[ℝ, ((0, 0) : ℝ × ℝ), (0, 1)] :=
      hVertical
    rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hVerticalAffine
    obtain ⟨c, hc⟩ := hVerticalAffine
    simpa [AffineMap.lineMap_apply_module] using congrArg Prod.fst hc
  · -- The origin belongs to both coordinate axes.
    refine ⟨(0, 0), ?_, ?_⟩
    · exact left_mem_affineSpan_pair ℝ _ _
    · exact left_mem_affineSpan_pair ℝ _ _

/-- The collection of real-plane lines is not pairwise disjoint. -/
theorem realPlaneLinesNotPairwiseDisjoint :
    ¬ realPlaneLines.PairwiseDisjoint id := by
  -- Intersecting distinct members contradict pairwise disjointness.
  intro hPairwise
  obtain ⟨l₁, hl₁, l₂, hl₂, hne, hIntersection⟩ :=
    exists_intersecting_realPlaneLines
  have hDisjoint : Disjoint l₁ l₂ := hPairwise hl₁ hl₂ hne
  obtain ⟨point, hPoint₁, hPoint₂⟩ := hIntersection
  exact Set.disjoint_left.mp hDisjoint hPoint₁ hPoint₂

/-- Example 3.6: The collection of all straight lines in the real plane is not a partition. -/
theorem realPlaneLinesNotPartition :
    ¬ Setoid.IsPartition realPlaneLines := by
  -- Every partition is pairwise disjoint, contrary to the preceding obstruction.
  intro hPartition
  exact realPlaneLinesNotPairwiseDisjoint hPartition.pairwiseDisjoint
