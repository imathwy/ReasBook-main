module

public import Topology_Munkres_2000.Book.Definition_13_3.SorgenfreyLine
public import Mathlib.Topology.Connected.TotallyDisconnected

public section

namespace SorgenfreyLine

/-- Helper for Exercise 25.1: the points whose real coordinates lie below `b`
form an open set in the Sorgenfrey line. -/
private lemma isOpen_toReal_lt (b : ℝ) : IsOpen {x : SorgenfreyLine | toReal x < b} := by
  -- Around each point below `b`, the basis interval ending at `b` stays in the ray.
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hxb
  exact ⟨Set.Ico (toReal x) b, ⟨toReal x, b, hxb, rfl⟩,
    Set.left_mem_Ico.mpr hxb, Set.Ico_subset_Iio_self⟩

/-- Helper for Exercise 25.1: the points whose real coordinates are at least
`b` form an open set in the Sorgenfrey line. -/
private lemma isOpen_toReal_ge (b : ℝ) : IsOpen {x : SorgenfreyLine | b ≤ toReal x} := by
  -- Around each point above `b`, a short basis interval remains above `b`.
  refine isTopologicalBasis_lowerLimitBasis.isOpen_iff.mpr ?_
  intro x hbx
  refine ⟨Set.Ico (toReal x) (toReal x + 1),
    ⟨toReal x, toReal x + 1, lt_add_one (toReal x), rfl⟩,
    Set.left_mem_Ico.mpr (lt_add_one (toReal x)), ?_⟩
  exact Set.Ico_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hbx)

/-- Helper for Exercise 25.1: the Sorgenfrey line is totally separated by
clopen coordinate rays. -/
private theorem totallySeparatedSpace_lowerLimit : TotallySeparatedSpace SorgenfreyLine := by
  -- Distinct points are separated by a clopen lower ray.
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro x y hxy
  have hxyReal : toReal x ≠ toReal y := toReal.injective.ne hxy
  rcases lt_or_gt_of_ne hxyReal with hxyReal | hyxReal
  · refine ⟨{z : SorgenfreyLine | toReal z < toReal y}, ⟨?_, ?_⟩, hxyReal, ?_⟩
    · rw [← isOpen_compl_iff]
      simpa only [Set.compl_setOf, not_lt] using isOpen_toReal_ge (toReal y)
    · exact isOpen_toReal_lt (toReal y)
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq, lt_self_iff_false, not_false_eq_true]
  · have hxUpper : x ∈ {z : SorgenfreyLine | toReal x ≤ toReal z} := by
      simp only [Set.mem_setOf_eq]
      exact le_refl (toReal x)
    refine ⟨{z : SorgenfreyLine | toReal x ≤ toReal z}, ⟨?_, ?_⟩, hxUpper, ?_⟩
    · rw [← isOpen_compl_iff]
      simpa only [Set.compl_setOf, not_le] using isOpen_toReal_lt (toReal x)
    · exact isOpen_toReal_ge (toReal x)
    · simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
      exact not_le_of_gt hyxReal

/-- The Sorgenfrey line is totally disconnected. -/
instance instTotallyDisconnectedSpace : TotallyDisconnectedSpace SorgenfreyLine :=
  @TotallySeparatedSpace.totallyDisconnectedSpace SorgenfreyLine _ totallySeparatedSpace_lowerLimit

end SorgenfreyLine
