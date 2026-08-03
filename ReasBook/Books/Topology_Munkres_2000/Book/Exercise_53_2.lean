module

public import Topology_Munkres_2000.Book.Definition_53_1
public import Topology_Munkres_2000.Book.Exercise_53_2.Slices

public section

universe u v

namespace EvenlyCovered

/-- Exercise 53.2: If a connected set `U` is evenly covered by `p`, then its partition into
slices is unique. -/
theorem existsUnique_slicePartition {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} (hU : EvenlyCovered p U)
    (hU_preconnected : IsPreconnected U) :
    ∃! P : Partition (p ⁻¹' U), IsSlicePartition p U P := by
  -- First choose the slice partition supplied by the even covering.
  obtain ⟨P, hP⟩ := hU.exists_slicePartition
  -- Preconnectedness identifies every competing slice partition with this one.
  exact ⟨P, hP, fun Q hQ ↦ IsSlicePartition.eq_of_isPreconnected hU_preconnected hQ hP⟩

end EvenlyCovered
