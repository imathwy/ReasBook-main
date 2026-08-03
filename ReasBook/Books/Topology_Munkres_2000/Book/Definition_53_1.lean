module

public import Topology_Munkres_2000.Book.Definition_53_1.Slices

public section

universe u v

/-- Definition 53.1. A set `U` is evenly covered by `p` when `U` is open and `p ⁻¹' U` is the
union of a pairwise disjoint collection of open slices, each mapped homeomorphically onto `U` by
`p`. -/
def EvenlyCovered {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    (p : E → B) (U : Set B) : Prop :=
  IsOpen U ∧ ∃ P : Partition (p ⁻¹' U), IsSlicePartition p U P

namespace EvenlyCovered

/-- An evenly covered set is open. -/
theorem isOpen {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]
    {p : E → B} {U : Set B}
    (hU : EvenlyCovered p U) : IsOpen U := hU.1

/-- An evenly covered set has a partition of its preimage into slices. -/
theorem exists_slicePartition {E : Type u} {B : Type v} [TopologicalSpace E]
    [TopologicalSpace B] {p : E → B} {U : Set B} (hU : EvenlyCovered p U) :
    ∃ P : Partition (p ⁻¹' U), IsSlicePartition p U P :=
  hU.2

end EvenlyCovered
