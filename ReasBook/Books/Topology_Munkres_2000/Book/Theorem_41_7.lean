module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Sets.OpenCover

public section

universe u v

namespace TopologicalSpace.IsOpenCover

/-- Theorem 41.7. A paracompact Hausdorff space admits a partition of unity
subordinate to every indexed open cover. -/
theorem exists_partitionOfUnity {ι : Type u} {X : Type v} [TopologicalSpace X]
    [ParacompactSpace X] [T2Space X] {U : ι → Opens X} (hU : IsOpenCover U) :
    ∃ ρ : PartitionOfUnity ι X Set.univ,
      ρ.IsSubordinate fun i ↦ (U i : Set X) := by
  apply PartitionOfUnity.exists_isSubordinate isClosed_univ
  · exact fun i ↦ (U i).isOpen
  · simp [hU.iSup_set_eq_univ]

end TopologicalSpace.IsOpenCover
