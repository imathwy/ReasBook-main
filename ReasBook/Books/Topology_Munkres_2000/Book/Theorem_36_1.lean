module

public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Sets.OpenCover

public section

open Set TopologicalSpace

universe u v

namespace PartitionOfUnity

/-- Theorem 36.1 (Existence of finite partitions of unity). A finite indexed open
cover of a normal space admits a partition of unity subordinate to that cover. -/
theorem exists_isSubordinate_of_finite {ι : Type u} [Finite ι] {X : Type v}
    [TopologicalSpace X] [NormalSpace X] (U : ι → Opens X) (hU : IsOpenCover U) :
    ∃ ρ : PartitionOfUnity ι X univ, ρ.IsSubordinate fun i ↦ U i := by
  exact exists_isSubordinate_of_locallyFinite isClosed_univ (fun i ↦ (U i : Set X))
    (fun i ↦ (U i).2) (locallyFinite_of_finite fun i ↦ (U i : Set X)) (by
      simpa only [hU.iSup_set_eq_univ] using (Subset.rfl : univ ⊆ univ))

end PartitionOfUnity
