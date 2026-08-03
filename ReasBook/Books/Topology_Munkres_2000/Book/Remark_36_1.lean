module

public import Mathlib.Topology.PartitionOfUnity

public section

namespace PartitionOfUnity

/-- Remark 36.1: although a partition of unity has pointwise sum equal to one on
its designated set, many applications only need this sum to be positive. -/
theorem sum_pos {ι : Type u} {X : Type v} [TopologicalSpace X] {s : Set X}
    (f : PartitionOfUnity ι X s) {x : X} (hx : x ∈ s) : 0 < ∑ᶠ i, f i x := by
  rw [f.sum_eq_one hx]
  exact zero_lt_one

end PartitionOfUnity
