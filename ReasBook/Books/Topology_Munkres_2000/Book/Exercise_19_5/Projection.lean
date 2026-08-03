module

public import Topology_Munkres_2000.Book.Proposition_19_3.Comparison

public section

universe u v

open scoped Topology

namespace Pi

/-- Each coordinate projection from a dependent product with the box topology is continuous. -/
theorem continuous_box_apply {ι : Type u} {X : ι → Type v}
    [(i : ι) → TopologicalSpace (X i)] (i : ι) :
    Continuous[boxTopologicalSpace X, _] (fun x : (i : ι) → X i ↦ x i) := by
  -- Refining the product topology to the box topology preserves continuity.
  exact continuous_le_dom box_le_product (continuous_apply i)

end Pi
