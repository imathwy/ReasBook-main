module

public import Mathlib.Topology.Compactness.CompactlyCoherentSpace

public section

open Set Set.Notation

universe u

namespace CompactlyCoherentSpace

/-- Example 46.2. The criterion defining a compactly generated space using open sets is
 equivalent to the corresponding criterion using closed sets. -/
theorem openCriterion_iff_closedCriterion (X : Type u) [TopologicalSpace X] :
    (∀ A : Set X, (∀ K : Set X, IsCompact K → IsOpen (K ↓∩ A)) → IsOpen A) ↔
      ∀ B : Set X, (∀ K : Set X, IsCompact K → IsClosed (K ↓∩ B)) → IsClosed B := by
  constructor
  · intro h_open B hB
    rw [← isOpen_compl_iff]
    apply h_open
    intro K hK
    simpa only [preimage_compl] using (hB K hK).isOpen_compl
  · intro h_closed A hA
    rw [← isClosed_compl_iff]
    apply h_closed
    intro K hK
    simpa only [preimage_compl] using (hA K hK).isClosed_compl

end CompactlyCoherentSpace
