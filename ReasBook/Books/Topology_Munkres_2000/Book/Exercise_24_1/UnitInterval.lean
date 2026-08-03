module

public import Mathlib.Topology.Instances.Real.Lemmas

public section

open Set

namespace UnitInterval

/-- The open real unit interval is contained in the closed real unit interval. -/
theorem open_subset_closed : Ioo (0 : ℝ) 1 ⊆ Icc (0 : ℝ) 1 :=
  fun _ hx ↦ mem_Icc_of_Ioo hx

/-- The canonical inclusion of the open real unit interval into the closed real unit interval. -/
@[expose]
def openInClosed : Ioo (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
  Set.inclusion open_subset_closed

/-- The canonical inclusion preserves the underlying real value. -/
@[simp]
theorem coe_openInClosed (x : Ioo (0 : ℝ) 1) : (openInClosed x : ℝ) = x := rfl

/-- The canonical inclusion of the open unit interval is a topological embedding. -/
theorem isEmbedding_openInClosed : Topology.IsEmbedding openInClosed :=
  Topology.IsEmbedding.inclusion open_subset_closed

/-- The canonical inclusion of the open unit interval has dense range. -/
theorem isDenseEmbedding_openInClosed : IsDenseEmbedding openInClosed := by
  -- The open interval is dense in the closed interval because its closure adds the endpoints.
  have hclosure : Icc (0 : ℝ) 1 ⊆ closure (Ioo (0 : ℝ) 1) := by
    rw [closure_Ioo]
    norm_num
  have hdense : DenseRange (Set.inclusion open_subset_closed) :=
    (denseRange_inclusion_iff open_subset_closed).2 hclosure
  refine { isEmbedding_openInClosed with dense := ?_ }
  simpa only [openInClosed] using hdense

end UnitInterval
