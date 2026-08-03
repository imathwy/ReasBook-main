module

public import Mathlib.Topology.UniformSpace.CompactConvergence
public import Mathlib.Topology.MetricSpace.Defs

public section

open Filter Set

universe u v

/-- Corollary 46.6. The compact-convergence limit of a sequence of continuous maps
from a compactly generated space to a metric space is continuous. -/
theorem continuous_of_tendsto_compactConvergence {X : Type u} {Y : Type v}
    [TopologicalSpace X] [CompactlyCoherentSpace X] [MetricSpace Y]
    (F : ℕ → X → Y) (f : X → Y) (h_continuous : ∀ n, Continuous (F n))
    (h_tendsto : Tendsto
      (fun n ↦ UniformOnFun.ofFun {K : Set X | IsCompact K} (F n)) atTop
      (nhds (UniformOnFun.ofFun {K : Set X | IsCompact K} f))) :
    Continuous f := by
  exact
    (UniformOnFun.isClosed_setOf_continuous CompactlyCoherentSpace.isCoherentWith).mem_of_tendsto
      h_tendsto (.of_forall h_continuous)

end
