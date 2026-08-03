module

public import Topology_Munkres_2000.Book.Definition_43_9.Evaluation
public import Mathlib.Topology.CompactOpen

public section

universe u v

namespace ContinuousMap

variable {X : Type u} {Y : Type v}
variable [TopologicalSpace X] [TopologicalSpace Y]

/-- Theorem 46.10. If `X` is locally compact, the evaluation map
`X × C(X, Y) → Y` is continuous when `C(X, Y)` has the compact-open topology.
This sharpens the source's locally compact Hausdorff hypothesis. -/
theorem continuousEvaluation_compactOpen [LocallyCompactSpace X] :
    Continuous (evaluation X Y) := by
  rw [evaluation_eq_comp_swap]
  exact continuous_eval.comp continuous_swap

end ContinuousMap
