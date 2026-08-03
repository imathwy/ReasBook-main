module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.Topology.Compactness.Paracompact
import Topology_Munkres_2000.Book.Exercise_8_99_1.LocalTopology
import Topology_Munkres_2000.Book.Remark_6_0_4

public section

universe u

namespace ChartedSpace

/-- Exercise 8.99.8: A locally `m`-Euclidean space is metrizable if and only if it is
paracompact and Hausdorff. -/
theorem metrizableSpace_iff_paracompact_t2 (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] :
    TopologicalSpace.MetrizableSpace X ↔ ParacompactSpace X ∧ T2Space X := by
  rw [TopologicalSpace.metrizableSpace_iff_paracompact_t2_locallyMetrizable]
  constructor
  · exact fun h ↦ ⟨h.1, h.2.1⟩
  · exact fun h ↦ ⟨h.1, h.2, inferInstance⟩

end ChartedSpace
