module

import Topology_Munkres_2000.Book.Exercise_8_99_5

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Exercise_8_99_9.ChartedSpace

public section

universe u

namespace ConnectedComponent

/-- Exercise 8.99.9: A connected component of a metrizable locally `m`-Euclidean space is
second countable. -/
theorem secondCountableTopology (m : ℕ) {X : Type u}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin m)) X]
    [TopologicalSpace.MetrizableSpace X] (x : X) :
    SecondCountableTopology (connectedComponent x) := by
  -- Regard the connected component as a connected, locally compact charted space.
  letI : ConnectedSpace (connectedComponent x) :=
    Subtype.connectedSpace isConnected_connectedComponent
  letI : LocallyCompactSpace (connectedComponent x) :=
    ChartedSpace.locallyCompactSpace (EuclideanSpace ℝ (Fin m)) (connectedComponent x)
  -- The chart sources form the required pointwise open cover.
  refine secondCountable_of_connected_metrizable_open_cover
    (fun y ↦ (chartAt (EuclideanSpace ℝ (Fin m)) y).source) ?_ ?_ ?_ ?_
  · intro y
    exact (chartAt (EuclideanSpace ℝ (Fin m)) y).open_source
  · intro y
    exact mem_chart_source (EuclideanSpace ℝ (Fin m)) y
  · intro y
    exact (chartAt (EuclideanSpace ℝ (Fin m)) y).secondCountableTopology_source
  · intro y
    exact (chartAt (EuclideanSpace ℝ (Fin m)) y).open_source.locallyCompactSpace

/-- Helper for Exercise 8.99.9: the connected component carries the resulting
`m`-manifold structure. -/
instance instTopologicalManifold (m : ℕ) {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [TopologicalSpace.MetrizableSpace X] (x : X) :
    TopologicalManifold m (connectedComponent x) where
  t2 := T2Space.t2
  is_open_generated_countable := (secondCountableTopology m x).is_open_generated_countable

end ConnectedComponent
