module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold

public section

universe u

/-- A compact Hausdorff space with Euclidean `m`-dimensional charts is a
topological `m`-manifold. -/
instance instTopologicalManifoldOfCompact (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [T2Space X] [CompactSpace X] :
    TopologicalManifold m X where
  toT2Space := inferInstance
  toSecondCountableTopology :=
    ChartedSpace.secondCountable_of_sigmaCompact (EuclideanSpace ℝ (Fin m)) X
