module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold

public section

universe u

/- Definition 36.1: An `m`-manifold is a Hausdorff second-countable space locally
homeomorphic to `EuclideanSpace ℝ (Fin m)`. -/
#check fun (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [TopologicalManifold m X] ↦ X
