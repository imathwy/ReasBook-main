module

public import Topology_Munkres_2000.Book.Exercise_36_3.Instances

public section

universe u

/- Exercise 36.3: Compactness supplies second countability for a Hausdorff space
with Euclidean `m`-dimensional charts, completing the conditions of Definition 36.1. -/
#check fun (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] [T2Space X]
    [CompactSpace X] ↦ (inferInstance : TopologicalManifold m X)
