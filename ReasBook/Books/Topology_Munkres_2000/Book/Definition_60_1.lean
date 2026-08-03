module

public import Topology_Munkres_2000.Book.Definition_36_2

public section

universe u

/- Definition 60.1 (recall): A surface is the `2`-manifold of Definition 36.2:
a Hausdorff second-countable space locally homeomorphic to
`EuclideanSpace ℝ (Fin 2)`. Mathlib's `ChartedSpace` contains the covering
atlas of local homeomorphisms required by this definition. -/
#check fun (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [T2Space X]
    [SecondCountableTopology X] ↦ X
