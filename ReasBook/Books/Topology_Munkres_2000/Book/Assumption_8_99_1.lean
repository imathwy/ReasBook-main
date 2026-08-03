module

public import Topology_Munkres_2000.Book.Definition_8_99_1

public section

universe u

/- Assumption 8.99.1: Throughout these exercises, let `X` be a space that is locally
`m`-Euclidean. -/
#check fun (m : ℕ) (X : Type u) [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin m)) X] ↦ X
