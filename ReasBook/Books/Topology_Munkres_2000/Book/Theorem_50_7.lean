module

public import Topology_Munkres_2000.Book.Definition_36_1.TopologicalManifold
public import Topology_Munkres_2000.Book.Remark_50_2

public section

open scoped CoveringDimension

universe u

/-- Theorem 50.7. Every nonempty `2`-manifold has covering dimension `2`.
The source assumes compactness, but `manifold_coveringDimension_eq` shows that it is unnecessary. -/
theorem surface_coveringDimension_eq {M : Type u}
    [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [TopologicalManifold 2 M] [Nonempty M] :
    dim M = (2 : ℕ∞) := manifold_coveringDimension_eq
