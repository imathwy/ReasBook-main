module

public import Topology_Munkres_2000.Book.Theorem_50_3

public section

universe u

/- Example 50.5. Every compact `2`-manifold has covering dimension at most `2`. -/
#check (compactManifold_coveringDimension_le :
  ∀ {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) X] [TopologicalManifold 2 X]
    [CompactSpace X], HasCoveringDimensionLE X 2)
