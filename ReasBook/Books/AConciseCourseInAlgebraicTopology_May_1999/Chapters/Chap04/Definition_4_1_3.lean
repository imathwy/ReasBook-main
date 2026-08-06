import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `Set.range` is Lean's canonical set owner for the image of the interval
-- parametrization `graphEdgePoint boundary j : I → graphRealization boundary`.

/-- Definition 4.1.3. The edge associated to `j : J` is the image of the interval `I` under the
parametrization `graphEdgePoint boundary j : I → graphRealization boundary`. -/
def graphEdge (boundary : J ↪ Fin 2 → X₀) (j : J) : Set (graphRealization boundary) :=
  Set.range (graphEdgePoint boundary j)

/-- A point lies on `graphEdge boundary j` exactly when it is the image of some `t : I` under the
edge parametrization `graphEdgePoint boundary j`. -/
@[simp]
theorem mem_graphEdge_iff (boundary : J ↪ Fin 2 → X₀) (j : J) (x : graphRealization boundary) :
    x ∈ graphEdge boundary j ↔ ∃ t : I, graphEdgePoint boundary j t = x :=
  Iff.rfl

/-- Every point of the interval parametrization of the edge indexed by `j` lies on
`graphEdge boundary j`. -/
theorem graphEdgePoint_mem_graphEdge (boundary : J ↪ Fin 2 → X₀) (j : J) (t : I) :
    graphEdgePoint boundary j t ∈ graphEdge boundary j :=
  (mem_graphEdge_iff boundary j (graphEdgePoint boundary j t)).2 ⟨t, rfl⟩
