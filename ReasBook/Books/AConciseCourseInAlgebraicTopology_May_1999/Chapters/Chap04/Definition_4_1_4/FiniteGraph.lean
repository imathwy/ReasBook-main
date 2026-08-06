import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

/-- Helper for Definition 4.1.4: the source-faithful quotient topology on
`graphRealization boundary`, induced from the chapter's discrete source topologies on `X₀` and
`J` together with the usual topology on `I`. -/
abbrev graphRealizationSourceFaithfulTopologicalSpace (boundary : J ↪ Fin 2 → X₀) :
    TopologicalSpace (graphRealization boundary) :=
  graphRealizationTopologicalSpace boundary

/-- A graph realization is finite when its vertex type `X₀` and edge index type `J` are both
finite. -/
class FiniteGraph (boundary : J ↪ Fin 2 → X₀) : Prop where
  finiteVertices : Finite X₀
  finiteEdges : Finite J

attribute [instance] FiniteGraph.finiteVertices FiniteGraph.finiteEdges

/-- A graph realization is finite whenever its vertex and edge types are finite. -/
instance instFiniteGraphOfFinite (boundary : J ↪ Fin 2 → X₀) [Finite X₀] [Finite J] :
    FiniteGraph boundary := by
  exact ⟨inferInstance, inferInstance⟩

attribute [instance 100] instFiniteGraphOfFinite

/-- A graph realization is finite exactly when its vertex type and edge index type are finite. -/
theorem finiteGraph_iff (boundary : J ↪ Fin 2 → X₀) :
    FiniteGraph boundary ↔ Finite X₀ ∧ Finite J := by
  constructor
  · intro h
    exact ⟨h.finiteVertices, h.finiteEdges⟩
  · rintro ⟨hX₀, hJ⟩
    let _ : Finite X₀ := hX₀
    let _ : Finite J := hJ
    exact instFiniteGraphOfFinite boundary
