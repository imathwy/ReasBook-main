import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4.FiniteGraph
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_5

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

/-- Helper for Lemma 4.2.7: the source disjoint union carries the chapter's intended discrete
topologies on `X₀` and `J` together with the usual topology on `I`. -/
abbrev graphRealizationSourceFaithfulSourceTopology :
    TopologicalSpace (X₀ ⊕ (J × I)) :=
  let _ : TopologicalSpace X₀ := ⊥
  let _ : TopologicalSpace J := ⊥
  inferInstance

/-- Helper for Lemma 4.2.7: a source-faithful tree is a graph realization that is connected for
the source-faithful quotient topology and has no closed reduced edge paths. -/
class SourceFaithfulIsTree (boundary : J ↪ Fin 2 → X₀) : Prop where
  toConnectedSpace :
    @ConnectedSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary)
  not_reduced_of_isClosed : ∀ p : EdgePath boundary, p.IsClosed → ¬ p.Reduced

/-- Compatibility bridge for the former auxiliary tree API.  The central graph-realization
topology is now the source-faithful quotient topology itself, so the chapter's `IsTree` assumption
supplies exactly the two fields required here. -/
instance instSourceFaithfulIsTreeOfIsTree
    (boundary : J ↪ Fin 2 → X₀) [h : IsTree boundary] :
    SourceFaithfulIsTree boundary where
  toConnectedSpace := by
    simpa only [graphRealizationSourceFaithfulTopologicalSpace] using h.toConnectedSpace
  not_reduced_of_isClosed := h.not_reduced_of_isClosed

instance instConnectedSpaceGraphRealizationSourceFaithful
    (boundary : J ↪ Fin 2 → X₀) [h : SourceFaithfulIsTree boundary] :
    @ConnectedSpace (graphRealization boundary)
      (graphRealizationSourceFaithfulTopologicalSpace boundary) :=
  h.toConnectedSpace

/-- A graph realization is a source-faithful tree exactly when it is connected for the
source-faithful realization topology and every closed edge path fails to be reduced. -/
theorem sourceFaithfulIsTree_iff (boundary : J ↪ Fin 2 → X₀) :
    SourceFaithfulIsTree boundary ↔
      (@ConnectedSpace (graphRealization boundary)
        (graphRealizationSourceFaithfulTopologicalSpace boundary)) ∧
        ∀ p : EdgePath boundary, p.IsClosed → ¬ p.Reduced := by
  constructor
  · intro h
    exact ⟨h.toConnectedSpace, h.not_reduced_of_isClosed⟩
  · rintro ⟨hConnected, hNoClosedReduced⟩
    exact
      { toConnectedSpace := hConnected
        not_reduced_of_isClosed := hNoClosedReduced }
