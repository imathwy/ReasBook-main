import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_4

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall via `lean_leansearch`: mathlib's nearby owner is `SimpleGraph.IsTree`, but in
-- this chapter a tree is a property of the topological graph realization `graphRealization
-- boundary`, expressed in terms of `EdgePath`.

/-- Definition 4.2.5. A tree is a connected graph realization with no closed reduced edge paths.

Equivalently, every closed `EdgePath boundary` fails to be reduced. -/
class IsTree (boundary : J ↪ Fin 2 → X₀) : Prop
    extends ConnectedSpace (graphRealization boundary) where
  not_reduced_of_isClosed : ∀ p : EdgePath boundary, p.IsClosed → ¬ p.Reduced

/-- A graph realization is a tree exactly when it is connected and every closed edge path fails
to be reduced. -/
theorem isTree_iff (boundary : J ↪ Fin 2 → X₀) :
    IsTree boundary ↔
      ConnectedSpace (graphRealization boundary) ∧
        ∀ p : EdgePath boundary, p.IsClosed → ¬ p.Reduced := by
  constructor
  · intro h
    exact ⟨h.toConnectedSpace, h.not_reduced_of_isClosed⟩
  · rintro ⟨hConnected, hNoClosedReduced⟩
    exact
      { toConnectedSpace := hConnected
        not_reduced_of_isClosed := hNoClosedReduced }
