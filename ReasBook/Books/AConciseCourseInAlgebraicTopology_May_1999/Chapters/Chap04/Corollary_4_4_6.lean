import Mathlib.Data.Finite.Card
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_4
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Theorem_4_4_5

-- `ConnectedCoveringSpace (graphRealization boundary)` is the chapter-local owner for connected
-- graph coverings, and Chapter 3 already provides the canonical fiber-cardinality invariance API
-- for path-connected covering maps.

universe u v

variable {B₀ : Type u} {J : Type v}

open scoped Cardinal

namespace ConnectedCoveringSpace

/-- For a connected covering of a connected graph realization, all fibers of `X.obj.hom` have the
same cardinality. This is the graph-realization specialization of the Chapter 3 theorem
`IsPathConnectedCoveringMap.fiber_cardinal_eq`. -/
theorem fiber_cardinal_eq
    (boundary : J ↪ Fin 2 → B₀) [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary))
    (x y : graphRealization boundary) :
    #(X.obj.hom ⁻¹' ({x} : Set (graphRealization boundary))) =
      #(X.obj.hom ⁻¹' ({y} : Set (graphRealization boundary))) := by
  sorry

/-- Corollary 4.4.6 (1): if the base realization `graphRealization boundary` is a finite graph and
one fiber of `X.obj.hom` has cardinality `n`, then connectedness forces every fiber to have that
same cardinality, so the total space `X.obj.left` admits a realizing lifted boundary `boundaryE`
whose graph is finite. -/
theorem finite_coverGraph_of_fiberCard
    (boundary : J ↪ Fin 2 → B₀) [FiniteGraph boundary]
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) (n : ℕ)
    (x : graphRealization boundary)
    (hfinite : Finite (X.obj.hom ⁻¹' ({x} : Set (graphRealization boundary))))
    (hcard : Nat.card (X.obj.hom ⁻¹' ({x} : Set (graphRealization boundary))) = n) :
    ∃ boundaryE :
        coverGraphEdgeIndex boundary X.obj.hom ↪ Fin 2 → coverGraphVertexSet boundary X.obj.hom,
      FiniteGraph boundaryE ∧
        ∃ hE : graphRealization boundaryE ≃ₜ X.obj.left,
          IsCoverGraphRealization boundary X.obj.hom boundaryE hE := sorry

/-- Corollary 4.4.6 (2): if the base realization `graphRealization boundary` is a finite graph and
one fiber of `X.obj.hom` has cardinality `n`, then connectedness forces every fiber to have that
same cardinality, so some finite graph
realization of `X.obj.left` over `boundary` has Euler characteristic `n χ(B)` in explicit
vertex-edge counting form. -/
theorem eulerFormula_of_fiberCard
    (boundary : J ↪ Fin 2 → B₀) [FiniteGraph boundary]
    [ConnectedSpace (graphRealization boundary)]
    (X : ConnectedCoveringSpace (graphRealization boundary)) (n : ℕ)
    (x : graphRealization boundary)
    (hfinite : Finite (X.obj.hom ⁻¹' ({x} : Set (graphRealization boundary))))
    (hcard : Nat.card (X.obj.hom ⁻¹' ({x} : Set (graphRealization boundary))) = n) :
    ∃ boundaryE :
        coverGraphEdgeIndex boundary X.obj.hom ↪ Fin 2 → coverGraphVertexSet boundary X.obj.hom,
      FiniteGraph boundaryE ∧
        ∃ hE : graphRealization boundaryE ≃ₜ X.obj.left,
          IsCoverGraphRealization boundary X.obj.hom boundaryE hE ∧
            (Nat.card (coverGraphVertexSet boundary X.obj.hom) : Int) -
                Nat.card (coverGraphEdgeIndex boundary X.obj.hom) =
              (n : Int) * ((Nat.card B₀ : Int) - Nat.card J) := sorry

end ConnectedCoveringSpace
