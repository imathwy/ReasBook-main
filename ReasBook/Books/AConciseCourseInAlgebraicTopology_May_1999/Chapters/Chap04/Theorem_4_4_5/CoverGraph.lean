import Mathlib.Topology.Covering.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2

open scoped unitInterval

universe u v w

variable {B₀ : Type u} {J : Type v} {E : Type w}

/-- The vertices of the lifted graph over a covering map `p : E → graphRealization boundary` are
the points of `E` lying over vertices of the base graph. -/
def coverGraphVertexSet (boundary : J ↪ Fin 2 → B₀) (p : E → graphRealization boundary) : Type w :=
  {e : E // p e ∈ Set.range (graphVertex boundary)}

/-- A lifted edge is indexed by a base edge `j : J` together with a chosen lift-starting point in
the fiber over the initial vertex `graphVertex boundary (boundary j 0)`. -/
def coverGraphEdgeIndex (boundary : J ↪ Fin 2 → B₀) (p : E → graphRealization boundary) :
    Type (max v w) :=
  Σ j : J, p ⁻¹' ({graphVertex boundary (boundary j 0)} : Set (graphRealization boundary))

/-- A vertex of the lifted graph lies over a specific vertex of the base graph. -/
theorem coverGraphVertexSet_exists_vertex (boundary : J ↪ Fin 2 → B₀)
    (p : E → graphRealization boundary) (x : coverGraphVertexSet boundary p) :
    ∃ b : B₀, p x.1 = graphVertex boundary b := by
  rcases x.2 with ⟨b, hb⟩
  exact ⟨b, hb.symm⟩

/-- The chosen point underlying a lifted edge index lies over the initial vertex of its base edge.
-/
@[simp] theorem coverGraphEdgeIndex_proj_eq_graphVertex (boundary : J ↪ Fin 2 → B₀)
    (p : E → graphRealization boundary) (e : coverGraphEdgeIndex boundary p) :
    p e.2.1 = graphVertex boundary (boundary e.1 0) := by
  have hmem :
      p e.2.1 ∈ ({graphVertex boundary (boundary e.1 0)} : Set (graphRealization boundary)) :=
    e.2.2
  exact Set.mem_singleton_iff.mp hmem

/-- The initial vertex of a lifted edge index is the corresponding element of
`coverGraphVertexSet boundary p`. -/
def coverGraphEdgeInitialVertex (boundary : J ↪ Fin 2 → B₀) (p : E → graphRealization boundary)
    (e : coverGraphEdgeIndex boundary p) : coverGraphVertexSet boundary p :=
  ⟨e.2.1, ⟨boundary e.1 0, (coverGraphEdgeIndex_proj_eq_graphVertex boundary p e).symm⟩⟩

@[simp] theorem coverGraphEdgeInitialVertex_val (boundary : J ↪ Fin 2 → B₀)
    (p : E → graphRealization boundary) (e : coverGraphEdgeIndex boundary p) :
    (coverGraphEdgeInitialVertex boundary p e).1 = e.2.1 :=
  rfl

@[simp] theorem coverGraphEdgeInitialVertex_proj_eq_graphVertex (boundary : J ↪ Fin 2 → B₀)
    (p : E → graphRealization boundary) (e : coverGraphEdgeIndex boundary p) :
    p (coverGraphEdgeInitialVertex boundary p e).1 = graphVertex boundary (boundary e.1 0) :=
  coverGraphEdgeIndex_proj_eq_graphVertex boundary p e

variable [TopologicalSpace E]

/-- `boundaryE` together with `hE` realizes the total space `E` as the graph obtained by lifting
each base edge from its chosen initial point. The homeomorphism sends lifted vertices to their
underlying points of `E`, fixes the chosen initial vertex of each lifted edge, and projects each
lifted edge to the corresponding base edge pointwise. -/
def IsCoverGraphRealization (boundary : J ↪ Fin 2 → B₀) (p : E → graphRealization boundary)
    (boundaryE : coverGraphEdgeIndex boundary p ↪ Fin 2 → coverGraphVertexSet boundary p)
    [TopologicalSpace (graphRealization boundaryE)]
    (hE : graphRealization boundaryE ≃ₜ E) : Prop :=
  (∀ x : coverGraphVertexSet boundary p, hE (graphVertex boundaryE x) = x.1) ∧
    (∀ e : coverGraphEdgeIndex boundary p,
      boundaryE e 0 = coverGraphEdgeInitialVertex boundary p e) ∧
    ∀ (e : coverGraphEdgeIndex boundary p) (t : I),
      p (hE (graphEdgePoint boundaryE e t)) = graphEdgePoint boundary e.1 t

namespace IsCoverGraphRealization

/-- Under a lifted graph realization, each graph vertex maps to its underlying point in `E`. -/
theorem vertex_eq {boundary : J ↪ Fin 2 → B₀} {p : E → graphRealization boundary}
    {boundaryE : coverGraphEdgeIndex boundary p ↪ Fin 2 → coverGraphVertexSet boundary p}
    [TopologicalSpace (graphRealization boundaryE)]
    {hE : graphRealization boundaryE ≃ₜ E}
    (h : IsCoverGraphRealization boundary p boundaryE hE) (x : coverGraphVertexSet boundary p) :
    hE (graphVertex boundaryE x) = x.1 :=
  h.1 x

/-- Under a lifted graph realization, the chosen starting point of each lifted edge is its initial
vertex. -/
theorem initial_eq {boundary : J ↪ Fin 2 → B₀} {p : E → graphRealization boundary}
    {boundaryE : coverGraphEdgeIndex boundary p ↪ Fin 2 → coverGraphVertexSet boundary p}
    [TopologicalSpace (graphRealization boundaryE)]
    {hE : graphRealization boundaryE ≃ₜ E}
    (h : IsCoverGraphRealization boundary p boundaryE hE) (e : coverGraphEdgeIndex boundary p) :
    boundaryE e 0 = coverGraphEdgeInitialVertex boundary p e :=
  h.2.1 e

/-- Under a lifted graph realization, each lifted edge projects pointwise to its base edge. -/
theorem edgePoint_eq {boundary : J ↪ Fin 2 → B₀} {p : E → graphRealization boundary}
    {boundaryE : coverGraphEdgeIndex boundary p ↪ Fin 2 → coverGraphVertexSet boundary p}
    [TopologicalSpace (graphRealization boundaryE)]
    {hE : graphRealization boundaryE ≃ₜ E}
    (h : IsCoverGraphRealization boundary p boundaryE hE) (e : coverGraphEdgeIndex boundary p)
    (t : I) :
    p (hE (graphEdgePoint boundaryE e t)) = graphEdgePoint boundary e.1 t :=
  h.2.2 e t

end IsCoverGraphRealization
