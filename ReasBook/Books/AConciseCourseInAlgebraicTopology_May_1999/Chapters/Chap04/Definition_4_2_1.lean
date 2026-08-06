import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_1_2

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `Quiver.reverse` and `SimpleGraph.Dart` are nearby combinatorial orientation
-- APIs, but this chapter needs the interval traversal of a chosen edge in a realized graph.

/-- The two possible interval orientations of an edge in a graph realization. -/
inductive EdgeOrientation
  | forward
  | backward
deriving DecidableEq

namespace EdgeOrientation

/-- Reversing an interval orientation swaps the forward and reverse parametrizations. -/
def reverse : EdgeOrientation → EdgeOrientation
  | .forward => .backward
  | .backward => .forward

@[simp] theorem reverse_reverse (orientation : EdgeOrientation) :
    orientation.reverse.reverse = orientation := by
  cases orientation <;> rfl

/-- The interval reparametrization attached to an edge orientation. -/
def toMap : EdgeOrientation → I → I
  | .forward => id
  | .backward => σ

@[simp] theorem toMap_forward : EdgeOrientation.toMap .forward = id := rfl

@[simp] theorem toMap_backward : EdgeOrientation.toMap .backward = σ := rfl

@[simp] theorem reverse_apply (orientation : EdgeOrientation) (t : I) :
    orientation.reverse.toMap t = orientation.toMap (σ t) := by
  cases orientation with
  | forward => rfl
  | backward =>
      simpa [EdgeOrientation.reverse, EdgeOrientation.toMap] using unitInterval.symm_symm t

end EdgeOrientation

/-- Definition 4.2.1. An oriented edge in `graphRealization boundary` is a chosen edge of the
realization together with one of its two interval orientations, viewed through the induced
traversal `I → graphRealization boundary`. -/
structure OrientedEdge (boundary : J ↪ Fin 2 → X₀) where
  edge : J
  orientation : EdgeOrientation

namespace OrientedEdge

/-- Reversing an oriented edge toggles its interval orientation on the same underlying edge. -/
def reverse {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) : OrientedEdge boundary where
  edge := k.edge
  orientation := k.orientation.reverse

@[simp] theorem reverse_edge {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.reverse.edge = k.edge := rfl

@[simp] theorem reverse_orientation {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.reverse.orientation = k.orientation.reverse := rfl

@[simp] theorem reverse_reverse {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.reverse.reverse = k := by
  cases k with
  | mk edge orientation =>
      cases orientation <;> rfl

/-- The interval traversal map associated to an oriented edge. -/
def toMap {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    I → graphRealization boundary :=
  fun t ↦ graphEdgePoint boundary k.edge (k.orientation.toMap t)

/-- The initial vertex of an oriented edge in `graphRealization boundary`. -/
def initialVertex {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    graphRealization boundary :=
  k.toMap 0

/-- The terminal vertex of an oriented edge in `graphRealization boundary`. -/
def terminalVertex {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    graphRealization boundary :=
  k.toMap 1

@[simp] theorem toMap_forward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    ((⟨j, .forward⟩ : OrientedEdge boundary)).toMap = graphEdgePoint boundary j := rfl

@[simp] theorem toMap_backward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    ((⟨j, .backward⟩ : OrientedEdge boundary)).toMap =
      fun t ↦ graphEdgePoint boundary j (σ t) := rfl

@[simp] theorem initialVertex_forward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    (⟨j, .forward⟩ : OrientedEdge boundary).initialVertex =
      graphVertex boundary (boundary j 0) := by
  change graphEdgePoint boundary j 0 = graphVertex boundary (boundary j 0)
  exact (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

@[simp] theorem terminalVertex_forward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    (⟨j, .forward⟩ : OrientedEdge boundary).terminalVertex =
      graphVertex boundary (boundary j 1) := by
  change graphEdgePoint boundary j 1 = graphVertex boundary (boundary j 1)
  exact (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm

@[simp] theorem initialVertex_backward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    (⟨j, .backward⟩ : OrientedEdge boundary).initialVertex =
      graphVertex boundary (boundary j 1) := by
  change graphEdgePoint boundary j (σ 0) = graphVertex boundary (boundary j 1)
  simpa using (graphVertex_boundary_one_eq_graphEdgePoint_one boundary j).symm

@[simp] theorem terminalVertex_backward {boundary : J ↪ Fin 2 → X₀} (j : J) :
    (⟨j, .backward⟩ : OrientedEdge boundary).terminalVertex =
      graphVertex boundary (boundary j 0) := by
  change graphEdgePoint boundary j (σ 1) = graphVertex boundary (boundary j 0)
  simpa using (graphVertex_boundary_zero_eq_graphEdgePoint_zero boundary j).symm

/-- The traversal map of an oriented edge is the forward or backward parametrization of its chosen
edge. -/
theorem toMap_eq_edgePoint_or_reverse {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.toMap = graphEdgePoint boundary k.edge ∨
      k.toMap = fun t ↦ graphEdgePoint boundary k.edge (σ t) := by
  cases k with
  | mk edge orientation =>
      cases orientation with
      | forward => exact Or.inl rfl
      | backward => exact Or.inr rfl

/-- The reversed oriented edge is given pointwise by precomposition with `t ↦ 1 - t`. -/
theorem reverse_apply {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) (t : I) :
    k.reverse.toMap t = k.toMap (σ t) := by
  exact congrArg (graphEdgePoint boundary k.edge) (EdgeOrientation.reverse_apply k.orientation t)

@[simp] theorem reverse_initialVertex {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.reverse.initialVertex = k.terminalVertex := by
  change k.reverse.toMap 0 = k.toMap 1
  simpa using k.reverse_apply 0

@[simp] theorem reverse_terminalVertex {boundary : J ↪ Fin 2 → X₀} (k : OrientedEdge boundary) :
    k.reverse.terminalVertex = k.initialVertex := by
  change k.reverse.toMap 1 = k.toMap 0
  simpa using k.reverse_apply 1

end OrientedEdge
