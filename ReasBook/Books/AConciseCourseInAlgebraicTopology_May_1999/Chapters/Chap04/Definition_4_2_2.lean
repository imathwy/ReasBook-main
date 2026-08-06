import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_1

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall: `Quiver.Path` and `SimpleGraph.Walk` encode combinatorial paths in mathlib,
-- but this item packages a finite composite of already-parametrized oriented edges in
-- `graphRealization boundary`.

/-- Definition 4.2.2. An edge path in `graphRealization boundary` is a finite composite
`k₀, …, kₙ` of oriented edges such that each consecutive pair is composable:
`(toEdge m.succ).initialVertex = (toEdge (Fin.castSucc m)).terminalVertex`.

The field `length` records the number `n` of compositions, so `toEdge` is indexed by
`Fin (length + 1)`. -/
structure EdgePath (boundary : J ↪ Fin 2 → X₀) where
  length : Nat
  toEdge : Fin (length + 1) → OrientedEdge boundary
  composable :
    ∀ m : Fin length,
      (toEdge m.succ).initialVertex = (toEdge (Fin.castSucc m)).terminalVertex

namespace EdgePath

/-- An edge path can be evaluated at an index to recover its corresponding oriented edge. -/
instance {boundary : J ↪ Fin 2 → X₀} : CoeFun (EdgePath boundary) fun p ↦
    Fin (p.length + 1) → OrientedEdge boundary where
  coe := EdgePath.toEdge

/-- The initial vertex of an edge path, viewed in `graphRealization boundary`. -/
def initialVertex {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    graphRealization boundary :=
  (p 0).initialVertex

/-- The terminal vertex of an edge path, viewed in `graphRealization boundary`. -/
def terminalVertex {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    graphRealization boundary :=
  (p (Fin.last p.length)).terminalVertex

@[simp] theorem initialVertex_apply_zero {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    p.initialVertex = (p 0).initialVertex :=
  rfl

@[simp] theorem terminalVertex_apply_last {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    p.terminalVertex = (p (Fin.last p.length)).terminalVertex :=
  rfl

/-- Consecutive oriented edges in an edge path meet at their shared endpoint. -/
@[simp] theorem composable_apply {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary)
    (m : Fin p.length) :
    (p m.succ).initialVertex = (p (Fin.castSucc m)).terminalVertex :=
  p.composable m

end EdgePath
