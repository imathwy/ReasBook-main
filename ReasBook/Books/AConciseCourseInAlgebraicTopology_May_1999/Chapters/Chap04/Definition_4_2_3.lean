import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_2

open scoped unitInterval

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall via `lean_leansearch`: mathlib has reduced/path APIs for other graph-path
-- formalisms, but here the source notion is the direct "no immediate backtracking" predicate on
-- consecutive `OrientedEdge`s in an `EdgePath`.

namespace EdgePath

/-- Definition 4.2.3. An edge path is reduced when no consecutive pair of oriented edges is
related by reversal, so the path never traverses an edge and then immediately traverses the same
edge with the opposite orientation. -/
def Reduced {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) : Prop :=
  ∀ m : Fin p.length, p m.succ ≠ (p (Fin.castSucc m)).reverse

/-- A reduced edge path cannot immediately retrace any consecutive oriented edge. -/
theorem Reduced.not_reverse {boundary : J ↪ Fin 2 → X₀} {p : EdgePath boundary}
    (hp : p.Reduced) (m : Fin p.length) :
    p m.succ ≠ (p (Fin.castSucc m)).reverse :=
  hp m

/-- A reduced edge path has no immediate backtracking across any consecutive pair of edges. -/
theorem reduced_iff {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    p.Reduced ↔ ∀ m : Fin p.length, p m.succ ≠ (p (Fin.castSucc m)).reverse :=
  Iff.rfl

end EdgePath
