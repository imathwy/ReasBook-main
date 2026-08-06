import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap04.Definition_4_2_2

universe u v

variable {X₀ : Type u} {J : Type v}

-- Semantic recall via `lean_leansearch`: mathlib graph-path APIs package loops in other path
-- owners, but here the source notion is the direct endpoint-equality predicate on `EdgePath`.

namespace EdgePath

/-- Definition 4.2.4. An edge path is closed when it starts and ends at the same vertex, so it
is a loop. -/
def IsClosed {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) : Prop :=
  p.initialVertex = p.terminalVertex

/-- A closed edge path is exactly one whose initial and terminal vertices agree. -/
@[simp] theorem isClosed_iff {boundary : J ↪ Fin 2 → X₀} (p : EdgePath boundary) :
    p.IsClosed ↔ p.initialVertex = p.terminalVertex :=
  Iff.rfl

end EdgePath
