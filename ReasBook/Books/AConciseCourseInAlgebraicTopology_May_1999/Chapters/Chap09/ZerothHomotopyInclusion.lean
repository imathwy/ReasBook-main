import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap09.Definition_9_1_5

open scoped Topology

universe u

variable {X : Type u} [TopologicalSpace X]

/-- The map `π₀(A) → π₀(X)` induced by the inclusion `A ↪ X`. -/
def zerothHomotopyInclusion (A : Set X) : ZerothHomotopy A → ZerothHomotopy X :=
  Quotient.map Subtype.val fun _ _ h ↦ ⟨h.somePath.map continuous_subtype_val⟩

/-- Evaluating `zerothHomotopyInclusion A` on the path component of `a : A` gives the ambient path
component of the same point in `X`. -/
@[simp] theorem zerothHomotopyInclusion_mk (A : Set X) (a : A) :
    zerothHomotopyInclusion A ⟦a⟧ = ⟦a.1⟧ :=
  rfl
