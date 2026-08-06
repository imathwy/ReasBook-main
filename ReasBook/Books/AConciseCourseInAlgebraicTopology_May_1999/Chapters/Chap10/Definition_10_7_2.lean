import Mathlib.Topology.Basic
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap10.Definition_10_7_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Set

-- Semantic recall: `lean_leansearch` found only general interior lemmas, not a canonical
-- mathlib notion of an excisive triad, so the source is formalized as a predicate on `Triad`.

namespace Triad

variable {X : Type u} [TopologicalSpace X]

/-- Definition 10.7.2: a triad `(X; A, B)` is excisive when `X` is the union of the interiors
of `A` and `B`, equivalently when `interior A ∪ interior B = X`. -/
def IsExcisive (T : Triad X) : Prop :=
  interior T.subspaceA ∪ interior T.subspaceB = (univ : Set X)

/-- A triad is excisive exactly when the interiors of its distinguished subspaces cover the
ambient space. -/
@[simp] theorem isExcisive_iff {T : Triad X} :
    T.IsExcisive ↔ interior T.subspaceA ∪ interior T.subspaceB = (univ : Set X) :=
  Iff.rfl

/-- The excisive condition can be used pointwise: every point of `X` lies in `interior A` or in
`interior B`. -/
theorem isExcisive_iff_forall {T : Triad X} :
    T.IsExcisive ↔ ∀ x : X, x ∈ interior T.subspaceA ∨ x ∈ interior T.subspaceB := by
  rw [isExcisive_iff, Set.eq_univ_iff_forall]
  simp

end Triad
