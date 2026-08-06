import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap05.Construction_5_1_14

open TopologicalSpace
open scoped Topology

universe u v

-- `continuous_from_compactlyGenerated` is the canonical mathlib bridge from the k-ification
-- topology `TopologicalSpace.compactlyGenerated X` to the original topology on `X`.

section

variable {X : Type u} [t : TopologicalSpace X]

/-- Lemma 5.1.15: the identity function `kX → X` is continuous, where `kX` is
`TopologicalSpace.compactlyGenerated.{v} X`. -/
theorem continuous_id_compactlyGenerated
    : Continuous[compactlyGenerated.{v} X, t] (id : X → X) := by
  refine continuous_from_compactlyGenerated (id : X → X) ?_
  intro S g
  simpa using g.continuous

end
